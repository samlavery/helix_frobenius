"""
Harmonic-chart wall-fraction bench.

Question (Sam, 2026-08-11): move the analysis to the HARMONIC chart (pi/3, pi/6)
and re-ask what fraction of zeta zeros sit at that chart's wall.

STEP 0 settled the definitional half: the "midpoint line" reading is a relabeling
(UnitMidpoint.criticality_is_half_unit is an iff), and the repo's actual wall
(eventArcs) is a condition on integer CELL COUNTS k, not on zeros.  The one
reading with content replaces the integer k by the zero ordinate gamma:

    wall(H)  <=>  gamma * H  ==  pi   (mod 2 pi)

which is a condition on Im rho, orthogonal to Re rho = 1/2.  Exactly zero zeros
satisfy it exactly, so what is measurable is the DISTRIBUTION of the cell phase
gamma*H mod 2pi.

THE DC IS COMPUTABLE EXACTLY, so we compute it before estimating anything.
The j-th harmonic of the cell phase,

    c_j(H) = (1/N) sum_n exp(i j gamma_n H),

is a Landau explicit-formula sum at x = e^{jH}:

    sum_{0<gamma<=T} x^{i gamma} = -(T/2pi) Lambda(x)/sqrt(x) + O(log T),   x>1 fixed.

Normalising by N(T) ~ (T/2pi)(log(T/2pi) - 1) gives the exact prediction

    c_j(H)  ~  - Lambda(e^{jH}) / ( sqrt(e^{jH}) * (log(T/2pi) - 1) ).

Lambda vanishes unless e^{jH} is a prime power.  So the harmonic scales are
predicted NULL at every harmonic, and the prime clocks H = log p^k are predicted
to ring.  H = log 2 is the positive control.

Run:  python3 harmonic_chart_bench.py
"""

import numpy as np

TWOPI = 2.0 * np.pi
CACHE = "/Users/samuellavery/work/helix_frobenius/tmp/zeta_zeros_cache.txt"


# ------------------------------------------------------------------ data

def load_zeros(path=CACHE):
    return np.loadtxt(path, dtype=np.float64)


def rvm(t):
    """Riemann-von Mangoldt smooth count N(t) = (t/2pi)(log(t/2pi) - 1) + 7/8."""
    return (t / TWOPI) * (np.log(t / TWOPI) - 1.0) + 0.875


# ------------------------------------------------------------------ the exact DC

def von_mangoldt_at(x, tol=1e-9):
    """Lambda(x) for real x: log p if x is (numerically) a prime power p^k, else 0."""
    if x <= 1.0:
        return 0.0
    for p in _PRIMES:
        if p > x + 1.0:
            break
        k = np.log(x) / np.log(p)
        kr = round(k)
        if kr >= 1 and abs(k - kr) < tol and abs(p ** kr - x) < tol * max(1.0, x):
            return np.log(p)
    return 0.0


def _sieve(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]


_PRIMES = _sieve(2_000_000)


def landau_dc(H, j, T):
    """Exact predicted c_j(H): -Lambda(x)/(sqrt(x) * (log(T/2pi) - 1)), x = e^{jH}."""
    x = np.exp(j * H)
    lam = von_mangoldt_at(x)
    if lam == 0.0:
        return 0.0
    return -lam / (np.sqrt(x) * (np.log(T / TWOPI) - 1.0))


# ------------------------------------------------------------------ statistics

def harmonics(gam, H, jmax=12):
    """c_j = (1/N) sum exp(i j gamma H) for j = 1..jmax."""
    N = gam.size
    out = np.empty(jmax, dtype=np.complex128)
    for j in range(1, jmax + 1):
        out[j - 1] = np.exp(1j * j * H * gam).sum() / N
    return out


def cell_counts(gam, H, m):
    """Occupancy of m cells of the phase gamma*H mod 2pi, bins CENTERED on
    multiples of 2pi/m so that the wall phase pi sits at the centre of a bin
    (bin index m/2).  The wall of eventArcs is cellAt H k = -1, i.e. phase pi."""
    ph = np.mod(gam * H, TWOPI)
    idx = np.floor(np.mod(ph + np.pi / m, TWOPI) / (TWOPI / m)).astype(int) % m
    return np.bincount(idx, minlength=m)


def chi2_uniform(counts):
    N = counts.sum()
    m = counts.size
    e = N / m
    chi2 = float(((counts - e) ** 2 / e).sum())
    return chi2, m - 1


def chi2_sf(chi2, df):
    """Upper tail of chi2 without scipy: regularised upper incomplete gamma."""
    import math
    a, x = df / 2.0, chi2 / 2.0
    if x <= 0:
        return 1.0
    if x < a + 1.0:                      # series for P(a,x), return 1-P
        term = 1.0 / a
        s = term
        n = 0
        while abs(term) > 1e-16 * abs(s) and n < 10000:
            n += 1
            term *= x / (a + n)
            s += term
        return 1.0 - s * math.exp(-x + a * math.log(x) - math.lgamma(a))
    # continued fraction for Q(a,x)
    tiny = 1e-300
    b, c = x + 1.0 - a, 1.0 / tiny
    d = 1.0 / b
    h = d
    for i in range(1, 10000):
        an = -i * (i - a)
        b += 2.0
        d = an * d + b
        if abs(d) < tiny:
            d = tiny
        c = b + an / c
        if abs(c) < tiny:
            c = tiny
        d = 1.0 / d
        de = d * c
        h *= de
        if abs(de - 1.0) < 1e-15:
            break
    return h * math.exp(-x + a * math.log(x) - math.lgamma(a))


# ------------------------------------------------------------------ surrogates

def surrogate_smooth(N, t0):
    """DETREND CONTROL: deterministic ordinates carrying the EXACT log-density
    gradient and no fluctuation at all -- t_n solves N_rvm(t) = n - 1/2.
    If the density gradient alone manufactured a harmonic, it shows up here."""
    out = np.empty(N)
    t = max(t0, 14.0)
    for n in range(1, N + 1):
        target = n - 0.5
        for _ in range(60):
            f = rvm(t) - target
            fp = np.log(t / TWOPI) / TWOPI
            step = f / fp
            t -= step
            if abs(step) < 1e-12:
                break
        out[n - 1] = t
    return out


def surrogate_poisson(gam, rng):
    """Poisson set with the same density: invert the smooth count at sorted
    uniforms on [N_rvm(gam_min), N_rvm(gam_max)]."""
    lo, hi = rvm(gam[0]), rvm(gam[-1])
    u = np.sort(rng.uniform(lo, hi, gam.size))
    out = np.empty_like(u)
    t = gam[0]
    for i, target in enumerate(u):
        for _ in range(60):
            f = rvm(t) - target
            fp = np.log(t / TWOPI) / TWOPI
            step = f / fp
            t -= step
            if abs(step) < 1e-12:
                break
        out[i] = t
    return out


def surrogate_reshuffle(gam, rng):
    """Spacing-reshuffle surrogate: keeps the LOCAL spacing law (GUE repulsion,
    empirically) but destroys long-range phase coherence."""
    d = np.diff(gam)
    rng.shuffle(d)
    return gam[0] + np.concatenate([[0.0], np.cumsum(d)])


# ------------------------------------------------------------------ report

def scales():
    lg = np.log
    return [
        ("pi/3      (harmonic)", np.pi / 3),
        ("pi/6      (harmonic)", np.pi / 6),
        ("1         (unit ctrl)", 1.0),
        ("pi/2      (harmonic)", np.pi / 2),
        ("pi/12     (harmonic)", np.pi / 12),
        ("log 2     (POS ctrl)", lg(2.0)),
        ("log 3     (POS ctrl)", lg(3.0)),
        ("log 4     (POS ctrl)", lg(4.0)),
        ("log 5     (POS ctrl)", lg(5.0)),
        ("log 7     (POS ctrl)", lg(7.0)),
        ("log 6     (NEG ctrl)", lg(6.0)),
        ("log 10    (NEG ctrl)", lg(10.0)),
    ]


def run_block(gam, label, jmax=6):
    N = gam.size
    T = gam[-1]
    floor95 = np.sqrt(3.0 / N)          # 95% threshold on |c| under the null
    print(f"\n{'='*78}\n{label}   N = {N}   gamma in [{gam[0]:.2f}, {T:.2f}]"
          f"   |c| 95% null threshold = {floor95:.4f}\n{'='*78}")
    print(f"{'scale H':<22}{'|c_1|':>9}{'pred':>9}{'|c_1|/thr':>11}"
          f"{'max_j|c_j|':>12}{'chi2(6)':>9}{'p':>9}{'chi2(12)':>10}{'p':>9}")
    for name, H in scales():
        c = harmonics(gam, H, jmax=jmax)
        pred = abs(landau_dc(H, 1, T))
        c6 = cell_counts(gam, H, 6)
        c12 = cell_counts(gam, H, 12)
        x6, d6 = chi2_uniform(c6)
        x12, d12 = chi2_uniform(c12)
        print(f"{name:<22}{abs(c[0]):>9.4f}{pred:>9.4f}{abs(c[0])/floor95:>11.2f}"
              f"{np.abs(c).max():>12.4f}{x6:>9.1f}{chi2_sf(x6, d6):>9.4f}"
              f"{x12:>10.1f}{chi2_sf(x12, d12):>9.4f}")


def main():
    gam = load_zeros()
    N, T = gam.size, gam[-1]
    rng = np.random.default_rng(20260811)

    print(__doc__.split("Run:")[0])
    print(f"zeros: N = {N}, gamma_max = {T:.4f}, log(T/2pi)-1 = "
          f"{np.log(T/TWOPI)-1:.4f}")

    print("\n### EXACT DC TABLE (evaluated before any estimate) ###")
    print(f"{'scale H':<22}{'j':>3}{'x = e^{jH}':>14}{'Lambda(x)':>11}{'pred c_j':>11}")
    for name, H in scales():
        for j in (1, 2, 3):
            x = np.exp(j * H)
            print(f"{name:<22}{j:>3}{x:>14.4f}{von_mangoldt_at(x):>11.4f}"
                  f"{landau_dc(H, j, T):>11.4f}")

    run_block(gam, "MEASURED -- actual zeta zeros")

    # ---- controls, matched N and range
    run_block(surrogate_smooth(N, gam[0]),
              "CONTROL A -- smooth surrogate (exact density gradient, no fluctuation)")
    run_block(surrogate_poisson(gam, rng),
              "CONTROL B -- Poisson, same density")
    run_block(surrogate_reshuffle(gam, rng),
              "CONTROL C -- spacing reshuffle (local GUE law kept, long range destroyed)")

    # ---- height-window split: any effect that dies as gamma grows is small-height
    half = N // 2
    run_block(gam[:half], "WINDOW low-gamma  (first half)")
    run_block(gam[half:], "WINDOW high-gamma (second half)")


if __name__ == "__main__":
    main()
