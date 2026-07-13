"""The calibrated center-reading, stage 1: a general self-certifying AFE evaluator.

Target 1 of the rung-4 campaign: the value of the degree-16 fiber at its
non-critical center, calibrated on the factorable f^{x4} case
(zeta^2 * Sym2^3 * Sym4).  This file builds the enabling machinery -- a
GENERAL completed-L evaluator with the split-vs-direct certificate -- and runs
it up the ladder with gates at every rung:

  GATE A (machinery): zeta(1/2) via the general evaluator vs the known
         -1.4603545088...  (degree 1, G = GammaR(s), Q = 1).
  GATE B (GL(2)): L(11a1, 1/2)_unitary vs the house value 0.2538418608
         (drift_observability jet 0), G = Q^{s/2} GammaC(s + 1/2), Q = 11.
  SYM2  (degree 3): coefficients from point counts (Chebyshev U2 phases,
         Steinberg at 11), Gamma shape / sign SCANNED and self-certified by
         split-vs-direct at s0 = 2.5; then the central value L(Sym2 f, 1/2)_u.
  SYM4  (degree 5): same, shape scanned; central value.
  ASSEMBLY: the factored center value of f^{x4},
         zeta(1/2)^2 L(Sym2,1/2)^3 L(Sym4,1/2) -- the classical side of the
         rung-4 calibration, computed from scratch.

Everything from point counts + mpmath contours; no L-library.  The completed
function is Lambda(s) = G(s) L(s), G(s) = Q^{s/2} prod Gamma-factors,
FE Lambda(s) = eps Lambda(1-s); the split identity

  Lambda(s0) = sum_n lam_n [ H(s0, y_n) + eps H(1-s0, y_n) ],
  H(s, y) = (1/2 pi i) int G(w) y^{-w} dw / (w - s),   y_n = n / sqrt(Q)?

with y_n absorbed so that the direct side is Lambda(s0) = G(s0) sum lam_n n^{-s0}:
concretely H(s, y_n) with y_n = n and G carrying Q^{w/2} -- the contour kernel
is cached on a log-grid in y and interpolated.

Run: python3 center_reading.py       (~3-6 min)
"""
import sys, os, math
import numpy as np
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH

mp.mp.dps = 25

AINV = (0, -1, 1, -10, -20)     # 11a1
N11 = 11
AP_BAD = {11: 1}                # a_11 = 1 (Steinberg, split multiplicative)


# ---------------------------------------------------------------- G-factors
def make_G(Q, factors):
    """G(s) = Q^{s/2} * prod of GammaR(s+a) / GammaC(s+a) factors.
    factors: list of ('R'|'C', shift)."""
    def G(s):
        out = mp.mpf(Q) ** (s / 2)
        for typ, a in factors:
            if typ == 'R':
                out *= mp.pi ** (-(s + a) / 2) * mp.gamma((s + a) / 2)
            else:
                out *= 2 * (2 * mp.pi) ** (-(s + a)) * mp.gamma(s + a)
        return out
    return G


def H_grid(G, s, ys, T=60, NODES=12001, M=1600):
    """H(s, y) = (1/2pi) int G(c+it) y^{-(c+it)} / (c+it - s) dt for every y,
    with G evaluated ONCE on a fixed Simpson grid in t and the y-dependence
    vectorized in numpy (chunked log-grid + interpolation)."""
    # contour right of Re(s) AND right of every Gamma pole (poles at w <= 0)
    c = max(float(mp.re(s)) + 1.5, 0.8)
    ts = np.linspace(-T, T, NODES)
    Gv = np.array([complex(G(mp.mpc(c, t))) for t in ts])
    w = np.ones(NODES)
    w[1:-1:2], w[2:-1:2] = 4.0, 2.0
    w *= (ts[1] - ts[0]) / 3.0
    sc = complex(s)
    denom = (c + 1j * ts) - sc
    base = Gv / denom * w
    ys = np.asarray(ys, dtype=float)
    lo, hi = np.log(ys.min()) - 0.05, np.log(ys.max()) + 0.05
    gl = np.linspace(lo, hi, M)
    vals = np.zeros(M, dtype=complex)
    CH = 200
    for i in range(0, M, CH):
        blk = gl[i:i + CH]
        phase = np.exp(-1j * np.outer(blk, ts))
        vals[i:i + CH] = np.exp(-c * blk) * (phase @ base) / (2 * math.pi)
    re = np.interp(np.log(ys), gl, vals.real)
    im = np.interp(np.log(ys), gl, vals.imag)
    return re + 1j * im


def split_parts(G, lam, s0, T=60):
    """(main, mirror) parts of the split identity; Lambda = main + eps*mirror."""
    n = np.arange(1, len(lam))
    keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float)
    H1 = H_grid(G, mp.mpf(s0), ys, T=T)
    H2 = H_grid(G, 1 - mp.mpf(s0), ys, T=T)
    a = complex((lam[1:][keep] * H1).sum())
    b = complex((lam[1:][keep] * H2).sum())
    return a, b


def direct_value(G, lam, s0):
    n = np.arange(1, len(lam))
    return complex(G(mp.mpf(s0))) * float((lam[1:] * n ** (-float(s0))).sum())


def certify(G, lam, s0=2.5, T=60, pole=False):
    """Return (eps, rel_true, rel_other).  pole=True adds the zeta-pole terms
    -1/s - 1/(1-s) to the split side (for the pure-zeta gate)."""
    d = direct_value(G, lam, s0)
    a, b = split_parts(G, lam, s0, T=T)
    corr = (-1.0 / s0 - 1.0 / (1 - s0)) if pole else 0.0
    res = {e: abs((a + e * b + corr) - d) / max(abs(d), 1e-30) for e in (+1, -1)}
    eps = +1 if res[+1] < res[-1] else -1
    return eps, res[eps], res[-eps]


def central_value(G, eps, lam, T=60, pole=False):
    """L(1/2) = Lambda(1/2)/G(1/2); Lambda(1/2) = (1+eps) sum lam_n H(1/2,n)
    (+ pole terms -4 for pure zeta)."""
    if eps == -1:
        return None                          # forced zero; derivative needed
    n = np.arange(1, len(lam))
    keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float)
    H1 = H_grid(G, mp.mpf("0.5"), ys, T=T)
    lam_val = 2.0 * (lam[1:][keep] * H1).sum() + (-4.0 if pole else 0.0)
    return complex(lam_val) / complex(G(mp.mpf("0.5")))


# ------------------------------------------------------------- coefficient banks
def bank_gl1(nmax):
    lam = np.ones(nmax + 1)
    lam[0] = 0
    return lam


def bank_gl2_unitary(nmax):
    bad = {int(p): SH.a_bad(int(p), AINV) for p in SH.sieve_primes(N11)
           if N11 % int(p) == 0}
    a = SH.bank_general(N11, AINV, bad, nmax)
    n = np.arange(0, nmax + 1, dtype=float)
    lam = np.zeros(nmax + 1)
    lam[1:] = a[1:] / np.sqrt(n[1:])
    return lam


def bank_sym_unitary(r, nmax):
    """lambda_n of Sym^r(11a1), unitary, incl. the Steinberg factor at 11."""
    lam = np.zeros(nmax + 1)
    lam[1] = 1.0
    for p in SH.sieve_primes(nmax):
        kmax = int(math.log(nmax) / math.log(p))
        if p == N11:
            alpha = AP_BAD[11] / math.sqrt(11)     # Steinberg eigenvalue
            c = np.array([alpha ** (r * k) for k in range(kmax + 1)])
        else:
            b = max(-2.0, min(2.0, SH.ap_general(p, *AINV) / math.sqrt(p)))
            t = math.acos(b / 2.0)
            phases = [(r - 2 * k) * t for k in range(r + 1)]
            poly = np.array([1.0 + 0j])
            for ph in phases:
                poly = np.convolve(poly, np.array([1.0, -np.exp(1j * ph)]))
            c = np.zeros(kmax + 1, dtype=complex)
            c[0] = 1.0
            for k in range(1, kmax + 1):
                acc = 0j
                for j in range(1, min(k, len(poly) - 1) + 1):
                    acc -= poly[j] * c[k - j]
                c[k] = acc
            c = c.real
        for k in range(kmax, 0, -1):
            pk = p ** k
            for m in range(1, nmax // pk + 1):
                if m % p:
                    lam[m * pk] += c[k] * lam[m]
    return lam


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# CENTER READING, stage 1 -- general self-certifying AFE evaluator")
    P("#" * 78)
    P()

    # GATE A: zeta, with the pole terms -1/s - 1/(1-s) included exactly
    Gz = make_G(1, [('R', 0)])
    lamz = bank_gl1(400)
    P("GATE A (zeta, pole terms included): certificate + zeta(1/2):")
    eps, r1, r2 = certify(Gz, lamz, s0=2.5, T=40, pole=True)
    Lz = central_value(Gz, eps, lamz, T=40, pole=True)
    zknown = -1.4603545088
    P(f"  eps = {eps:+d} (match {r1:.1e} vs wrong {r2:.1e});  "
      f"zeta(1/2) = {Lz.real:.8f}  (known {zknown})")
    okA = eps == +1 and abs(Lz.real - zknown) < 1e-5
    P(f"  GATE A: {'PASS' if okA else 'FAIL'}")
    P()

    # GATE B: 11a1
    P("GATE B (11a1, degree 2): certificate + central value vs house 0.2538419:")
    G2 = make_G(11, [('C', 0.5)])
    lam2 = bank_gl2_unitary(1200)
    eps2, r1, r2 = certify(G2, lam2, s0=2.5, T=60)
    L2 = central_value(G2, eps2, lam2, T=60)
    P(f"  eps = {eps2:+d} (match {r1:.1e} vs wrong {r2:.1e});  "
      f"L(1/2) = {L2.real:.7f}  (house: 0.2538419)")
    okB = eps2 == +1 and abs(L2.real - 0.2538419) < 2e-4 and abs(L2.imag) < 1e-6
    P(f"  GATE B: {'PASS' if okB else 'FAIL'}")
    P()

    if not okB:
        P("ABORT: fix the evaluator before climbing.")
        with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                               "center_reading_results.txt"), "w") as f:
            f.write("\n".join(lines) + "\n")
        return

    # SYM2: shape scan
    P("SYM2(11a1), degree 3, Q = 121: shape scan (self-certifying):")
    lam3 = bank_sym_unitary(2, 3000)
    best = None
    for dlt in (0.0, 1.0):
        G3 = make_G(121, [('C', 1.0), ('R', dlt)])
        eps3a, r1a, _ = certify(G3, lam3, s0=2.5, T=60)
        eps3b, r1b, _ = certify(G3, lam3, s0=2.2, T=60)
        agree = (eps3a == eps3b)
        r1 = max(r1a, r1b)
        P(f"  shape GammaC(s+1) GammaR(s+{dlt:.0f}): eps {eps3a:+d}/{eps3b:+d}, "
          f"two-point match {r1a:.2e}, {r1b:.2e}")
        if agree and (best is None or r1 < best[0]):
            best = (r1, dlt, eps3a, G3)
    r1, dlt, eps3, G3 = best
    ok3 = r1 < 1e-4
    P(f"  selected shape: GammaR shift {dlt:.0f}, eps = {eps3:+d}, "
      f"match {r1:.1e}   {'CERTIFIED' if ok3 else 'NOT CERTIFIED'}")
    if ok3:
        L3 = central_value(G3, eps3, lam3, T=60)
        if L3 is None:
            P("  eps = -1: central value forced zero (derivative next stage)")
        else:
            P(f"  L(Sym2 11a1, 1/2)_u = {L3.real:.7f}  (imag {L3.imag:.1e})")
    P()

    # SYM4: shape scan
    P("SYM4(11a1), degree 5, Q = 14641: shape scan (self-certifying):")
    lam5 = bank_sym_unitary(4, 6000)
    best = None
    for dlt in (0.0, 1.0):
        G5 = make_G(14641, [('C', 2.0), ('C', 1.0), ('R', dlt)])
        eps5a, r1a, _ = certify(G5, lam5, s0=2.5, T=60)
        eps5b, r1b, _ = certify(G5, lam5, s0=2.2, T=60)
        agree = (eps5a == eps5b)
        r1 = max(r1a, r1b)
        P(f"  shape GammaC(s+2) GammaC(s+1) GammaR(s+{dlt:.0f}): eps "
          f"{eps5a:+d}/{eps5b:+d}, two-point match {r1a:.2e}, {r1b:.2e}")
        if agree and (best is None or r1 < best[0]):
            best = (r1, dlt, eps5a, G5)
    r1, dlt, eps5, G5 = best
    ok5 = r1 < 1e-4
    P(f"  selected shape: GammaR shift {dlt:.0f}, eps = {eps5:+d}, "
      f"match {r1:.1e}   {'CERTIFIED' if ok5 else 'NOT CERTIFIED'}")
    L5 = None
    if ok5:
        L5 = central_value(G5, eps5, lam5, T=60)
        if L5 is None:
            P("  eps = -1: central value forced zero (derivative next stage)")
        else:
            P(f"  L(Sym4 11a1, 1/2)_u = {L5.real:.7f}  (imag {L5.imag:.1e})")
    P()

    P("VERDICT (stage 1):")
    if okB and ok3 and ok5:
        zc = float(mp.zeta(0.5))
        P(f"  evaluator validated (Gate B), Sym2 and Sym4 shapes CERTIFIED by")
        P(f"  split-vs-direct with no external input.")
        if L3 is not None and L5 is not None:
            prod = zc ** 2 * L3.real ** 3 * L5.real
            P(f"  ASSEMBLY -- the factored center of f^(x4) (classical side of")
            P(f"  the rung-4 calibration):")
            P(f"    zeta(1/2)^2 * L(Sym2,1/2)^3 * L(Sym4,1/2)")
            P(f"    = ({zc:.7f})^2 * ({L3.real:.7f})^3 * ({L5.real:.7f})")
            P(f"    = {prod:.9f}")
            P(f"  Next stage: the windowed carrier reading of the degree-16")
            P(f"  bank, calibrated to this value, then the primitive quadruple")
            P(f"  -- the prediction.")
    else:
        P(f"  Gate/certification status: B {okB}, Sym2 {ok3}, Sym4 {ok5} --")
        P(f"  extend the scan set (shifts, Q, eps) where uncertified.")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "center_reading_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to center_reading_results.txt]")


if __name__ == "__main__":
    main()
