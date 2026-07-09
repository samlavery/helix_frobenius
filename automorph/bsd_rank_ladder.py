"""The BSD rank ladder at the hinge: rank = dimensions of vanishing jet.

Sam's extension: adding dimensions takes the weld picture up the rank ladder.  At the
hinge the collapse wave's jet tower is killed twice over —
  * PARITY (the weld): eps = +1 => Lambda even in t (odd jets vanish structurally);
    eps = -1 => Lambda odd (even jets vanish; HingeKernel.weld_minus_one_forces_zero
    is the 0th layer);
  * RANK: the arithmetic kills the remaining jets below order r.
The first surviving jet IS the BSD leading datum:

    |d^r Lambda/dt^r (0)| = (sqrt(N)/2pi) * L^(r)(1),
    i.e. fit coefficient |c_r| = (sqrt(N)/2pi) * L^(r)(1)/r!  =  (sqrt(N)/2pi) * 2 sum (a_n/n) G_r(2pi n/sqrt(N))

with G_0(x) = e^-x, G_k(x) = int_x^inf G_{k-1}(t) dt/t (Cremona 2.13; G_1 = E1).
Rank 0 = hinge value, 1 = reverb rate, 2 = reverb curvature, 3 = reverb jerk.

Curves (all prime conductor; a_N determined by the weld-pinning test, expect a_N = eps):
  11.a   rank 0  eps +1      37.a   rank 1  eps -1
  389.a  rank 2  eps +1      5077.a rank 3  eps -1
"""
import math

import numpy as np
from scipy.special import exp1, loggamma

from bsd_weld import an_bank, ap_curve, completed_line


def G_ladder(rmax, xs):
    """G_0..G_rmax on grid xs; the dt/t integral done in u = ln t where it is smooth:
    G_k(x) = int_{ln x}^{ln xmax} G_{k-1}(e^u) du, reverse cumulative trapezoid."""
    du = math.log(xs[1] / xs[0])
    Gs = [np.exp(-xs)]
    for _ in range(rmax):
        g = Gs[-1]
        c = np.concatenate([[0.0], np.cumsum(0.5 * (g[1:] + g[:-1]) * du)])
        Gs.append(c[-1] - c)      # tail beyond xmax negligible (e^-80)
    return Gs


XS = np.exp(np.linspace(math.log(1e-8), math.log(80.0), 60000))
GS = G_ladder(3, XS)
# accuracy check of the ladder: G_1 vs scipy E1 on [0.1, 10]
chk = np.exp(np.linspace(math.log(0.1), math.log(10.0), 50))
e1_grid = np.interp(chk, XS, GS[1])
assert np.max(np.abs(e1_grid - exp1(chk)) / exp1(chk)) < 1e-5, "G ladder inaccurate"


def G_r(r, x):
    return np.interp(x, XS, GS[r])


CURVES = [
    ("11.a",   11,   (-1, -10, -20), 0, +1, 0.2538418609),
    ("37.a",   37,   (0, -1, 0),     1, -1, 0.3059997738),
    ("389.a",  389,  (1, -2, 0),     2, +1, 0.7593165003),   # L''(1)/2!
    ("5077.a", 5077, (0, -7, 6),     3, -1, 1.7318499001),   # L'''(1)/3!
]


def exact_tower(a, N, eps, ray, tw):
    """Completed line on the window via the EXACT incomplete-Gamma AFE — the
    double-ended kernel: term 1 = the helix strand (y > 1/sqrt(N)), term 2 =
    eps x the antihelix strand.  Both strands weigh equally at the hinge."""
    import mpmath as mp
    mp.mp.dps = 25
    sq = math.sqrt(N)
    vals = []
    for t in tw:
        s = mp.mpf(1) + 1j * mp.mpf(float(t))
        tot = mp.mpc(0)
        for n in range(1, len(a)):
            if a[n] == 0.0:
                continue
            x = 2 * math.pi * n / sq
            if x > 45:
                break
            r = sq / (2 * math.pi * n)
            tot += a[n] * (r ** s * mp.gammainc(s, x, mp.inf)
                           + eps * r ** (2 - s) * mp.gammainc(2 - s, x, mp.inf))
        vals.append(complex(tot))
    return np.array(vals)


print(f"{'curve':>7} {'r':>2} {'eps(ray)':>9} {'a_N':>4} | exact-kernel jet tower |c_0..c_3|"
      f"{'':>8} | {'c_r exact':>9} {'fiber':>8} {'pred':>9} {'agree':>8} {'lit':>7}")

for tag, N, A, r, eps_exp, lit in CURVES:
    NB = max(40000, int(3.0 * N ** 0.5 * 21 * 4))   # floor 40k: the pinning test needs
    # enough multiples of the bad prime in the bank to discriminate a_N (389 taught this)
    best = None
    for ab in (+1, -1):
        a = an_bank(N, lambda p: ap_curve(p, *A), ab, NB)
        lam = a[1:] / np.sqrt(np.arange(1.0, NB + 1))
        ts = np.linspace(0.05, 12.0, 500)
        Lam = completed_line(lam, N, ts)
        mask = np.abs(Lam) > 0.5 * np.median(np.abs(Lam))
        zbar = np.mean(np.exp(2j * np.mod(np.angle(Lam[mask]), math.pi)))
        if best is None or (1 - abs(zbar)) < best[0]:
            best = (1 - abs(zbar), ab, a, lam, (np.angle(zbar) / 2) % math.pi)
    spread, aN, a, lam, ray = best
    eps = -1 if abs(ray - math.pi / 2) < math.pi / 4 else +1

    tw = np.linspace(-0.5, 0.5, 81)
    V = np.vander(tw, 8, increasing=True)           # c0..c7
    Zx = (exact_tower(a, N, eps, ray, tw) * np.exp(-1j * ray)).real
    cx = np.linalg.lstsq(V, Zx, rcond=None)[0]
    Zf = (completed_line(lam, N, tw) * np.exp(-1j * ray)).real
    cf = np.linalg.lstsq(V, Zf, rcond=None)[0]

    n = np.arange(1, NB + 1, dtype=np.float64)
    x = 2 * math.pi * n / math.sqrt(N)
    series = 2 * np.sum((a[1:] / n) * G_r(r, x))    # L^(r)(1)/r!
    pred_cr = (math.sqrt(N) / (2 * math.pi)) * series
    tower = " ".join(f"{abs(cx[k]):.2e}" for k in range(4))
    print(f"{tag:>7} {r:>2} {eps:+d}({ray/math.pi:.3f}p) {aN:+4d} | {tower} | "
          f"{abs(cx[r]):>9.5f} {abs(cf[r]):>8.4f} {abs(pred_cr):>9.5f} "
          f"{abs(cx[r]/pred_cr):>8.5f} {series/lit:>7.4f}")

print()
print("Jet tower from an 8-term fit of the ray-rotated completed wave on |t| <= 0.5, exact")
print("double-ended kernel (helix + eps*antihelix incomplete-Gamma strands).  'fiber' = the")
print("same jet from the single-ended tapered bank: accurate at small conductor, develops a")
print("~1e-2 hinge floor by N ~ 5000 — at the hinge both strands weigh equally, so the")
print("antihelix cannot be smoothed away.  'pred' = (sqrt(N)/2pi) * 2 sum (a_n/n) G_r(2pi n/sqrt(N));")
print("'lit' = our G-series / literature (LMFDB, Gross-Zagier, BGZ).")
print("Reading: parity kills alternate jets exactly (weld), rank kills the rest, and the")
print("first live jet IS the BSD leading datum: rank = dimensions added at the hinge.")
print("CAVEAT: the pinning a_N determination works while N^(-1/2) exceeds the single-strand")
print("fiber floor (~1e-2): decisive at 37 (4 orders) and 389 (40x), masked at 5077 — its")
print("a_N column is noise there (Atkin-Lehner theory: a_N = eps for prime conductor).")
print("The exact-kernel tower never feels a_N (bad prime beyond the kernel cutoff).")
