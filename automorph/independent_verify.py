"""Independent verification of the repo's Python mathematics.

Written from the spec/paper formulas directly; uses the repo code only as the
OBJECT under test (never as the ground-truth side of a comparison).
"""
import math
import sys

import mpmath as mp
import numpy as np

sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius")
sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius/carrier_fiber")

mp.mp.dps = 30

CHARS = {
    "eta_trivial": (2, None),
    "chi3": (3, [0, 1, -1]),
    "chi4": (4, [0, 1, 0, -1]),
    "chi5": (5, [0, 1, -1, -1, 1]),
    "chi8": (8, [0, 1, 0, -1, 0, -1, 0, 1]),
}


def L_hurwitz(vals, q, s):
    """L(s, chi) = q^-s sum_a chi(a) zeta(s, a/q) -- my own transcription of the classical formula."""
    return q ** (-s) * mp.fsum(vals[a] * mp.zeta(s, mp.mpf(a) / q) for a in range(1, q) if vals[a])


def Lval(name, t):
    q, vals = CHARS[name]
    s = mp.mpf("0.5") + mp.mpc(0, 1) * t
    if name == "eta_trivial":
        return mp.zeta(s)
    return L_hurwitz(vals, q, s)


print("=" * 78)
print("[1] REFERENCE_GAMMAS: is each listed gamma a genuine zero of the actual L?")
print("    newton_dist = |L/L'| at the listed gamma ~ distance to the true zero")
from carrier_fiber import REFERENCE_GAMMAS  # noqa: E402

worst = {}
for name, gams in REFERENCE_GAMMAS.items():
    wd = 0.0
    for g in gams:
        t = mp.mpf(repr(g))
        f = Lval(name, t)
        h = mp.mpf("1e-8")
        fp = (Lval(name, t + h) - Lval(name, t - h)) / (2 * h)
        d = abs(f / fp)
        wd = max(wd, float(d))
    worst[name] = wd
    print(f"    {name:12s} {len(gams):>2} zeros   max newton-dist to true zero = {wd:.1e}")

print()
print("[2] Lane equality P=M at a zero (spec sec 7.3): zeta(s,1/3) = zeta(s,2/3)")
g1 = mp.mpf("8.039737155681467")
s = mp.mpf("0.5") + mp.mpc(0, 1) * g1
diff_on = abs(mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))
s_off = mp.mpf("0.5") + mp.mpc(0, 1) * mp.mpf("9.5")
diff_off = abs(mp.zeta(s_off, mp.mpf(1) / 3) - mp.zeta(s_off, mp.mpf(2) / 3))
print(f"    |zeta(s,1/3)-zeta(s,2/3)| at gamma_1(chi3) = {float(diff_on):.2e}   off-zero (y=9.5) = {float(diff_off):.3f}")

print()
print("[3] Convergence envelope claim: |S_N(gamma)| ~ 0.667/sqrt(N) at a zero (spec sec 5)")


def S_N(vals_fn, y, N, sigma=0.5):
    n = np.arange(1, N + 1, dtype=np.float64)
    return abs(np.sum(vals_fn(n) * n ** (-sigma) * np.exp(-1j * y * np.log(n))))


eta_fn = lambda n: np.where(n % 2 == 1, 1.0, -1.0)
chi3_fn = lambda n: np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))
for lbl, fn, y in [("eta @ 14.1347...", eta_fn, 14.134725141734694), ("chi3 @ 8.0397...", chi3_fn, 8.039737155681467)]:
    cs = [S_N(fn, y, N) * math.sqrt(N) for N in (100_000, 400_000, 1_600_000)]
    off = S_N(fn, y + 0.5, 400_000)
    print(f"    {lbl:18s} |S_N|*sqrt(N) at N=1e5,4e5,1.6e6 = {cs[0]:.3f}, {cs[1]:.3f}, {cs[2]:.3f}   |S(off)| = {off:.3f}")

print()
print("[4] Abel-summation strip fiber vs analytic value (helix_phasor_tool.abel_fiber)")
import helix_phasor_tool as H  # noqa: E402

for s_test in (0.7 + 3.2j, 0.5 + 2.0j):
    a_eta = H.abel_fiber(H.eta_coeff, s_test, M=30000)
    t_eta = complex((1 - mp.power(2, 1 - mp.mpc(s_test))) * mp.zeta(mp.mpc(s_test)))
    a_c3 = H.abel_fiber(H.chi_mod3, s_test, M=30000)
    t_c3 = complex(L_hurwitz([0, 1, -1], 3, mp.mpc(s_test)))
    print(f"    s={s_test}:  |abel_eta - (1-2^(1-s))zeta| = {abs(a_eta - t_eta):.1e}   |abel_chi3 - L| = {abs(a_c3 - t_c3):.1e}")

print()
print("[5] Helix arclength closed form vs independent numerical quadrature (p=1, r=3)")
p, r = 1.0, 3.0
for k in (0.7, 5.0, 42.0):
    closed = H.arclength(p, r, k)
    quad = float(mp.quad(lambda t: mp.sqrt(p * p + r * r + (2 * mp.pi * r * t) ** 2), [0, k]))
    print(f"    k={k:>5}:  closed={closed:.10f}  quad={quad:.10f}  |diff|={abs(closed - quad):.1e}")

print()
print("[6] Area law r_n^2/n -> r*Delta/pi, via MY OWN inversion (bisection on the quad arclength)")


def my_theta(nn):
    s_target = nn * math.pi / 3
    lo, hi = 0.0, 1.0
    F = lambda k: float(mp.quad(lambda t: mp.sqrt(p * p + r * r + (2 * mp.pi * r * t) ** 2), [0, k]))
    while F(hi) < s_target:
        hi *= 2
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        if F(mid) < s_target:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


for nn in (2000, 20000):
    k = my_theta(nn)
    print(f"    n={nn}: (r*k)^2/n = {(r * k) ** 2 / nn:.6f}   target r*Delta/pi = {r * (math.pi / 3) / math.pi:.6f}")

print()
print("[7] Exact six-cell closure (eta on the mu_6 cell): sum_(s=0..5) (-1)^s e^(i pi s/3)")
tot = sum((-1) ** k * mp.expjpi(mp.mpf(k) / 3) for k in range(6))
print(f"    |sum| = {float(abs(tot)):.2e}  (should be exactly 0: full geometric cycle, ratio e^(i4pi/3))")

print()
print("[8] carrier_fiber.analytic_channels vs Lean Achan/Bchan semantics")
from carrier_fiber import CHARACTERS, CarrierFiber, UCELL  # noqa: E402

fib = CarrierFiber(CHARACTERS["eta_trivial"])
g = 14.134725141734694
A, B = fib.analytic_channels(g / UCELL, dps=40)
myA = complex(mp.zeta(mp.mpf("1.5") + 1j * mp.mpf(repr(g))) * (1 - mp.power(2, 1 - (mp.mpf("1.5") + 1j * mp.mpf(repr(g))))))
print(f"    A = eta(3/2+i*gamma1): code={A:.10f}  mine={myA:.10f}  |diff|={abs(A - myA):.1e}")
print(f"    B = (pi/3)*eta(1/2+i*gamma1): |B| = {abs(B):.1e}  (should be ~0 at the zero)")
fib3 = CarrierFiber(CHARACTERS["chi3"])
g3 = 8.039737155681467
A3, B3 = fib3.analytic_channels(g3 / UCELL, dps=40)
myA3 = complex(L_hurwitz([0, 1, -1], 3, mp.mpf("1.5") + 1j * mp.mpf(repr(g3))))
print(f"    A = L_chi3(3/2+i*gamma1): code={A3:.10f}  mine={myA3:.10f}  |diff|={abs(A3 - myA3):.1e}")
print(f"    B = (pi/3)*L_chi3(1/2+i*gamma1): |B| = {abs(B3):.1e}")

print()
print("[9] Spec sec-2 phasors-per-turn table at n=1000 (geometric / live)")
import helix_geometry_3d as G  # noqa: E402

spec_geo = {"eta": 297, "chi3": 489, "chi4": 803, "chi5": 1309, "chi8": 4664}
spec_live = {"eta": 297, "chi3": 326, "chi4": 401, "chi5": 1047, "chi8": 2332}
for nm in ("eta", "chi3", "chi4", "chi5", "chi8"):
    ch = G.CHARACTERS[nm]
    b = G.radial_b(ch.q)
    geo = G.phasors_per_turn(1000, b)
    live = G.active_phasors_per_turn(1000, b, ch.active_fraction)
    print(f"    {nm:5s} geometric={geo:8.1f} (spec {spec_geo[nm]:>4})   live={live:8.1f} (spec {spec_live[nm]:>4})")

print()
print("[10] Spec sec-4 cancellation heights e^gamma")
for nm, g1v, hexp in [("chi3", 8.039737, 3.10e3), ("chi4", 6.020949, 4.12e2), ("eta", 14.134725, 1.38e6)]:
    print(f"    {nm:5s} e^{g1v} = {math.exp(g1v):.3e}   spec {hexp:.2e}")

print()
print("done")
