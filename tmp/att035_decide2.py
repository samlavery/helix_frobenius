"""
att035 part 2 -- the restatement kill, the Tsang-class comparison, and the
                 charge optimisation with the ACTUAL Simonic constants.

NULLS (pre-registered, part 1 of this file's header applies):
 N0 restatement: REJECT if the sech-weighted strip functional reproduces BGSTB's
     BOTH published proportions.
 N2 the prize:  REJECT if max_A [2 - Z(A) - charge(A)] < 0.6725007.
 N3 charge form: REJECT if the amplification e^{2 S A} multiplies the count.
"""
import numpy as np
from scipy.integrate import quad
import cvxpy as cp

SEP = "=" * 78
MT = 0.5 + 2 ** -0.5 / np.tan(2 ** -0.5)
r2 = np.sqrt(2.0)
jF = lambda a: max(0.0, 1.0 - abs(a))
# Montgomery-Taylor alpha-side = autocorrelation of v(s)=cos(sqrt2 s) on |s|<=1/2,
# normalised by (1 - cos sqrt2).  Pinned by BGSTB's own stated jM(0)=1.0061271908.
def jM(a):
    t = jF(a)
    return ((0.5 / r2) * np.sin(r2 * t) + 0.5 * t * np.cos(r2 * a)) / (1 - np.cos(r2))

print(SEP); print("N0 RESTATEMENT GATE -- reproduce BGSTB (7.2) from the strip functional")
print(f"    jM(0) = {jM(0.0):.10f}   BGSTB print Khat(0)=jM(0)=1.0061271908")
def Z_sech(j, W=1.0, S=1.0):
    num = j(0.0) + 2 * quad(lambda a: a * j(a) / np.cosh(a * W), 0, 1, limit=400)[0]
    den = 2 * quad(lambda a: j(a) / np.cosh(a * W), 0, S, limit=400)[0]
    return num / den
for nm, j, tgt in (("Fejer j_F", jF, 0.608612927), ("Mont-Taylor j_M", jM, 0.617483786)):
    Z = Z_sech(j)
    print(f"    {nm:16s} Z(W=1) = {Z:.9f}   2-Z = {2-Z:.9f}   BGSTB {tgt}"
          f"   |diff|={abs(2-Z-tgt):.2e}")
print(f"    gate 2*int a jM sech = {2*quad(lambda a: a*jM(a)/np.cosh(a),0,1)[0]:.10f}"
      f"   (BGSTB 0.2832624869)")
print(f"    gate   int   jM sech = {quad(lambda a: jM(a)/np.cosh(a),0,1)[0]:.10f}"
      f"   (BGSTB piK(0)=0.4663199124)")
print("    => at W=1 the strip functional IS BGSTB/Tsang's, term for term.")

# ---------------------------------------------------------------- SDP
def Zsdp(A, S=2.0, D=0.04, dip=True, nonneg_band=False):
    n = int(round(S / D)); x = np.arange(n) * D; W = 2.0 * A
    sech = 1.0 / np.cosh(x * W)
    Q = cp.Variable((n, n), symmetric=True)
    b = cp.hstack([cp.trace(Q)] + [sum(Q[k, k + j] for k in range(n - j)) for j in range(1, n)])
    c = cp.multiply(sech, b)
    w1 = np.where(x <= 1.0, x, 0.0) * 2.0; w1[0] = D / 2.0
    cons = [Q >> 0, c[0] + 2 * cp.sum(c[1:]) == 1]
    if dip:
        cons.append(c[x >= 1.0 - 1e-12] <= 0)
    else:
        cons += [c[x > 1.0 + 1e-12] == 0, b[n - 1] == 0]
    if nonneg_band:
        cons.append(c[x <= 1.0 + 1e-12] >= 0)          # Tsang's j >= 0
    p = cp.Problem(cp.Minimize(c[0] / D + w1 @ c), cons); p.solve(solver=cp.CLARABEL)
    return p.value, p.status

print(SEP); print("Tsang-class comparison at W=1 (=BGSTB's box A=1/2): how much does")
print("optimising over the class buy over BGSTB's fixed j_M (Z = 1.3825236)?")
zbg = Z_sech(jM)
for lbl, kw in (("S=1, j>=0 (exactly Tsang's class)", dict(S=1.0, dip=False, nonneg_band=True)),
                ("S=1, j free sign on band       ", dict(S=1.0, dip=False)),
                ("S=2, dip allowed (CGdL class)  ", dict(S=2.0, dip=True))):
    v4, _ = Zsdp(0.5, D=0.04, **kw); v2, _ = Zsdp(0.5, D=0.02, **kw)
    r = v2 + (v2 - v4) / 3
    print(f"    {lbl}: Z = {r:.6f}   2-Z = {2-r:.6f}   (BGSTB j_M: {zbg:.6f} / {2-zbg:.6f})")

print(SEP); print("Z(A) at the saturated type S=4 (CGdL's own type) + the crossing")
S4 = []
for A in (0.0, 0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35, 0.50):
    v, st = Zsdp(A, S=4.0, D=0.05)
    S4.append((A, v)); print(f"    A={A:<5} Z(S=4,D=.05) = {v:.6f}  [{st}]")

# --------------------------------------------------------- the charge
print(SEP); print("THE CHARGE.  Simonic Thm 1 corollary (arXiv:1910.08274v2 p.2), read at source:")
print("    N(sigma,T) <= [10395.21/(2^{1-(1/4)(sigma-1/2)}-1)] T^{1-(1/4)(sigma-1/2)} log(T/2)")
print("    sigma = 1/2 + A/log T  =>  T^{-(1/4)(sigma-1/2)} = e^{-A/4} exactly, c = 1/4.")
print("    /N(T) ~ (T/2pi)log T  =>  C_1sided -> 2pi*10395.21, C_2sided = 2x that.")
Cs = {"Simonic Thm1 (T>=6.1e10)": 2 * np.pi * 10395.21,
      "Simonic eq(5) (T>=2e50) ": 2 * np.pi * 5.357,
      "Simonic method FLOOR    ": 2 * np.pi * 3.259,
      "fantasy C=1             ": 1.0}
for k, v in Cs.items():
    print(f"    C_1sided[{k}] = {v:12.2f}   C_2sided = {2*v:12.2f}"
          f"   charge<1 needs A > {4*np.log(2*v):.2f}")

# continuum Z(A) from my Richardson S=2 run (att035_ZA.npy) + interpolation
ZA = np.load("/Users/samuellavery/work/helix_frobenius/tmp/att035_ZA.npy")
Ag, Zg = ZA[:, 0], ZA[:, 3]
Zf = lambda a: np.interp(a, Ag, Zg, right=Zg[-1] + 0.62 * (a - Ag[-1]))   # B: dZ/dA -> 0.62

print(SEP)
print("TABLE 2  net constant  2 - Z(A) - C e^{-A/4},  C = 2*2pi*10395.21 = %.0f (two-sided)"
      % (2 * 2 * np.pi * 10395.21))
print(f"{'A':>6} {'Z(A)':>10} {'2-Z(A)':>10} {'charge':>14} {'net':>14}")
best = (-1e9, None)
for A in [0.0, 0.1, 0.2, 0.206, 0.3, 0.5, 1.0, 2.0, 5.0, 10.0, 20.0, 44.4, 47.1, 60.0, 100.0]:
    Z = Zf(A); ch = 2 * 2 * np.pi * 10395.21 * np.exp(-A / 4); net = 2 - Z - ch
    if net > best[0]: best = (net, A)
    print(f"{A:6.2f} {Z:10.5f} {2-Z:10.5f} {ch:14.4g} {net:14.5g}")
print(f"    max net = {best[0]:.5g} at A = {best[1]}   vs target 0.6725007  "
      f"-> short by {0.6725007-best[0]:.5g}")

print(SEP); print("TABLE 3  same, at Simonic's own method floor C_2sided = %.2f (unattainable"
                  " today; the best any refinement of his method could give)"
                  % (2 * 2 * np.pi * 3.259))
best2 = (-1e9, None)
print(f"{'A':>6} {'Z(A)':>10} {'2-Z(A)':>10} {'charge':>14} {'net':>14}")
for A in [0.0, 0.2, 0.5, 1.0, 2.0, 5.0, 10.0, 12.1, 15.0, 20.0, 30.0, 40.0]:
    Z = Zf(A); ch = 2 * 2 * np.pi * 3.259 * np.exp(-A / 4); net = 2 - Z - ch
    if net > best2[0]: best2 = (net, A)
    print(f"{A:6.2f} {Z:10.5f} {2-Z:10.5f} {ch:14.4g} {net:14.5g}")
print(f"    max net = {best2[0]:.5g} at A = {best2[1]}")

print(SEP); print("TABLE 4  REQUIREMENT INVERSION: what exponent c would be needed?")
print("    need  C e^{-cA} < 2 - Z(A) - 0.6725007  for some A>0")
for lbl, C in (("C=1 (fantasy)", 1.0), ("C=40.95 (Simonic floor, 2-sided)", 2*2*np.pi*3.259),
               ("C=130629 (Simonic Thm 1, 2-sided)", 2*2*np.pi*10395.21)):
    creq = np.inf; aat = None
    for A in np.arange(0.001, 0.30, 0.0005):
        prize = 2 - Zf(A) - 0.6725007
        if prize <= 0: continue
        c = np.log(C / prize) / A
        if c < creq: creq, aat = c, A
    print(f"    {lbl:34s}: need c >= {creq:8.1f}  (at A={aat:.4f});  "
          f"Selberg gives c = 0.25  -> short by {creq/0.25:.0f}x")

print(SEP); print("N3  THE CHARGE IS NOT A COUNT (BGSTB sec.6, in print).")
print("    |K(-i(rho-rho')log T)| << e^{S|Im|}/|.|^2 = T^{S|beta-beta'|};  BGSTB bound it by")
print("    (1/2)(T^{2S(beta-1/2)} + T^{2S(beta'-1/2)}) = e^{2SA} at depth A/log T.")
print("    So charge(A) ~ C e^{-cA} * e^{2SA} = C e^{(2S-c)A}, INCREASING in A for c<2S.")
print(f"{'A':>6} {'S=1: Ce^{(2-1/4)A}':>22} {'S=2: Ce^{(4-1/4)A}':>22}   (C=130629)")
for A in [0.0, 0.2, 0.5, 1.0, 2.0]:
    C = 2 * 2 * np.pi * 10395.21
    print(f"{A:6.2f} {C*np.exp((2-.25)*A):22.4g} {C*np.exp((4-.25)*A):22.4g}")
print("    minimum over A>=0 is at A=0 and equals C = 130629 >> 0.0063 (the whole prize).")
print("    Need c > 2S just for convergence: c>2 (S=1) = the near-line Density Hypothesis")
print("    (OPEN); c>4 (S=2) = BEYOND it.  Available: c=1/4 explicit, c<8/7 unpublished.")
print(SEP)
