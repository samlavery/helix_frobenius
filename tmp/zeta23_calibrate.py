"""STEP 1 -- CALIBRATION against Zeta23 Table 3 / p.26 trace-level check.

Targets (T=2000, I=[2000,4000], l=5.763, G from 3700 zeros, N(I)=1957):
   lambda=1.0 eta=0.05:  d=1834  C_zero=1436.41  C/N=0.734  ("tapered law" 0.741)
   lambda=0.9 eta=0.10:  d=1650  C_zero=1322.28  C/N=0.676  ("tapered law" 0.688)
   lambda=0.9 eta=0.05:  d=1650              C/N=0.687  ("tapered law" 0.699)
   lambda=0.9 eta=0.20:  d=1650              C/N=0.651  ("tapered law" 0.665)
   lambda=1.0 eta=0.10:  d=1834              C/N=0.723  ("tapered law" 0.731)
"""
import time
import numpy as np
from zeta23_bench import phihat, a_const, b_const, load_zeros, traces, rvm

T = 2000.0
l = np.log(T / (2 * np.pi))
l1 = l + 2 * np.log(2) - 1
NI = T * l1 / (2 * np.pi)          # Riemann-von Mangoldt main term for [T,2T]
gam_all = load_zeros()
gam = gam_all[:3700]               # the paper's set: "G from 3700 zeros"

print(f"T={T}  l={l:.6f}  l1={l1:.6f}  N(I) main term = {NI:.2f}  (paper: 1957)")
print(f"zeros used: {gam.size}, range [{gam[0]:.3f}, {gam[-1]:.3f}]")
print()
print(f"{'lam':>5} {'eta':>5} {'L':>8} {'X':>8} {'d':>6} {'a':>8} "
      f"{'trGt':>11} {'trGt/(aL)':>10} {'trGt^2':>12} {'C':>10} {'C/N':>7} "
      f"{'paper C/N':>9} {'law':>7}")


def tapered_law(lam, eta):
    """paper p.25: (tr Gt)^2/tr Gt^2 ~ N lam a^2/(b + lam^2 J(eta)),
    J(eta) -> 1/3 - (0.60-0.35 eta) eta."""
    J = 1.0 / 3.0 - (0.60 - 0.35 * eta) * eta
    L = lam * l
    w = eta * L / 2
    a, b = a_const(L, w), b_const(L, w)
    return lam * a**2 / (b + lam**2 * J)


rows = []
for lam, eta, paper in [(1.0, 0.05, 0.734), (1.0, 0.10, 0.723),
                        (0.9, 0.05, 0.687), (0.9, 0.10, 0.676), (0.9, 0.20, 0.651)]:
    L = lam * l
    w = eta * L / 2
    t0 = time.time()
    d, trG, trG2, K = traces(gam, T, L, w, 1.0)
    a = a_const(L, w)
    trGt, trGt2 = trG / L, trG2 / L**2
    C = trG**2 / trG2
    rows.append((lam, eta, d, trGt, trGt2, C, C / NI))
    print(f"{lam:5.2f} {eta:5.2f} {L:8.4f} {np.exp(L):8.1f} {d:6d} {a:8.5f} "
          f"{trGt:11.3f} {trGt/(a*L):10.2f} {trGt2:12.3f} {C:10.3f} {C/NI:7.4f} "
          f"{paper:9.3f} {tapered_law(lam, eta):7.4f}   [{time.time()-t0:.1f}s]")

print()
print("paper trace-level targets:  lam=1.0,eta=0.05 -> C_zero=1436.41 ;"
      "  lam=0.9,eta=0.10 -> C_zero=1322.28")
print(f"ours:                       lam=1.0,eta=0.05 -> C     ={rows[0][5]:.2f} ;"
      f"  lam=0.9,eta=0.10 -> C     ={rows[3][5]:.2f}")

print()
print("Zero-set truncation sensitivity (lambda=1.0, eta=0.05, c=1):")
L, w = 1.0 * l, 0.05 * 1.0 * l / 2
for lo, hi, tag in [(1700.0, 4300.0, "gamma in [1700,4300]"),
                    (1900.0, 4100.0, "gamma in [1900,4100]"),
                    (1955.3, 4044.7, "gamma in I' (D0=44.7)"),
                    (0.0, 4218.3, "first 3700 (paper)"),
                    (0.0, 5541.0, "all 5100 in cache")]:
    sub = gam_all[(gam_all >= lo) & (gam_all <= hi)]
    d, trG, trG2, K = traces(sub, T, L, w, 1.0)
    print(f"  {tag:24s} n={sub.size:5d}  trGt={trG/L:11.3f}  C={trG**2/trG2:10.4f}  "
          f"C/N={trG**2/trG2/NI:.6f}")
