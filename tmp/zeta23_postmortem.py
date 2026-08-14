"""POST-MORTEM on the harmonization null.  Rule out instrument failure before any verdict.

PM1  second/third heights (T=1000, T=2500) - is T=2000 special?
PM2  truncation tail, quantified against the diagonal
PM3  normalization stability: C, C/N, C/d, trGt/N -- and does the C/d optimum sit at pi/3
     for a structural reason, or does it move with the taper?
PM4  precision: cancellation amplification, mpmath ground truth on a reduced problem,
     sensitivity to the 5e-11 uncertainty in the cached zero ordinates
PM5  narrow-feature search: ultra-fine sweeps at every harmonic value
"""
import numpy as np
import mpmath as mp
from zeta23_bench import phihat, phi, a_const, load_zeros, traces, rvm
from zeta23_controls import traces_ext

GAM = load_zeros()
np.random.seed(20260811)


def setup(T, lam=1.0, eta=0.05):
    l = np.log(T / (2 * np.pi))
    L = lam * l
    return l, L, eta * L / 2, T * (l + 2 * np.log(2) - 1) / (2 * np.pi)


# ------------------------------------------------------------------ PM1
print("=" * 90)
print("PM1. OTHER HEIGHTS (same taper eta=0.05, lambda=1). Is T=2000 special?")
print("=" * 90)
print(f"{'T':>6} {'l':>7} {'L':>7} {'d':>6} {'N(I)':>8} {'nzeros':>7} "
      f"{'C':>10} {'C/N':>8} | plateau over c in {{1/3,1/2,2/3,3/pi,1}}")
for T in [1000.0, 2000.0, 2500.0]:
    l, L, w, NI = setup(T)
    g = GAM[(GAM >= T - 300) & (GAM <= 2 * T + 300)]
    vals = []
    for c in [1 / 3, 0.5, 2 / 3, 3 / np.pi, 1.0]:
        d, t1, t2, _ = traces(g, T, L, w, c)
        vals.append((d, t1**2 / t2))
    C1 = vals[-1][1]
    sp = np.ptp([v[1] / NI for v in vals])
    print(f"{T:6.0f} {l:7.4f} {L:7.4f} {vals[-1][0]:6d} {NI:8.1f} {g.size:7d} "
          f"{C1:10.3f} {C1/NI:8.5f} | " +
          " ".join(f"{v[1]/NI:.5f}" for v in vals) + f"  spread={sp:.1e}")

# ------------------------------------------------------------------ PM2
print()
print("=" * 90)
print("PM2. TRUNCATION TAIL, quantified (T=2000, lambda=1, eta=0.05, c=1)")
print("=" * 90)
T = 2000.0
l, L, w, NI = setup(T)
full = GAM[GAM <= 5540.7]
d0, trG_full, trG2_full, _ = traces(full, T, L, w, 1.0)
print(f"  reference: ALL {full.size} cached zeros (gamma<=5540.7)  "
      f"trG={trG_full:.6f}  C={trG_full**2/trG2_full:.6f}")
for lo, hi in [(1700., 4300.), (1900., 4100.), (1955.3, 4044.7), (0., 4218.3)]:
    sub = GAM[(GAM >= lo) & (GAM <= hi)]
    d, t1, t2, _ = traces(sub, T, L, w, 1.0)
    print(f"  gamma in [{lo:7.1f},{hi:7.1f}] n={sub.size:5d}  "
          f"dropped trG frac = {(trG_full-t1)/trG_full:9.2e}   "
          f"dC/C = {(t1**2/t2 - trG_full**2/trG2_full)/(trG_full**2/trG2_full):+9.2e}")
# what the excluded bands actually carry
for lo, hi, tag in [(4300., 5540.7, "4300 < gamma <= 5540 (have data)"),
                    (14., 1700., "gamma < 1700 (have data)")]:
    sub = GAM[(GAM >= lo) & (GAM <= hi)]
    d, t1, t2, _ = traces(sub, T, L, w, 1.0)
    print(f"  band {tag:34s} n={sub.size:5d}  trG={t1:.4e}  "
          f"= {t1/trG_full:.2e} of diagonal")
# analytic bound for gamma > 5540 and for the negative-ordinate zeros
c_rho = 4 * 2.0 + 4 * 4.0            # 4||rho'||_inf + 4||rho''||_1 = 24
h = 2 * np.pi / L


def tail_bound(D):
    """sum over zeros beyond distance D of sum_k phihat^2, using |phihat(r)|<=c_rho/(w r^2)
    and zero density log(g/2pi)/2pi."""
    r = np.linspace(D, 5e6, 2000000)
    dens = np.log(r / (2 * np.pi)) / (2 * np.pi)
    per_zero = (2.0 / h) * (c_rho / (w * r**2))**2 * r / 3.0   # ~ int_r^inf psi^2 /h
    return np.trapezoid(dens * (c_rho / (w * r**2))**2 * (1.0 / h) * r, r) * 0 + \
        np.trapezoid(dens * (2.0 / h) * (c_rho**2 / (w**2 * 3 * r**3)), r)


print(f"  ANALYTIC tail, gamma > 5540 (distance >= {5540.7-4000:.0f}): "
      f"<= {tail_bound(5540.7-4000.0):.2e}  (= {tail_bound(5540.7-4000.)/trG_full:.2e} of diagonal)")
print(f"  ANALYTIC tail, NEGATIVE ordinates (distance >= {2000+14:.0f}):  "
      f"<= {tail_bound(2014.0):.2e}  (= {tail_bound(2014.)/trG_full:.2e} of diagonal)")

# ------------------------------------------------------------------ PM3
print()
print("=" * 90)
print("PM3. NORMALIZATION STABILITY, and: does the C/d optimum track pi/3?")
print("=" * 90)
gam = GAM[(GAM >= 1700.) & (GAM <= 4300.)]
print("  Is the verdict stable across normalizations?  (T=2000, lam=1, eta=0.05)")
print(f"  {'c':>8} {'C':>10} {'C/N':>9} {'C/d':>9} {'trGt/N':>9} {'cert':>8}")
NIp = ((2*T+44.7)/(2*np.pi)*(np.log((2*T+44.7)/(2*np.pi))-1)
       - (T-44.7)/(2*np.pi)*(np.log((T-44.7)/(2*np.pi))-1))
for c in [1/3, 0.5, 2/3, 3/np.pi, 1.0, np.pi/3, 4/3, 2.0]:
    d, t1, t2, _ = traces(gam, T, L, w, c)
    C = t1**2/t2
    print(f"  {c:8.4f} {C:10.3f} {C/NI:9.5f} {C/d:9.5f} {t1/L/NI:9.4f} "
          f"{(2*C-NIp)/NI:8.4f}")
print()
print("  C/d peaks just past c=1.  If that optimum is at pi/3 for a STRUCTURAL reason it")
print("  must not move with the taper width eta or with lambda.  Locating it:")
print(f"  {'lam':>5} {'eta':>5} {'argmax_c C/d':>13} {'max C/d':>9}  pi/3 = 1.0472")
for lam in [0.9, 1.0]:
    for eta in [0.02, 0.05, 0.10, 0.20]:
        l2, L2, w2, _ = setup(T, lam, eta)
        cs = np.arange(1.00, 1.201, 0.005)
        cd = []
        for c in cs:
            d, t1, t2, _ = traces(gam, T, L2, w2, c)
            cd.append(t1**2/t2/d)
        cd = np.array(cd)
        print(f"  {lam:5.2f} {eta:5.2f} {cs[cd.argmax()]:13.4f} {cd.max():9.5f}")
