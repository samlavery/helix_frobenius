"""STEP 2c -- the OTHER lever.  The zero side of G needs no primes, so C/N is
computable for any lambda, including lambda > 1 where the paper's prime-side
evaluation (Prop 5.6 / sec 7.5(a)) stops.  This measures what the lambda<=1 wall costs,
and checks that the c-plateau is lambda-independent (the two levers are orthogonal).

Predicted law (Montgomery pair correlation, sharp cutoff): F(lambda)=lambda/(1+lambda^2/3),
maximised at lambda=sqrt(3) with F=sqrt(3)/2.
"""
import numpy as np
from zeta23_bench import a_const, b_const, load_zeros, traces

T = 2000.0
l = np.log(T / (2 * np.pi))
l1 = l + 2 * np.log(2) - 1
NI = T * l1 / (2 * np.pi)
NIp = ((2*T+44.7)/(2*np.pi)*(np.log((2*T+44.7)/(2*np.pi))-1)
       - (T-44.7)/(2*np.pi)*(np.log((T-44.7)/(2*np.pi))-1))
ETA = 0.05
gam_all = load_zeros()
gam_win = gam_all[(gam_all >= 1500.0) & (gam_all <= 4500.0)]


def F(lam):
    return lam / (1 + lam**2 / 3)


def tapered(lam, eta):
    J = 1/3 - (0.60 - 0.35*eta)*eta
    L = lam*l; w = eta*L/2
    return lam*a_const(L, w)**2/(b_const(L, w) + lam**2*J)


print(f"T={T}  eta={ETA}  N(I)={NI:.1f}   zeros in [1500,4500]: {gam_win.size}")
print("(2C - N(I'))/N(I) is the Prop 4.4(ii) certificate; the paper reads +0.42 at lambda=1")
print()
print(f"{'lam':>6} {'L':>7} {'X=e^L':>10} {'d':>6} {'C':>10} {'C/N':>8} {'F(lam)':>8} "
      f"{'tapered':>8} {'cert':>7} {'c-flat?':>28}")
for lam in [0.5, 0.7, 0.9, 1.0, 1.2, 1.5, np.sqrt(3), 2.0, 2.5, 3.0]:
    L = lam*l; w = ETA*L/2
    d, trG, trG2, _ = traces(gam_win, T, L, w, 1.0)
    C = trG**2/trG2
    # c-flatness at this lambda: spread of C/N over c in {1/2, 2/3, 3/pi, 1}
    vals = []
    for c in [0.5, 2/3, 3/np.pi, 1.0]:
        dd, g1, g2, _ = traces(gam_win, T, L, w, c)
        vals.append(g1**2/g2/NI)
    flat = f"{min(vals):.5f}..{max(vals):.5f} (sp {np.ptp(vals):.1e})"
    print(f"{lam:6.3f} {L:7.3f} {np.exp(L):10.1f} {d:6d} {C:10.3f} {C/NI:8.5f} "
          f"{F(lam):8.5f} {tapered(lam,ETA):8.5f} {(2*C-NIp)/NI:7.4f} {flat:>28}")

print()
print("zero-set adequacy check at the largest lambda (reach grows with L):")
for lam in [2.0, 3.0]:
    L = lam*l; w = ETA*L/2
    for lo, hi in [(1500., 4500.), (1000., 5000.), (0., 5541.)]:
        sub = gam_all[(gam_all >= lo) & (gam_all <= hi)]
        d, trG, trG2, _ = traces(sub, T, L, w, 1.0)
        print(f"  lam={lam}  zeros in [{lo:.0f},{hi:.0f}] n={sub.size:5d}  "
              f"C={trG**2/trG2:10.4f}  C/N={trG**2/trG2/NI:.6f}")
