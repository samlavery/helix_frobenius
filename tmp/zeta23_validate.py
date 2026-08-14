"""Pipeline validation: zeros, phihat, Lemma 2.2 (Poisson for the Gabor system)."""
import numpy as np
from scipy.integrate import quad
import mpmath as mp
from zeta23_bench import phi, phihat, a_const, b_const, load_zeros, rvm

mp.mp.dps = 20
np.set_printoptions(precision=12)

print("=" * 78)
print("V1. zero cache vs mpmath.zetazero")
print("=" * 78)
gam = load_zeros()
print(f"cache: {gam.size} zeros, gamma_1 = {gam[0]:.10f}, gamma_last = {gam[-1]:.6f}")
for n in [1, 2, 3, 100, 1000, 2500, 3700, gam.size]:
    ref = float(mp.im(mp.zetazero(n)))
    print(f"  n={n:5d}  cache={gam[n-1]:.10f}  mpmath={ref:.10f}  diff={gam[n-1]-ref:+.3e}")
# completeness: count vs Riemann-von Mangoldt (+7/8)
for t in [1000.0, 2000.0, 4000.0, 5000.0]:
    cnt = int(np.sum(gam < t))
    print(f"  #zeros < {t:7.0f}: cache={cnt:6d}  RvM main+7/8={rvm(t)+0.875:9.2f}")

print()
print("=" * 78)
print("V2. phihat closed form vs numerical quadrature")
print("=" * 78)
T = 2000.0
l = np.log(T / (2 * np.pi))
for lam, eta in [(1.0, 0.05), (0.9, 0.10)]:
    L = lam * l
    w = eta * L / 2
    print(f"  lambda={lam} eta={eta}: L={L:.6f} w={w:.6f}")
    worst = 0.0
    for r in [0.0, 1e-9, 0.3, 1.0, 2 * np.pi / w, 2 * np.pi / w + 1e-6, 5.0, 17.3, 44.7, 300.0, 1985.9]:
        num = quad(lambda u: phi(u, L, w) * np.cos(r * u), -L / 2, L / 2,
                   limit=400, epsabs=1e-14, epsrel=1e-13)[0]
        cf = float(phihat(r, L, w))
        worst = max(worst, abs(cf - num))
        print(f"    r={r:12.6f}  closed={cf:+.12e}  quad={num:+.12e}  diff={cf-num:+.2e}")
    print(f"    worst abs diff = {worst:.2e}")
    # a, b constants vs paper's a = 1-0.603 eta, b = 1-0.688 eta
    aa, bb = a_const(L, w), b_const(L, w)
    print(f"    a={aa:.6f} (paper 1-0.603*eta={1-0.603*eta:.6f})   "
          f"b={bb:.6f} (paper 1-0.688*eta={1-0.688*eta:.6f})")
    # phihat(0) should be int phi = L - 2w(1-int rho) ; and (1/2pi) int phihat^2 = int phi^2 = a L
    print(f"    phihat(0)={float(phihat(0.0,L,w)):.6f}   L-2w*(1-int rho)="
          f"{L-2*w*(1-0.5):.6f}   a*L={aa*L:.6f}")

print()
print("=" * 78)
print("V3. Lemma 2.2  sum_k phihat(tau-tau_k)^2 = a L^2   (and the 1/c law for c<1)")
print("=" * 78)
lam, eta = 1.0, 0.05
L = lam * l
w = eta * L / 2
aL2 = a_const(L, w) * L**2
KMAX = 400000
for c in [0.25, 0.5, 1 / np.pi * 3, 1.0, np.pi / 3, 1.25, 1.5, 2.0]:
    h = c * 2 * np.pi / L
    k = np.arange(-KMAX, KMAX + 1, dtype=np.float64)
    vals = []
    for tau_off in [0.0, 0.137, 0.5 * h, 0.83 * h]:
        tau = T + tau_off
        s = float(np.sum(phihat(tau - (T + k * h), L, w) ** 2))
        vals.append(s)
    vals = np.array(vals)
    pred = aL2 / c
    print(f"  c={c:7.4f}  sum={vals.mean():12.6f} (spread {np.ptp(vals):.3e})  "
          f"a L^2/c={pred:12.6f}  ratio={vals.mean()/pred:.9f}")
print("  (exact ratio 1 for c<=1 = no aliasing; departure for c>1 is the aliasing signal)")
