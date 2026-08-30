# THE LAST-SLOT TEST (pre-registered in header, decision rules fixed before run).
# Question: is the radial sign  x * d/dx |F(x+it)|^2 > 0  produced by the ARITHMETIC
# coherence of Riemann's kernel (freqs pi*n^2, weights 1, Poisson-locked), or is it
# generic in the even-positive doubly-exponential class?
# Kernels (all symmetrized to even):
#   ZETA : phi_n with lambda_n = n^2, weights 1        (the genuine article)
#   JIT  : lambda_n = n^2*(1+0.15*j_n), j_n fixed jitter list (breaks lattice)
#   WGT  : lambda_n = n^2, mode weights w_n = 1+0.6*j_n (breaks Poisson weights)
#   G3   : 3-Gaussian countermodel (att551)             (violation POWER CONTROL)
# Decision rules: ZETA must hold sign at ALL grid pts (else pipeline suspect);
#   G3 must VIOLATE near (x,t)=(0.45,1.571) (else test underpowered);
#   verdict = "coherence-supported" iff >=1 of {JIT,WGT} violates; "falsified" iff
#   both hold everywhere.  Kernel positivity of JIT/WGT spot-checked; failures noted.
from mpmath import mp, mpf, mpc, exp, cos, sin, pi, quad, gamma, zeta, sqrt, j, cosh
mp.dps = 20
L = mpf('4.5')
N = 60
jit = [((17*k*k + 31*k + 7) % 101)/mpf(101) - mpf('0.5') for k in range(1, N+1)]  # fixed, in [-1/2,1/2)
def mode(lam, w, u):
    return w*(2*pi**2*lam**2*exp(9*u/2) - 3*pi*lam*exp(5*u/2))*exp(-pi*lam*exp(2*u))
def make_kernel(lams, ws):
    raw = lambda u: 4*sum(mode(lams[k], ws[k], u) for k in range(N))
    return lambda u: (raw(u) + raw(-u))/2
PHI = {
 'ZETA': make_kernel([mpf(n*n) for n in range(1,N+1)], [mpf(1)]*N),
 'JIT' : make_kernel([n*n*(1+mpf('0.15')*jit[n-1]) for n in range(1,N+1)], [mpf(1)]*N),
 'WGT' : make_kernel([mpf(n*n) for n in range(1,N+1)], [1+mpf('0.6')*jit[n-1] for n in range(N)]),
}
lam3, a3 = mpf('0.5'), mpf('2.0')
PHI['G3'] = lambda u: exp(-u**2/2) + (lam3/2)*(exp(-(u-a3)**2/2) + exp(-(u+a3)**2/2))
def F(phi, x, t):   return quad(lambda u: phi(u)*exp(x*u)*(cos(t*u)+j*sin(t*u)), [-L, 0, L])
def Fx(phi, x, t):  return quad(lambda u: u*phi(u)*exp(x*u)*(cos(t*u)+j*sin(t*u)), [-L, 0, L])
def signed_cross(phi, x, t):
    f, fx = F(phi, x, t), Fx(phi, x, t)
    return x * (f * fx.conjugate()).real
# --- pipeline validation: ZETA kernel vs exact xi at two points
def xi_exact(s): return s*(s-1)/2 * pi**(-s/2) * gamma(s/2) * zeta(s)
for (x, t) in [(mpf('0.3'), mpf(10)), (mpf('0.45'), mpf(25))]:
    kv = F(PHI['ZETA'], x, t)
    ev = xi_exact(mpf('0.5')+x + j*t)
    print(f"validate x={float(x)} t={float(t)}: |kernel - exact|/|exact| = {float(abs(kv-ev)/abs(ev)):.2e}")
# --- kernel positivity spot checks for scrambles
for name in ['JIT','WGT']:
    bad = [float(u) for u in [-3.5,-2,-1,-0.3,0,0.3,1,2,3.5] if PHI[name](mpf(u)) <= 0]
    print(f"{name} positivity: {'OK' if not bad else 'NEGATIVE at '+str(bad)}")
# --- the sign grid
xs = [mpf('0.1'), mpf('0.3'), mpf('0.45')]
ts = [mpf('1.571')] + [mpf(v) for v in range(2, 41, 2)]
print(f"{'kernel':>6} {'min of x*cross over grid':>26} {'argmin (x,t)':>16} {'violations':>11}")
for name, phi in PHI.items():
    worst, arg, nviol = None, None, 0
    for x in xs:
        for t in ts:
            v = signed_cross(phi, x, t)
            if v <= 0: nviol += 1
            if worst is None or v < worst: worst, arg = v, (float(x), float(t))
    print(f"{name:>6} {float(worst):>26.6e} {str(arg):>16} {nviol:>11}")
