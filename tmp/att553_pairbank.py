# PROOF-FIRST on the actual model.  Exact decomposition (derived, this session):
#   x*Re(xi.conj(xi'))(1/2+x+it) = (1/2) Int_0^inf p*x*sinh(xp)*A(p,t) dp,
#   A(p,t) = 2 Int Phi(u) Phi(p-u) cos(t(2u-p)) du,   x*sinh(xp) >= 0 always.
# CLAIM UNDER TEST (the candidate last slot, stronger-and-constructive):
#   A(p,t) >= 0 for all p >= 0, t   (pair-bank positivity at fixed total height).
# Pre-registered: A >= -1e-12 (rel) at all grid points => adopt as the last-slot
# claim and proceed to PROVE it; any robust A < 0 => record where, keep the signed
# integral form.  Validation: Phi evenness + kernel-vs-exact xi at t=10.
from mpmath import mp, mpf, exp, cos, pi, quad, gamma, zeta, mpc, j
mp.dps = 15
N = 90
def Phi(u):
    s = mpf(0)
    for n in range(1, N+1):
        nn = n*n
        s += (2*pi**2*nn*nn*exp(9*u/2) - 3*pi*nn*exp(5*u/2))*exp(-pi*nn*exp(2*u))
    return 4*s
# validations
ev = abs(Phi(mpf(-2))/Phi(mpf(2)) - 1)
xi_kernel = quad(lambda u: Phi(u)*cos(10*u), [-4, 0, 4])
s0 = mpc(0.5, 10)
xi_exact = (s0*(s0-1)/2 * pi**(-s0/2) * gamma(s0/2) * zeta(s0)).real
print(f"Phi evenness |Phi(-2)/Phi(2)-1| = {float(ev):.2e}")
print(f"xi(1/2+10i): kernel {float(xi_kernel):.10e} exact {float(xi_exact):.10e}")
def A(p, t):
    c = p/2
    return 2*quad(lambda u: Phi(u)*Phi(p-u)*cos(t*(2*u-p)), [c-4, c, c+4])
print(f"{'p':>5} | A(p,t) for t = 0, 5, 10, 15, 20, 25, 30")
worst = (mpf(1), None)
Anorm = A(mpf(0), mpf(0))
for pv in [0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 4.0]:
    row = []
    for tv in [0, 5, 10, 15, 20, 25, 30]:
        a = A(mpf(pv), mpf(tv))
        row.append(a)
        if a < worst[0]: worst = (a, (pv, tv))
    print(f"{pv:>5} | " + " ".join(f"{float(v):>10.3e}" for v in row))
print(f"min A over grid = {float(worst[0]):.3e} at (p,t)={worst[1]};  A(0,0) = {float(Anorm):.3e}")
print("VERDICT:", "A >= 0 on grid -> adopt pair-bank positivity as last-slot claim"
      if worst[0] > -mpf('1e-12')*Anorm else "A < 0 found -> record location, keep signed form")
