# Corrected pair-bank probe: Phi evaluated as raw(|u|) (mode sum is positive-term
# and accurate for u>=0; evenness is structural, never numerical).
# Validation: xi ratio kernel/exact at two t (must be equal -> pipeline sane;
# value itself just fixes normalization, irrelevant to signs).
# CLAIM: A(p,t) = 2 Int Phi(u)Phi(p-u)cos(t(2u-p))du >= 0.
from mpmath import mp, mpf, exp, cos, pi, quad, gamma, zeta, mpc
mp.dps = 15
N = 90
def PhiRaw(u):
    s = mpf(0)
    for n in range(1, N+1):
        nn = n*n
        s += (2*pi**2*nn*nn*exp(9*u/2) - 3*pi*nn*exp(5*u/2))*exp(-pi*nn*exp(2*u))
    return 4*s
def Phi(u): return PhiRaw(abs(u))
for tv in [10, 14]:
    kern = quad(lambda u: Phi(u)*cos(tv*u), [-4, 0, 4])
    s0 = mpc(0.5, tv)
    exact = (s0*(s0-1)/2 * pi**(-s0/2) * gamma(s0/2) * zeta(s0)).real
    print(f"t={tv}: kernel/exact = {float(kern/exact):.10f}")
def A(p, t):
    c = p/2
    return 2*quad(lambda u: Phi(u)*Phi(p-u)*cos(t*(2*u-p)), [c-4, c, c+4])
print(f"{'p':>5} | A(p,t), t = 0, 5, 10, 15, 20, 25, 30, 35, 40")
worst = (mpf(1), None)
for pv in [0, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0]:
    row = []
    for tv in [0, 5, 10, 15, 20, 25, 30, 35, 40]:
        a = A(mpf(pv), mpf(tv))
        row.append(a)
        if a < worst[0]: worst = (a, (pv, tv))
    print(f"{pv:>5} | " + " ".join(f"{float(v):>10.3e}" for v in row))
print(f"min A = {float(worst[0]):.3e} at (p,t)={worst[1]}")
