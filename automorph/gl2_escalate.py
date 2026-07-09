import numpy as np, mpmath as mp
mp.mp.dps = 25
# GL(2) escalation: derive the Delta FE (weight 12, level 1) from MODULARITY (double-sided helix),
# no FE input.  tau(n) from eta^24; f(iy)=sum tau(n)e^{-2pi n y}; modularity f(i/y)=y^12 f(iy)
# gives Lambda(s)=int_1^inf f(iy)(y^{s-1}+y^{11-s})dy  =>  Lambda(s)=Lambda(12-s) manifestly.
N = 400
# Pi (1-q^n) via pentagonal, then ^24, then tau[n]=coeff q^{n-1}
P = np.zeros(N+1); P[0] = 1.0
for n in range(1, N+1):
    k = n
    # multiply current P by (1-q^k): P -= shift(P,k)
    P[k:] -= P[:N+1-k].copy()
# now P = Prod_{n=1}^{N}(1-q^n) truncated; raise to 24th via repeated convolution (trunc)
def cmul(a,b):
    return np.convolve(a,b)[:N+1]
E = P.copy(); base = P.copy(); e = 24; R = np.zeros(N+1); R[0]=1.0
while e:
    if e & 1: R = cmul(R, base)
    base = cmul(base, base); e >>= 1
tau = np.zeros(N+1)
tau[1:] = R[:N]          # tau[n] = coeff q^{n-1} in Prod(1-q^n)^24
print("  tau(1..6) =", tau[1:7], " (want 1, -24, 252, -1472, 4830, -6048)")
def f_iy(y):
    n = np.arange(1, N+1)
    return np.sum(tau[1:]*np.exp(-2*np.pi*n*y))
def Lam(s):  # Hecke: int_1^inf f(iy)(y^{s-1}+y^{11-s}) dy   (no FE input; uses modularity split)
    return mp.quad(lambda y: f_iy(float(y))*(y**(s-1)+y**(11-s)), [1, mp.inf])
for s in [mp.mpf(6)+2j, mp.mpf(7)+1j, mp.mpf('5.5')]:
    L, L2 = Lam(s), Lam(12-s)
    print(f"  Delta: Lambda({mp.nstr(s,4)}) - Lambda(12-s) = {mp.nstr(L-L2,3)}   (GL(2) FE derived from modularity, no FE input)")
