"""Euler-Maclaurin zeta and zeta', vectorised.
  zeta(s) = sum_{n<N} n^-s + N^-s/2 + N^{1-s}/(s-1) + sum_k B_2k/(2k)! (s)_{2k-1} N^{-s-2k+1}
differentiated analytically.  GATE against mpmath first."""
import numpy as np, mpmath as mp, sys, time, math
def P(*a): print(*a); sys.stdout.flush()
B=[1/6, -1/30, 1/42, -1/30, 5/66, -691/2730, 7/6]
def zz(s, N=None, K=7):
    s=np.atleast_1d(np.asarray(s,dtype=complex))
    if N is None: N=int(max(30, 2*np.abs(s.imag).max()))
    n=np.arange(1,N); ln=np.log(n)
    ns=np.power(n[None,:], -s[:,None])
    Z=ns.sum(1); Zp=(-ln[None,:]*ns).sum(1)
    lN=np.log(N)
    Z+= N**(-s)/2 + N**(1-s)/(s-1)
    Zp+= -lN*N**(-s)/2 + (-lN*N**(1-s)/(s-1) - N**(1-s)/(s-1)**2)
    for k in range(1,K+1):
        m=2*k-1
        poch=np.ones_like(s); dp=np.zeros_like(s)
        for j in range(m):
            poch=poch*(s+j)
        for j in range(m):
            dp=dp+1.0/(s+j)
        c=B[k-1]/math.factorial(2*k)
        term=c*poch*N**(-s-2*k+1)
        Z+=term
        Zp+=term*(dp - lN)
    return Z,Zp
mp.mp.dps=25
P("GATE: Euler-Maclaurin vs mpmath in 0 < sigma < 1/2")
P(f"  {'s':>20}{'rel err zeta':>15}{'rel err zeta-prime':>21}")
worst=0
for sig in (0.05,0.2,0.35,0.49):
    for t in (50.,200.,800.,3000.):
        z,zp=zz(complex(sig,t))
        zt=complex(mp.zeta(mp.mpc(sig,t))); zpt=complex(mp.diff(mp.zeta,mp.mpc(sig,t)))
        e1=abs(z[0]-zt)/abs(zt); e2=abs(zp[0]-zpt)/abs(zpt); worst=max(worst,e2)
        P(f"  {f'{sig}+{t:.0f}i':>20}{e1:>15.2e}{e2:>21.2e}")
P(f"  worst relative error: {worst:.2e}   -> {'GATE PASSED' if worst<1e-8 else 'GATE FAILED'}")
t0=time.time(); s=np.array([complex(0.25,t) for t in np.linspace(100,300,2000)])
zz(s); P(f"  speed: 2000 points at t~200 in {time.time()-t0:.2f}s")
