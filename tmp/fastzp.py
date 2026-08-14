"""Fast zeta and zeta' in the strip via the approximate functional equation.
   zeta(s)  = sum_{n<=N} n^-s + chi(s) sum_{n<=N} n^{s-1} + err
   zeta'(s) = -sum log(n) n^-s + chi'(s) sum n^{s-1} + chi(s) sum log(n) n^{s-1} + err
   chi(s) = 2^s pi^{s-1} sin(pi s/2) Gamma(1-s),   chi'/chi = log(2pi) + (pi/2)cot(pi s/2) - psi(1-s)
GATE against mpmath before any use."""
import numpy as np
from scipy.special import loggamma, digamma
import mpmath as mp, sys
def P(*a): print(*a); sys.stdout.flush()

def chi_and_dchi(s):
    lg = np.log(2)*s + (s-1)*np.log(np.pi) + np.log(np.sin(np.pi*s/2)+0j) + loggamma(1-s)
    chi = np.exp(lg)
    dlog = np.log(2*np.pi) + (np.pi/2)/np.tan(np.pi*s/2) - digamma(1-s)
    return chi, chi*dlog

def zeta_zp(s):
    s=np.atleast_1d(np.asarray(s,dtype=complex))
    t=np.abs(s.imag); N=np.floor(np.sqrt(t/(2*np.pi))).astype(int)
    Z=np.zeros(s.shape,dtype=complex); Zp=np.zeros(s.shape,dtype=complex)
    A=np.zeros(s.shape,dtype=complex); Ap=np.zeros(s.shape,dtype=complex)
    for n in range(1,int(N.max())+1):
        m=N>=n; ln=np.log(n)
        Z[m]+=np.power(n,-s[m]); Zp[m]+=-ln*np.power(n,-s[m])
        A[m]+=np.power(n,s[m]-1); Ap[m]+=ln*np.power(n,s[m]-1)
    chi,dchi=chi_and_dchi(s)
    return Z+chi*A, Zp+dchi*A+chi*Ap

mp.mp.dps=25
P("GATE: approximate functional equation vs mpmath, in 0 < sigma < 1/2")
P(f"  {'s':>22}{'|zeta err|':>13}{'|zeta-prime err|':>19}")
worst=0
for sig in (0.05,0.2,0.35,0.49):
    for t in (50.,200.,800.,3000.):
        s=complex(sig,t)
        z,zp=zeta_zp(s); z=z[0]; zp=zp[0]
        zt=complex(mp.zeta(mp.mpc(sig,t))); zpt=complex(mp.diff(mp.zeta,mp.mpc(sig,t)))
        e1=abs(z-zt); e2=abs(zp-zpt); worst=max(worst,e2/max(abs(zpt),1e-30))
        P(f"  {f'{sig}+{t:.0f}i':>22}{e1:>13.2e}{e2:>19.2e}")
P(f"  worst RELATIVE error in zeta-prime: {worst:.2e}")
P(f"  -> {'GATE PASSED' if worst<0.05 else 'GATE FAILED'}")
