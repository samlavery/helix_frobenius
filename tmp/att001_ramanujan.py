"""ATTEMPT 1: Ramanujan sums x divisor-class coherence.
   S(h) = sum_q (mu(q)/phi(q))^2 c_q(h)      [verified 14/14 today]
   => O_1 ~ 4 sum_q (mu/phi)^2 * [ sum_h c_q(h) K(h) ]
   c_q(h) depends only on gcd(h,q): the inner sum is divisor-class grouped.
NULL: q-sum needs Q ~ Hmax (200) to match M2 -> no gain, HL input still asymptotic.
HIT : q-sum truncates at small Q -> the needed HL input is FINITE."""
import numpy as np, time, sys
from math import gcd
from sympy import mobius, totient
from zeta23_prime import prime_powers
from zeta23_hl import R_all_integers, O1_model
def P(*a): print(*a); sys.stdout.flush()

T,ETA,lam=600.0,0.01,2.0
l=np.log(T/(2*np.pi)); L=lam*l; w=ETA*L/2
X=int(np.exp(L)); h=2*np.pi/L; d=int(np.floor(T/h))
lamv,u=prime_powers(float(X))
cn=np.zeros(X); keep=u<np.log(X+1)
idx=np.rint(np.exp(u[keep])).astype(int); ok=(idx>=1)&(idx<=X)
cn[idx[ok]-1]=lamv[keep][ok]/np.sqrt(idx[ok])
Rt=R_all_integers(X,L,w,d,h)
HMAX=200
C2=0.6601618158468696
def Sser(hh):
    if hh%2: return 0.0
    f=1.0; m=hh
    p=3
    while p*p<=m:
        if m%p==0:
            f*=(p-1)/(p-2)
            while m%p==0: m//=p
        p+=2
    if m>2: f*=(m-1)/(m-2)
    return 2*C2*f
def cq(q,hh):
    g=gcd(q,hh)
    return float(sum(dd*mobius(q//dd) for dd in range(1,g+1) if g%dd==0 and q%dd==0))

# GATE: full HL model M2
M2,_=O1_model(T,L,w,Sser,cn,X,d,Rt,HMAX)
P(f"GATE  M2 (full singular series) = {M2:14.2f}")
P(f"\n  {'Q':>5}{'partial sum over q<=Q':>26}{'ratio to M2':>14}{'[s]':>7}")
tot=0.0; t0=time.time(); prev=None
for Q in (1,2,3,5,10,20,40,80,150,300):
    acc=0.0
    for q in range(1,Q+1):
        mu=int(mobius(q))
        if mu==0: continue
        wgt=(mu/float(totient(q)))**2
        if abs(wgt)<1e-14: continue
        val,_=O1_model(T,L,w,lambda hh,q=q: cq(q,hh),cn,X,d,Rt,HMAX)
        acc+=wgt*val
    P(f"  {Q:>5}{acc:>26.2f}{acc/M2:>14.4f}{time.time()-t0:>7.0f}")
