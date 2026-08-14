"""Character orthogonality kills off-diagonal terms with n != m mod q.
So the family-averaged O_1 keeps ONLY shifts h = n-m divisible by q.
Measure how fast O_1 dies as we drop shifts not divisible by q.
If it dies fast, the lambda<=1 wall dissolves for FAMILIES -- the paper's
own unfinished Theorem E extension."""
import numpy as np, time, sys
from zeta23_bench import phihat
from zeta23_prime import prime_powers, R_amb
from zeta23_hl import R_all_integers, E_all, O1_model
def P(*a): print(*a); sys.stdout.flush()

T,ETA,lam=600.0,0.01,2.0
l=np.log(T/(2*np.pi)); L=lam*l; w=ETA*L/2
X=int(np.exp(L)); h=2*np.pi/L; d=int(np.floor(T/h))
lamv,u=prime_powers(float(X))
cn=np.zeros(X)
keep=u<np.log(X+1); idx=np.rint(np.exp(u[keep])).astype(int)
ok=(idx>=1)&(idx<=X); cn[idx[ok]-1]=lamv[keep][ok]/np.sqrt(idx[ok])
Rt=R_all_integers(X,L,w,d,h)
HMAX=200
P(f"T={T} lam={lam} L={L:.3f} X={X} d={d}  shifts to h<={HMAX}\n")
full,_=O1_model(T,L,w,lambda hh:1.0,cn,X,d,Rt,HMAX)
P(f"  full O_1 (all shifts)         = {full:14.2f}")
P(f"\n  family average over chi mod q keeps ONLY h = 0 mod q:")
P(f"  {'q':>6}{'kept shifts':>13}{'O_1 restricted':>17}{'fraction':>12}")
for q in (1,2,3,5,7,11,20,50,100,200):
    val,_=O1_model(T,L,w,lambda hh,q=q: 1.0 if hh%q==0 else 0.0,cn,X,d,Rt,HMAX)
    nk=len([hh for hh in range(1,HMAX+1) if hh%q==0])
    P(f"  {q:>6}{nk:>13}{val:>17.2f}{val/full:>12.4f}")
P(f"\n  -> if the fraction falls like ~1/q, the averaged off-diagonal is O(1/q) of the")
P(f"     single-function one, and q -> infinity removes it entirely.")
