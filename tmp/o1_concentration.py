"""Does O_1 concentrate on SMALL primes the way S(t) does?
If yes, the Hardy-Littlewood input needed for lambda>1 is FINITE, not asymptotic.
Uses the validated splitter (gate: EXACT weights must reproduce measured O_1)."""
import numpy as np, time, sys
from zeta23_prime import prime_powers, R_amb
from zeta23_o1 import split
def P(*a): print(*a); sys.stdout.flush()

T,ETA,lam = 600.0, 0.01, 2.0
l=np.log(T/(2*np.pi)); L=lam*l; w=ETA*L/2; X=np.exp(L)
h=2*np.pi/L; d=int(np.floor(T/h)); tau=T+np.arange(d)*h
lamv,u=prime_powers(X)
_,_,D,O1,_,_=split(T,L,w,lamv,u)
P(f"T={T} lam={lam} L={L:.3f} X={X:.0f} d={d}")
P(f"  measured D/L^2 = {D/L**2:.2f}   O1/L^2 = {O1/L**2:.2f}\n")

deltas=np.arange(-(d-1),d)*h
idx=(np.arange(d)[:,None]-np.arange(d)[None,:])+(d-1)
mbar=0.5*(tau[:,None]+tau[None,:])
keep=u<L
lamk=lamv[keep]; uk=u[keep]; nk=np.rint(np.exp(uk)).astype(int)
a=lamk*np.exp(-0.5*uk)
Rcache={}
def Rof(i):
    if i not in Rcache: Rcache[i]=R_amb(uk[i],deltas,L,w)
    return Rcache[i]
# base prime of each prime power
def basep(n):
    p=2
    while p*p<=n:
        if n%p==0: return p
        p+=1
    return n
bp=np.array([basep(int(x)) for x in nk])
P("O_1 restricted to pairs with BOTH primes <= P  (cumulative):")
P(f"  {'P':>8}{'#terms':>8}{'O1(P)/L^2':>14}{'frac of full O1':>18}{'[s]':>7}")
full=O1/L**2
for Pcut in (3,5,7,11,20,50,100,300,1000,int(X)+1):
    t0=time.time()
    sel=np.nonzero(bp<=Pcut)[0]
    tot=0.0
    for ii in range(len(sel)):
        i=sel[ii]; Ri=Rof(i)
        for jj in range(len(sel)):
            j=sel[jj]
            if i==j: continue
            Rm=Ri[idx]*Rof(j)[idx]
            tot+=a[i]*a[j]*float(np.sum(Rm*np.cos(mbar*(uk[i]-uk[j]))))
    P(f"  {Pcut:>8}{len(sel):>8}{tot/L**2:>14.2f}{tot/L**2/full:>18.4f}{time.time()-t0:>7.0f}")
    if len(sel)>260: break
