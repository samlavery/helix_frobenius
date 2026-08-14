"""RE-INDEX O_1 MULTIPLICATIVELY.

Lambda(n)Lambda(m) != 0 needs n,m prime powers.  Two prime powers have gcd>1 ONLY if
they are powers of the SAME prime.  So the pair sum splits EXACTLY:

    O_1 = O_same  (n=p^i, m=p^j, i!=j)  +  O_diff  (n=p^i, m=q^j, p!=q)

O_same is a FINITE, EXPLICITLY ENUMERABLE set -- no Hardy-Littlewood needed, ever.
Its pairs sit on log n - log m = (i-j) log p : the PRIME CLOCKS.

PRECHECK: if O_same is negligible, O_1 is essentially all different-prime and HL is
unavoidable.  If it carries real weight, that fraction of O_1 is unconditionally
computable.  Either outcome is informative; the instrument is the validated splitter.
"""
import time, numpy as np, sys
from zeta23_prime import prime_powers, R_amb
from zeta23_o1 import split

def P(*a): print(*a); sys.stdout.flush()

def same_prime_pairs(X):
    """all (p^i, p^j), i != j, both <= X, with their Lambda weights"""
    sieve=np.ones(int(X)+1,bool); sieve[:2]=False
    for i in range(2,int(X**0.5)+1):
        if sieve[i]: sieve[i*i::i]=False
    out=[]
    for p in np.nonzero(sieve)[0]:
        pw=[]; v=int(p)
        while v<=X: pw.append(v); v*=int(p)
        if len(pw)<2: continue
        for a in pw:
            for b in pw:
                if a!=b: out.append((a,b,float(np.log(p))))
    return out

def run(T, ETA, lam):
    l=np.log(T/(2*np.pi)); L=lam*l; w=ETA*L/2; X=np.exp(L)
    h=2*np.pi/L; d=int(np.floor(T/h)); tau=T+np.arange(d)*h
    lamv,u=prime_powers(X)
    _,_,D,O1,_,_=split(T,L,w,lamv,u)
    deltas=np.arange(-(d-1),d)*h
    idx=(np.arange(d)[:,None]-np.arange(d)[None,:])+(d-1)
    mbar=0.5*(tau[:,None]+tau[None,:])
    pairs=same_prime_pairs(X)
    t0=time.time(); Osame=0.0; cache={}
    for a,b,lp in pairs:
        for n in (a,b):
            if n not in cache: cache[n]=R_amb(np.log(n),deltas,L,w)
        ua,ub=np.log(a),np.log(b)
        Rm=cache[a][idx]*cache[b][idx]
        Osame+=2.0*(lp/np.sqrt(a))*(lp/np.sqrt(b))*float(np.sum(Rm*np.cos(mbar*(ua-ub))))
    P(f"  lam={lam:4.2f}  L={L:6.3f}  X={X:8.0f}  d={d:5d}  prime-power pairs(same)={len(pairs):5d}"
      f"  [{time.time()-t0:.0f}s]")
    P(f"        D/L^2      = {D/L**2:14.2f}")
    P(f"        O1/L^2     = {O1/L**2:14.2f}   (total off-diagonal)")
    P(f"        O_same/L^2 = {Osame/L**2:14.2f}   <- EXACTLY computable, no HL")
    P(f"        O_diff/L^2 = {(O1-Osame)/L**2:14.2f}   <- needs prime pairs")
    P(f"        O_same / O1 = {Osame/O1:7.2%}      |O_same|/D = {abs(Osame/D):.4f}")
    return Osame/O1

P("O_1 SPLIT BY gcd:  same-prime pairs vs different-prime pairs   (T=600, eta=0.01)")
fr=[]
for lam in (1.5,1.75,2.0):
    fr.append(run(600.0,0.01,lam))
P(f"\n  O_same as a fraction of O_1 across lam: " + ", ".join(f"{f:.2%}" for f in fr))
