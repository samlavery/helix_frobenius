"""THE question: does sup_x M_c(x) saturate as Y -> inf (rails added)?
M_c has convergent mean (c=2 > c*); sup measured per Y at decade 1e12."""
import numpy as np, math
def primes_to(m):
    s=np.ones(m+1,bool); s[:2]=False
    for i in range(2,int(m**.5)+1):
        if s[i]: s[i*i::i]=False
    return [int(q) for q in np.nonzero(s)[0]]
c=2.0
rng=np.random.default_rng(381)
lo=10**12
def M(xv,P,J):
    m=0.0
    for p in P:
        pk=p; d=1
        while pk*p<=xv: pk*=p; d+=1
        Jp=min(J[p],d); q=xv//(pk//p**(Jp-1)); ok=True
        for _ in range(Jp):
            if 2*(q%p)>=p: ok=False; break
            q//=p
        if ok: m+=1.0/p
    return m
XS=[int(x) for x in rng.integers(lo,10*lo,25000)]
base=[3,5,7,11,13,17,19]
SM=[]
for _ in range(3000):
    S=1
    for p in rng.permutation(base):
        while S*p<lo and rng.random()<0.6: S*=int(p)
    for mult in (1,2,3,5):
        x=S*mult
        while x<lo: x*=2
        if x<10*lo: SM.append(x)
for Y in (200,1000,5000,20000):
    P=[p for p in primes_to(Y) if p>=3]
    J={p:max(1,int(c*math.log(math.log(p+2)))) for p in P}
    best=0.0; bx=0; tot=0.0
    for xv in XS[:12000]+SM:
        v=M(xv,P,J)
        tot+=v
        if v>best: best,bx=v,xv
    print(f"Y={Y:>6}: sup M ~ {best:.4f}  (mean ~ {tot/(12000+len(SM)):.4f})  at {bx}")
