"""Discriminate sup-mean: 1/3 (0.33333) vs pi/9 (0.34907) vs c-dependent.
Hill-climb extremal search + c-variation."""
import numpy as np, math, random
def primes_to(m):
    s=np.ones(m+1,bool); s[:2]=False
    for i in range(2,int(m**.5)+1):
        if s[i]: s[i*i::i]=False
    return [int(q) for q in np.nonzero(s)[0]]
PALL=[p for p in primes_to(20000) if p>=3]
def make(c):
    J={p:max(1,int(c*math.log(math.log(p+2)))) for p in PALL}
    def M(xv):
        m=0.0
        for p in PALL:
            pk=p; d=1
            while pk*p<=xv: pk*=p; d+=1
            Jp=min(J[p],d); q=xv//(pk//p**(Jp-1)); ok=True
            for _ in range(Jp):
                if 2*(q%p)>=p: ok=False; break
                q//=p
            if ok: m+=1.0/p
        return m
    return M,J
rng=np.random.default_rng(500)
lo=10**12
for c in (1.6, 2.0, 2.6):
    M,J=make(c)
    # mean via sampling
    mean=np.mean([M(int(x)) for x in rng.integers(lo,10*lo,4000)])
    # extremal: greedy digit construction + local search
    best=0.0; bx=0
    for x0 in list(rng.integers(lo,10*lo,3000)):
        x=int(x0); v=M(x)
        for _ in range(60):   # hill-climb: try aligning one more small rail via CRT nudge
            p=random.choice([3,3,3,5,5,7,11,13,17,19,23])
            pk=p; d=1
            while pk*p<=x: pk*=p; d+=1
            Jp=min(J[p],d); s=pk//p**(Jp-1)
            # nudge x to nearest point with rail p's top-Jp digits all zero-ish (lower-half mid)
            q=x//s
            tgt=0
            qq=q
            for t in range(Jp):
                dig=min((p-1)//2//2, p-1)
                tgt+=dig*p**t
                qq//=p
            xn=(q - q% p**Jp + tgt)*s + x%s
            if lo<=xn<10*lo:
                vn=M(xn)
                if vn>v: x,v=xn,vn
        if v>best: best,bx=v,x
    print(f"c={c}: mean~{mean:.4f}  extremal sup~{best:.4f}  EXCESS={best-mean:.4f}   (1/3={1/3:.4f}, pi/9={math.pi/9:.4f})")
