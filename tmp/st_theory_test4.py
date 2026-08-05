"""Slaving test with exact integer depths and manual regression (crash guard)."""
import numpy as np, math
def primes_to(m):
    s=np.ones(m+1,bool); s[:2]=False
    for i in range(2,int(m**.5)+1):
        if s[i]: s[i*i::i]=False
    return [int(q) for q in np.nonzero(s)[0]]
P=[p for p in primes_to(2000) if p>=3]
c=2.0
J={p:max(1,int(c*math.log(math.log(p+2)))) for p in P}
rng=np.random.default_rng(379)
K=15000
u=np.sort(rng.uniform(math.log(1e6), math.log(9e17), K))
xs=np.exp(u).astype(np.int64)
M=np.zeros(K); M1=np.zeros(K)
for k in range(K):
    xv=int(xs[k]); m=0.0; m1=0.0
    for p in P:
        pk=p; d=1
        while pk*p<=xv: pk*=p; d+=1      # pk = p^d <= xv < p^{d+1}? ensure top scale
        # top digit at scale pk: td = xv // pk in [1, p)
        td=xv//pk
        if 2*td < p: m1+=1.0/p           # lower-half top digit (strict half)
        Jp=min(J[p],d)
        q=xv//(pk//p**(Jp-1)) if Jp>=1 else xv
        ok=True
        qq=q
        for _ in range(Jp):
            if 2*(qq%p) >= p: ok=False; break
            qq//=p
        if ok: m+=1.0/p
    M[k]=m; M1[k]=m1
mM,m1M=M.mean(),M1.mean()
cov=((M-mM)*(M1-m1M)).mean(); v1=((M1-m1M)**2).mean(); vM=((M-mM)**2).mean()
r=cov/math.sqrt(v1*vM) if v1>0 and vM>0 else float('nan')
beta=cov/v1 if v1>0 else 0
res=M-mM-beta*(M1-m1M)
du=np.diff(u,prepend=u[0]); T=u[-1]-u[0]
D=np.cumsum((M-mM)*du); Dr=np.cumsum(res*du)
print(f"K={K} T={T:.1f}: mean={mM:.4f} sup={M.max():.4f} sd={math.sqrt(vM):.4f}")
print(f"max|D|={np.abs(D).max():.4f} vs RW~{math.sqrt(vM)*T/math.sqrt(K)*math.sqrt(K):.2f}")
print(f"SLAVING: corr(M, top-level M1) = {r:.4f}  R^2 = {r*r:.4f}")
print(f"residual sd = {res.std():.4f} vs raw {math.sqrt(vM):.4f}; residual band max|Dr| = {np.abs(Dr).max():.4f}")
