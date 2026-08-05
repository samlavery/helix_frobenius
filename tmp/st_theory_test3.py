"""Extend to 1e18 + slaving test: how much of M is explained by the top-1-level
chart geometry (leading-digit phases) — the digit-fiber analog of the zeta
Euler-stream slaving (99.5% there)."""
import numpy as np, math
def primes_to(m):
    s=np.ones(m+1,bool); s[:2]=False
    for i in range(2,int(m**.5)+1):
        if s[i]: s[i*i::i]=False
    return [int(q) for q in np.nonzero(s)[0]]
Y=2000; c=2.0
P=[p for p in primes_to(Y) if p>=3]
logs={p:math.log(p) for p in P}
J={p:max(1,int(c*math.log(math.log(p+2)))) for p in P}
rng=np.random.default_rng(378)
K=40000
u=np.sort(rng.uniform(math.log(1e6), math.log(9e17), K))
xs=np.exp(u).astype(np.int64)
M=np.zeros(K); M1=np.zeros(K)
for k,xv in enumerate(xs):
    lx=math.log(xv); m=0.0; m1=0.0
    for p in P:
        d=int(lx/logs[p]); Jp=min(J[p],d)
        q=xv//p**(d-Jp); ok=True; first=None
        for t in range(Jp):
            dig=q%p
            if t==Jp-1: first=dig   # top digit last
            if dig>(p-1)//2: ok=False
            q//=p
        # recompute top digit properly: top digit = xv // p^(d-1) ... use directly
        td=xv//p**(d-1)
        if td<=(p-1)//2: m1+=1.0/p
        if ok: m+=1.0/p
    M[k]=m; M1[k]=m1
mean=M.mean(); sig=M.std()
du=np.diff(u,prepend=u[0]); D=np.cumsum((M-mean)*du); T=u[-1]-u[0]
print(f"span 1e6..9e17 (T={T:.1f}): mean={mean:.4f} sup={M.max():.4f} sig={sig:.4f}")
print(f"max|D|={np.abs(D).max():.4f}  vs RW={sig*T/math.sqrt(K)*math.sqrt(K):.3f}  ratio/sqrtK: {np.abs(D).max()/(sig*T/math.sqrt(K)):.2f} vs 200")
r=np.corrcoef(M,M1)[0,1]
beta=np.polyfit(M1,M,1)
res=M-np.polyval(beta,M1)
print(f"slaving: corr(M, M1_top-level)={r:.4f}  R2={r*r:.4f}  residual sigma={res.std():.4f} (vs {sig:.4f})")
Dr=np.cumsum((res-res.mean())*du)
print(f"residual integral band: max|Dr|={np.abs(Dr).max():.4f}")
print(f"sup M by decade:")
for lo,hi in [(1e6,1e9),(1e9,1e12),(1e12,1e15),(1e15,9e17)]:
    m=(xs>=lo)&(xs<hi)
    if m.any(): print(f"  [{lo:.0e},{hi:.0e}): sup={M[m].max():.4f} mean={M[m].mean():.4f}")
