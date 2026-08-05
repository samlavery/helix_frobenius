"""ENTROPY BUDGET, dyadic window [N/2,N] (n=0,1 are balanced at every rail -- artifact)."""
import numpy as np, math
def sieve(N):
    s=np.ones(N+1,bool); s[:2]=False
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]
def beta(p): return math.log(2*p/(p+1))/math.log(p)
C=1/3+1/5+1/7
for N in [10**6, 10**7, 4*10**7]:
    lo=N//2
    n=np.arange(lo,N+1,dtype=np.int64)
    print(f"\nN = {N}   window [{lo},{N}]")
    print(f"{'z':>7} {'#rails':>7} {'max pay':>10} {'argmax':>11} {'max cost':>9} "
          f"{'p90 cost':>9} {'#cost>1':>9} {'frac':>8}")
    print("-"*80)
    for z in [7,31,101,1009]:
        ps=[int(p) for p in sieve(z) if p>2]
        pay=np.zeros(len(n)); cost=np.zeros(len(n))
        for p in ps:
            D=(p-1)//2
            ok=np.ones(len(n),bool); q=n.copy()
            while q.any():
                liv=q>0
                ok &= ~(liv & ((q%p)>D))
                q=np.where(liv,q//p,0)
            pay+=ok*(1.0/p); cost+=ok*beta(p)
        mp=pay.max(); ap=int(n[pay.argmax()])
        print(f"{z:>7} {len(ps):>7} {mp:>10.6f} {ap:>11} {cost.max():>9.5f} "
              f"{np.percentile(cost,90):>9.5f} {int((cost>1).sum()):>9} "
              f"{(cost>1).mean():>8.2e}")
    print(f"   ceiling 1/3+1/5+1/7 = {C:.6f}")
