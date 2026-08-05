"""j-resolved forcing curve: P(rail r lower-half at lvl1 / lvl1&2 of q_j) vs j,
for jointly balanced (p,r) at real n.  Correlation length ell = last j above null."""
import numpy as np
from collections import defaultdict
def bal(x,p):
    while x:
        if x%p>(p-1)//2: return False
        x//=p
    return True
stats=defaultdict(lambda: [0,0,0])   # j -> [tot, lvl1, lvl12] aggregated over pairs (normalized by null)
per=defaultdict(lambda: defaultdict(lambda: [0,0,0]))
PAIRS=[(3,5),(3,7),(5,7),(3,11),(5,11),(7,11),(3,13),(5,13),(7,13),(11,13)]
cnt=0
for n in range(10**6, 4*10**6):
    for (p,r) in PAIRS:
        if bal(n,p) and bal(n,r):
            j=1
            while p**(j-1)<=n:
                q=n//p**(j-1)
                if q<r*r: break
                d1 = q%r<=(r-1)//2
                d12 = d1 and (q//r)%r<=(r-1)//2
                null1=(r+1)/(2*r)
                s=per[(p,r)][j]; s[0]+=1; s[1]+=d1; s[2]+=d12
                j+=1
            cnt+=1
print(f"jointly balanced (n,pair) events: {cnt}")
print(f"{'j':>3} {'N':>6} {'lvl1 obs/null':>14} {'lvl12 obs/null':>15}   (aggregated, null-normalized)")
agg=defaultdict(lambda:[0,0.0,0.0])
for (p,r),by_j in per.items():
    null1=(r+1)/(2*r); null12=null1*null1
    for j,(t,c1,c12) in by_j.items():
        if t==0: continue
        a=agg[j]; a[0]+=t; a[1]+=c1/null1; a[2]+=c12/null12
for j in sorted(agg):
    t,s1,s12=agg[j]
    print(f"{j:>3} {t:>6} {s1/t:>14.3f} {s12/t:>15.3f}")
