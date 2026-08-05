"""Census of {3,5,7,11}-balanced integers (full depth, all four bases) — the first
beta-over-budget set. Negative dimension excess -0.227 predicts a FINITE list."""
import numpy as np
def scan(lo,hi,bases=(3,5,7,11)):
    n=np.arange(lo,hi,dtype=np.int64)
    ok=np.ones(hi-lo,bool)
    for p in bases:
        half=(p-1)//2
        q=n.copy()
        while q.max()>0:
            ok&=(q%p)<=half
            q//=p
        if not ok.any(): return []
    return list(n[ok])
found=[]
step=5*10**6
lo=1
while lo<10**9:
    hi=min(lo+step,10**9)
    found+=scan(lo,hi)
    lo=hi
print("all {3,5,7,11}-balanced n <= 1e9:", found)
print("count:", len(found))
# also the other 4-sets at the trigger
for extra in (13,17,19):
    f2=[]
    lo=1
    while lo<10**8:
        hi=min(lo+step,10**8)
        f2+=scan(lo,hi,(3,5,7,extra))
        lo=hi
    print(f"{{3,5,7,{extra}}}-balanced n <= 1e8: {f2}")
