import numpy as np
def scan(lo,hi,bases):
    n=np.arange(lo,hi,dtype=np.int64); ok=np.ones(hi-lo,bool)
    for p in bases:
        half=(p-1)//2; q=n.copy()
        while q.max()>0:
            ok&=(q%p)<=half; q//=p
        if not ok.any(): return []
    return list(n[ok])
step=2*10**7
for bases,LIM in [((3,5,7,11),2*10**10),((3,5,7,13),10**10)]:
    found=[]; lo=1
    while lo<LIM:
        hi=min(lo+step,LIM); found+=scan(lo,hi,bases); lo=hi
    print(bases, "balanced n <=", LIM, ":", [int(x) for x in found])
