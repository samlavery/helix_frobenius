import numpy as np, math
def L(p,d):
    mod=p**d; v=np.zeros(mod)
    for r in range(mod):
        x=r; ok=True
        for _ in range(d):
            if x%p>(p-1)//2: ok=False; break
            x//=p
        v[r]=1.0 if ok else 0.0
    C=np.fft.fft(v)/mod
    return np.abs(C).sum()
print("Lebesgue constant L(p,d) = sum_alpha |chat(alpha)|  for the depth-d restricted-digit rail")
print("   p    d     L(p,d)      p^d        (2 log p)^d    L / (log p)^d")
for p in [3,5,7,11,101,1009]:
    for d in ([1,2,3,4,5,6,7,8] if p<12 else [1,2]):
        if p**d>3*10**6: break
        l=L(p,d); print("  %-5d %-4d  %-11.3f %-10d %-13.2f %.3f"%(p,d,l,p**d,(2*math.log(p))**d,l/math.log(p)**d))
print()
print("TEST: does err <= (prod_i L_i) * log M explain the sweep, including the cases sum p^d failed?")
N=10**7; n=np.arange(1,N+1,dtype=np.int64); cache={}
def mask(p,d):
    if (p,d) not in cache:
        m=np.ones(N,bool); x=n.copy()
        for _ in range(d): m &= (x%p)<=(p-1)//2; x=x//p
        cache[(p,d)]=m
    return cache[(p,d)]
print("   config                       |err|      prod L * log M    sum p^d     ratio to Lbound")
for ps,ds in [((3,5),(9,6)),((3,5,7),(7,5,4)),((3,5,7,11),(7,5,4,3)),((11,13),(4,4)),
              ((31,37),(3,3)),((101,103),(2,2)),((1009,1013),(1,1)),((251,257),(1,1))]:
    m=np.ones(N,bool); D=1.0; M=1; Lp=1.0
    for p,d in zip(ps,ds):
        m &= mask(p,d); D*=(((p+1)//2)/p)**d; M*=p**d; Lp*=L(p,d)
    e=abs(int(m.sum())-N*D); bound=Lp*math.log(M); S=sum(p**d for p,d in zip(ps,ds))
    print("   p=%-18s d=%-14s %-10.0f %-16.1f %-11d %.3f"%(str(ps),str(ds),e,bound,S,e/bound))
