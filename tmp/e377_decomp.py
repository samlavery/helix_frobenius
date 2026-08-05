import numpy as np, math
N=10**7; n=np.arange(1,N+1,dtype=np.int64); cache={}
def M(p,d):
    if (p,d) not in cache:
        m=np.ones(N,bool); x=n.copy()
        for _ in range(d): m &= (x%p)<=(p-1)//2; x=x//p
        cache[(p,d)]=m
    return cache[(p,d)]
def dens(p,d): return (((p+1)//2)/p)**d
print("HARMONIC DECOMPOSITION TEST")
print("  is  err_joint  ==  sum_i err_i * prod_{j!=i} dens_j   (single-rail modes only)?")
print("  if yes, the cross modes contribute nothing and additivity is exact orthogonality.\n")
print("  p                d                err_joint     single-rail sum   ratio    cross/joint")
for ps,ds in [((3,5),(9,6)),((3,5,7),(7,5,4)),((3,5,7),(9,6,5)),((3,5,7,11),(7,5,4,3)),
              ((3,5,7,11,13),(7,5,4,3,3)),((11,13),(4,4)),((31,37),(3,3)),
              ((101,103),(2,2)),((1009,1013),(1,1)),((5,7,11),(5,4,3))]:
    m=np.ones(N,bool); D=1.0
    for p,d in zip(ps,ds): m &= M(p,d); D*=dens(p,d)
    ej=int(m.sum())-N*D
    est=0.0
    for i,(p,d) in enumerate(zip(ps,ds)):
        ei=int(M(p,d).sum())-N*dens(p,d)
        est+=ei*math.prod(dens(q,e) for j,(q,e) in enumerate(zip(ps,ds)) if j!=i)
    cross=ej-est
    print("  %-16s %-16s %+12.1f  %+14.1f   %7.3f  %10.3f"
          %(str(ps),str(ds),ej,est,(ej/est if est else float('nan')),abs(cross)/max(abs(ej),1e-9)))
