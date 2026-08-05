import numpy as np, math
def D_spacing(P,Q,A=64):
    "min |a Q - b P| over 1<=a<=A, b>=1  -- the three-distance spacing"
    best=min(abs(a*Q-round(a*Q/P)*P) for a in range(1,A+1))
    return max(best,1)
def err(ps,ds,N,n,cache={}):
    m=np.ones(N,bool); D=1.0
    for p,d in zip(ps,ds):
        k=(p,d)
        if k not in cache:
            mm=np.ones(N,bool); x=n.copy()
            for _ in range(d): mm &= (x%p)<=(p-1)//2; x=x//p
            cache[k]=mm
        m&=cache[k]; D*=(((p+1)//2)/p)**d
    return abs(int(m.sum())-N*D)
N=10**7; n=np.arange(1,N+1,dtype=np.int64)
print("CROSS-TERM MECHANISM: near-diagonal modes with spacing D = min|aQ-bP|")
print("  predicted near-diagonal contribution ~ M/(2D) ; capped by N\n")
print("  p^d        q^e         D      M/(2D)      min(N,M/2D)   single-mode  total pred   observed  ratio")
for ps,ds in [((101,103),(2,2)),((1009,1013),(1,1)),((251,257),(1,1)),((31,37),(3,3)),
              ((11,13),(4,4)),((3,5),(9,6)),((3,5,7),(7,5,4)),((7,11),(2,2))]:
    P=ps[0]**ds[0]; Q=ps[1]**ds[1] if len(ps)>1 else 1
    M=math.prod(p**d for p,d in zip(ps,ds))
    Dg=D_spacing(P,Q) if len(ps)==2 else 1
    nd=min(N,M/(2*Dg))
    sm=sum(p*(math.log(p)**max(d-1,0)) for p,d in zip(ps,ds))*math.pi**2/6
    pred=nd+sm; obs=err(ps,ds,N,n)
    print("  %-10d %-11d %-6d %-11.3g %-13.3g %-12.1f %-12.3g %-9.0f %.2f"
          %(P,Q,Dg,M/(2*Dg),nd,sm,pred,obs,obs/pred))
