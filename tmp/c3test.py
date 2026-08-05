"""TEST THE WARP'S LINEARITY:  c_k = (k-1) c_2 ?
   k=3 occupancy by SAMPLING splits (DC only needs the survival probability).
   N_0 = #{(a1,a2,a3)>=0 : sum = A} = C(A+2,2).  DC-first: average survival, then quantile."""
import numpy as np, math
from sympy import primerange
rng=np.random.default_rng(7)
NM=900; GMAX=44; M=2*NM+GMAX+4
ALL=[int(p) for p in primerange(2,NM+1)]
S={}
for p in ALL:
    a=np.arange(M); s=np.zeros(M,dtype=np.int64); t=a.copy()
    while t.max()>0: s+=t%p; t//=p
    S[p]=s
NS=40000
def surv3(n,G):
    A=n+G; Ps=[p for p in ALL if p<=n]
    a1=rng.integers(0,A+1,NS); a2=rng.integers(0,A+1,NS)
    keep=(a1+a2)<=A; a1=a1[keep]; a2=a2[keep]; a3=A-a1-a2
    m=None
    for p in Ps:
        v=S[p][a1]+S[p][a2]+S[p][a3]-S[p][n]
        m=v if m is None else np.minimum(m,v)
    return float((m>=G).mean()), len(a1)
def dc_quantile(ns,k):
    rows=[]
    for G in range(0,GMAX):
        ps=[]
        for n in ns:
            s,_=surv3(n,G) if k==3 else (None,None)
            ps.append(s)
        rows.append(np.mean(ps))
        if rows[-1]<1e-6: break
    A0=int(np.mean(ns)); N0=(A0+2)*(A0+1)/2
    y=[];x=[]
    for G,v in enumerate(rows):
        if v>0: y.append(math.log(v*N0)); x.append(float(G))
    y=np.array(y);x=np.array(x)
    B=np.vstack([x*x,x,np.ones_like(x)]).T
    A2,B2,C2=np.linalg.lstsq(B,y,rcond=None)[0]
    a=-A2; b=B2/(2*a); c=C2+a*b*b
    return b+math.sqrt(max(c,0)/a), rows
print("k=3, DC-first quantile by sampling")
print(f"{'window':>14} {'DC-quantile':>12} {'log n':>7} {'c_3':>8} {'c_3/c_2':>9}")
C2M=1.2403
for lo,hi in ((200,400),(400,800)):
    ns=list(range(lo,hi,max(1,(hi-lo)//25)))
    q,rows=dc_quantile(ns,3)
    L=math.log(math.sqrt(lo*hi))
    print(f"[{lo:>5},{hi:>5}) {q:>12.3f} {L:>7.3f} {q/L:>8.4f} {q/L/C2M:>9.4f}")
print(f"\n  warp predicts c_3/c_2 = 2 exactly")
print(f"  closed form: c_2=1.1089 c_3=2.2178 (ratio 2.0000); measured c_2=1.2403")
