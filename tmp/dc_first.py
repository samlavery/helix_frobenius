"""DWELL + S(t) ON #400, IN THE RIGHT ORDER.
   WRONG (what I did): g_2(n) = quantile(N_n), then average over n.
   RIGHT (DC first):   average the occupancy over n  ->  DC spectrum  ->  quantile.
   S(t) claim: the per-n deviation g_2(n) - DCpred(n) is mean-zero chart error.
   If both hold, c_2 comes out of the DC spectrum and should be STABLE across windows."""
import numpy as np, math
from sympy import primerange
NM=1600; GMAX=40; M=2*NM+GMAX+4
ALL=[int(p) for p in primerange(2,NM+1)]
S={}
for p in ALL:
    a=np.arange(M); s=np.zeros(M,dtype=np.int64); t=a.copy()
    while t.max()>0: s+=t%p; t//=p
    S[p]=s
def spec(n,GM=GMAX):
    Ps=[p for p in ALL if p<=n]; out=[]
    for G in range(0,GM):
        A=n+G; a1=np.arange(0,A//2+1); m=None
        for p in Ps:
            v=S[p][a1]+S[p][A-a1]-S[p][n]
            m=v if m is None else np.minimum(m,v)
        out.append(int((m>=G).sum()))
    return np.array(out,dtype=float)
print("DC-FIRST: average survival prob over the window, then take the quantile\n")
print(f"{'window':>14} {'#n':>4} {'mean g2':>8} {'DC-quantile':>12} {'c2 direct':>10} {'c2 DC':>8}")
res=[]
for lo,hi in ((200,400),(400,800),(800,1600)):
    ns=list(range(lo,hi,7))
    Sp=np.vstack([spec(n) for n in ns])
    N0=Sp[:,0].copy()
    surv=(Sp/N0[:,None]).mean(axis=0)          # DC survival probability
    n0=N0.mean()
    g2s=np.array([np.max(np.nonzero(Sp[i]>0)[0]) for i in range(len(ns))],dtype=float)
    # quantile of the DC spectrum: solve surv(G)*n0 = 1 via Gaussian tail fit
    k=np.nonzero(surv>0)[0]; y=np.log(surv[k]*n0); x=k.astype(float)
    B=np.vstack([x*x,x,np.ones_like(x)]).T
    A2,B2,C2=np.linalg.lstsq(B,y,rcond=None)[0]
    a=-A2; b=B2/(2*a); c=C2+a*b*b
    dcq=b+math.sqrt(max(c,0)/a)
    L=math.log(math.sqrt(lo*hi))
    res.append((lo,hi,g2s.mean(),dcq,g2s.mean()/L,dcq/L))
    print(f"[{lo:>5},{hi:>5}) {len(ns):>4} {g2s.mean():>8.3f} {dcq:>12.3f} "
          f"{g2s.mean()/L:>10.4f} {dcq/L:>8.4f}")
print("\nS(t) CHECK: is the per-n deviation from the DC prediction mean-zero?")
ns=list(range(300,1600,5))
Sp=np.vstack([spec(n) for n in ns])
g2s=np.array([np.max(np.nonzero(Sp[i]>0)[0]) for i in range(len(ns))],dtype=float)
pred=[]
for i,n in enumerate(ns):
    k=np.nonzero(Sp[i]>0)[0]; y=np.log(Sp[i][k]); x=k.astype(float)
    if len(x)<5: pred.append(np.nan); continue
    B=np.vstack([x*x,x,np.ones_like(x)]).T
    A2,B2,C2=np.linalg.lstsq(B,y,rcond=None)[0]
    if A2>=0: pred.append(np.nan); continue
    a=-A2; b=B2/(2*a); c=C2+a*b*b
    pred.append(b+math.sqrt(max(c,0)/a))
pred=np.array(pred); ok=~np.isnan(pred)
dev=g2s[ok]-pred[ok]
print(f"  mean deviation = {dev.mean():+.4f}   sd = {dev.std():.4f}   n = {ok.sum()}")
run=np.cumsum(dev)
print(f"  running sum: max|.| = {np.abs(run).max():.1f} over {ok.sum()} terms; "
      f"sqrt(n)*sd = {math.sqrt(ok.sum())*dev.std():.1f}  -> "
      f"{'RANDOM WALK (mean-zero)' if np.abs(run).max()<3*math.sqrt(ok.sum())*dev.std() else 'DRIFT (biased)'}")
