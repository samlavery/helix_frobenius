"""FINAL CORRECTION. Large rails are EXACTLY tight (they give exactly G), so the
   binding distribution lives on SMALL rails only.  Use the measured occupancy tail:
        log N_n(G) = c - a*(G-b)^2      =>      g_2 = b + sqrt(c/a)   [where N=1]
   Predict g_2 from the Gaussian tail fit alone."""
import numpy as np, math
from sympy import primerange
NM=1600; GMAX=40; M=2*NM+GMAX+4
ALL=[int(p) for p in primerange(2,NM+1)]
S={}
for p in ALL:
    a=np.arange(M); s=np.zeros(M,dtype=np.int64); t=a.copy()
    while t.max()>0: s+=t%p; t//=p
    S[p]=s
def spectrum(n):
    Ps=[p for p in ALL if p<=n]; out=[]
    for G in range(0,GMAX):
        A=n+G; a1=np.arange(0,A//2+1); m=None
        for p in Ps:
            v=S[p][a1]+S[p][A-a1]-S[p][n]
            m=v if m is None else np.minimum(m,v)
        out.append(int((m>=G).sum()))
        if out[-1]==0: break
    return out
print(f"{'n':>6} {'g2':>3} {'pred':>7} {'err':>6}   quadratic-tail prediction  g2 = b+sqrt(c/a)")
rows=[]
for n in range(300,1601,50):
    o=spectrum(n); g=len(o)-2
    y=np.array([math.log(v) for v in o if v>0]); x=np.arange(len(y),dtype=float)
    if len(y)<5: continue
    B=np.vstack([x*x,x,np.ones_like(x)]).T
    A2,B2,C2=np.linalg.lstsq(B,y,rcond=None)[0]
    if A2>=0: continue
    a=-A2; b=B2/(2*a); c=C2+a*b*b        # y = c - a(G-b)^2
    if c<0: continue
    pred=b+math.sqrt(c/a)
    rows.append((n,g,pred))
    if n%200==100: print(f"{n:>6} {g:>3} {pred:>7.2f} {pred-g:>6.2f}")
gs=np.array([r[1] for r in rows],float); pr=np.array([r[2] for r in rows])
print(f"\n  corr(pred, actual) = {np.corrcoef(pr,gs)[0,1]:+.4f}")
print(f"  mean err = {np.mean(pr-gs):+.3f}   mean |err| = {np.mean(np.abs(pr-gs)):.3f}   (geometric model: +3.85 / 3.85)")
ln=np.log(np.array([r[0] for r in rows],float))
print(f"  g2 / log n slope (actual)    = {np.polyfit(ln,gs,1)[0]:.4f}")
print(f"  g2 / log n slope (predicted) = {np.polyfit(ln,pr,1)[0]:.4f}")
print(f"\n  DC floor (k-1)/(2log2) = {1/(2*math.log(2)):.4f};  ceiling k/log2 = {2/math.log(2):.4f}")
