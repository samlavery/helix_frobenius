"""CORRECTION: occupancy tail is GAUSSIAN, so g_2 is an extreme-value quantile.
   Measure mu_n, sigma_n of X_a = min_p ( s_p(a1)+s_p(A-a1)-s_p(n) ) over splits,
   with N_0 = #splits.  Extreme-value law:  g_2 ~ mu + sigma*sqrt(2 log N_0).
   Test 1: does log N(G) fit G^2 better than G?
   Test 2: does the quantile law predict g_2?"""
import numpy as np, math
from sympy import primerange
NM=1400; GMAX=36; M=2*NM+GMAX+4
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
def stats(n):
    Ps=[p for p in ALL if p<=n]; A=n; a1=np.arange(0,A//2+1); m=None
    for p in Ps:
        v=S[p][a1]+S[p][A-a1]-S[p][n]
        m=v if m is None else np.minimum(m,v)
    return float(m.mean()), float(m.std()), len(a1)
r1=[];r2=[];rows=[]
for n in range(300,1401,50):
    o=spectrum(n); g=len(o)-2
    y=np.array([math.log(v) for v in o if v>0]); x=np.arange(len(y),dtype=float)
    if len(y)<5: continue
    for basis,store in ((np.vstack([x,np.ones_like(x)]).T,r1),
                        (np.vstack([x*x,np.ones_like(x)]).T,r2)):
        sol,_,_,_=np.linalg.lstsq(basis,y,rcond=None)
        store.append(1-np.sum((y-basis@sol)**2)/np.sum((y-y.mean())**2))
    mu,sd,N0=stats(n)
    pred=mu+sd*math.sqrt(2*math.log(N0))
    rows.append((n,g,mu,sd,N0,pred))
print(f"TEST 1  mean R^2:  linear in G = {np.mean(r1):.4f}    quadratic in G = {np.mean(r2):.4f}")
print(f"        -> tail is {'GAUSSIAN' if np.mean(r2)>np.mean(r1) else 'geometric'}\n")
print(f"TEST 2  {'n':>6} {'g2':>3} {'mu':>7} {'sigma':>6} {'N0':>5} {'pred':>7} {'err':>6}")
for n,g,mu,sd,N0,pred in rows[::3]:
    print(f"        {n:>6} {g:>3} {mu:>7.2f} {sd:>6.2f} {N0:>5} {pred:>7.2f} {pred-g:>6.2f}")
gs=np.array([r[1] for r in rows],float); pr=np.array([r[5] for r in rows])
print(f"\n  corr(quantile pred, actual) = {np.corrcoef(pr,gs)[0,1]:+.4f}   mean err = {np.mean(pr-gs):+.3f}   mean|err| = {np.mean(np.abs(pr-gs)):.3f}")
ln=np.log(np.array([r[0] for r in rows],float))
mu=np.array([r[2] for r in rows]); sd=np.array([r[3] for r in rows])
print(f"  mu / log n   : {np.polyfit(ln,mu,1)[0]:.4f}   (DC predicts (k-1)/(2 log2) = {1/(2*math.log(2)):.4f})")
print(f"  sigma^2/log n: {np.polyfit(ln,sd**2,1)[0]:.4f}")
print(f"  => c_2 = mu/log n + (sigma/sqrt(log n))*sqrt(2 log N0)/sqrt(log n) ~ "
      f"{np.polyfit(ln,mu,1)[0] + math.sqrt(np.polyfit(ln,sd**2,1)[0])*math.sqrt(2):.4f}")
