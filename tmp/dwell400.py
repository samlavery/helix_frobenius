"""DWELL APPLIED TO #400.
   The readout g_2(n) = max_a min_p [.] SKIPS every non-optimal split.
   Dwell re-registers them: the occupancy spectrum
        N_n(G) = #{ splits a_1+a_2 = n+G : min_p ( s_p(a1)+s_p(a2)-s_p(n) ) >= G }.
   g_2(n) = max{ G : N_n(G) >= 1 }  -- the max only reads where occupancy hits zero.
   PREDICTION (harmonic): occupancy decays geometrically, N_n(G) ~ N_n(0) theta^G,
   hence   g_2(n) ~ log N_n(0) / log(1/theta)   -- the max DERIVED from the DC,
   instead of estimated.  If this holds, c_2 is a saddle point, not an extreme value."""
import numpy as np, math
from sympy import primerange
NM=1200; GMAX=34; M=2*NM+GMAX+4
ALL=[int(p) for p in primerange(2,NM+1)]
S={}
for p in ALL:
    a=np.arange(M); s=np.zeros(M,dtype=np.int64); t=a.copy()
    while t.max()>0: s+=t%p; t//=p
    S[p]=s
def occupancy(n):
    Ps=[p for p in ALL if p<=n]; out=[]
    for G in range(0,GMAX):
        A=n+G; a1=np.arange(0,A//2+1); m=None
        for p in Ps:
            v=S[p][a1]+S[p][A-a1]-S[p][n]
            m=v if m is None else np.minimum(m,v)
        out.append(int((m>=G).sum()))
        if out[-1]==0: break
    return out
print("occupancy spectra N_n(G)  (dwell readout; g_2 = last G with N>0)")
for n in (200,400,800,1200):
    o=occupancy(n); g=len(o)-2
    print(f"  n={n:>5} g2={g:>2}  N = {o[:12]}{' ...' if len(o)>12 else ''}")
print("\nIs the decay geometric?  fit log N_n(G) = log N_n(0) + G log(theta)")
print(f"{'n':>6} {'g2':>3} {'logN0':>7} {'log(1/th)':>10} {'pred g2':>8} {'err':>6} {'R^2':>6}")
rows=[]
for n in range(300,1201,60):
    o=occupancy(n); g=len(o)-2
    y=[math.log(v) for v in o if v>0]; x=list(range(len(y)))
    if len(y)<4: continue
    A_=np.vstack([np.array(x),np.ones(len(x))]).T
    sol,_,_,_=np.linalg.lstsq(A_,np.array(y),rcond=None)
    slope,inter=sol
    ss=1-np.sum((np.array(y)-A_@sol)**2)/max(1e-12,np.sum((np.array(y)-np.mean(y))**2))
    pred=inter/(-slope) if slope<0 else float('nan')
    rows.append((n,g,inter,-slope,pred,ss))
    print(f"{n:>6} {g:>3} {inter:>7.3f} {-slope:>10.4f} {pred:>8.2f} {pred-g:>6.2f} {ss:>6.3f}")
gs=np.array([r[1] for r in rows]); pr=np.array([r[4] for r in rows])
print(f"\n  corr(pred, actual) = {np.corrcoef(pr,gs)[0,1]:+.4f}   mean |err| = {np.mean(np.abs(pr-gs)):.3f}")
print(f"  mean R^2 of geometric fit = {np.mean([r[5] for r in rows]):.4f}")
th=np.array([r[3] for r in rows]); n_=np.array([r[0] for r in rows],dtype=float)
print(f"  log(1/theta): mean {th.mean():.4f} sd {th.std():.4f}  -> theta {math.exp(-th.mean()):.4f}")
print(f"  logN0 vs log n: slope {np.polyfit(np.log(n_),np.array([r[2] for r in rows]),1)[0]:.4f} (DC predicts 1)")
print(f"  => c_2 predicted = slope/mean log(1/theta) = {np.polyfit(np.log(n_),np.array([r[2] for r in rows]),1)[0]/th.mean():.4f}")
