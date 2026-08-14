"""Does the removable fraction of S grow with HEIGHT?
Surviving band: log n <~ L'/(0.8 pi), L' = log(t/2pi).  So the harmonic truncation
should admit more primes -- and predict better -- as t increases."""
import numpy as np, mpmath as mp, sys
mp.mp.dps=15
def P(*a): print(*a); sys.stdout.flush()
X=200000
Lm=np.zeros(X+1)
for p in range(2,X+1):
    if all(p%q for q in range(2,int(p**0.5)+1)):
        q=p
        while q<=X: Lm[q]=np.log(p); q*=p
IDX=np.nonzero(Lm)[0]; W=Lm[IDX]/(np.sqrt(IDX)*np.log(IDX)); LN=np.log(IDX)
def invth(y,g): return float(mp.findroot(lambda t: mp.siegeltheta(t)-y, g))
P(f"{'zeros n':>14}{'t range':>18}{'L-prime':>9}{'cutoff n':>10}{'#terms':>8}"
  f"{'base sd':>10}{'final sd':>10}{'reduction':>11}")
for lo,hi in ((1,200),(400,600),(1400,1600),(3000,3200)):
    true=[float(mp.im(mp.zetazero(k))) for k in range(lo,hi+1)]
    ns=np.arange(lo,hi+1)
    sp=np.array([2*np.pi/np.log(t/(2*np.pi)) for t in true])
    Lp=np.log(np.mean(true)/(2*np.pi))
    cut=np.exp(Lp/(0.8*np.pi))
    m=IDX<=max(4,cut); w=W[m]; ln=LN[m]
    S=lambda t: -(1/np.pi)*np.sum(w*np.sin(t*ln))
    gam=np.array([invth((n-1.5)*np.pi, max(true[i],14.0)) for i,n in enumerate(ns)])
    base=((gam-np.array(true))/sp).std()
    for it in range(4):
        Sv=np.array([S(t) for t in gam])
        gam=np.array([invth((n-1.5-Sv[i])*np.pi, gam[i]) for i,n in enumerate(ns)])
    fin=((gam-np.array(true))/sp).std()
    P(f"{f'{lo}-{hi}':>14}{f'{true[0]:.0f}-{true[-1]:.0f}':>18}{Lp:>9.2f}{cut:>10.1f}"
      f"{int(m.sum()):>8}{base:>10.5f}{fin:>10.5f}{1-fin/base:>10.1%}")
