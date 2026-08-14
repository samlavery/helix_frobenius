"""Addendum: independent check of NULL-F (prime-truncation shares) and of the S reconstruction."""
import numpy as np, os, math
from math import log, pi
TMP=os.path.dirname(os.path.abspath(__file__))
def theta_rs(t):
    t=np.asarray(t,float)
    return t/2*np.log(t/(2*np.pi))-t/2-np.pi/8+1/(48*t)+7/(5760*t**3)
def primepow(X):
    X=int(X); s=np.ones(X+1,bool); s[:2]=False
    for i in range(2,int(X**0.5)+1):
        if s[i]: s[i*i::i]=False
    ns,lam=[],[]
    for p in np.nonzero(s)[0]:
        pk=int(p)
        while pk<=X: ns.append(pk); lam.append(log(p)); pk*=int(p)
    o=np.argsort(ns); return np.array(ns,float)[o],np.array(lam,float)[o]
Z={T:np.load(os.path.join(TMP,f'att010_zeros_{T:.0e}.npy')) for T in (1e3,1e5,1e7)}
print(f"{'T':>8}{'x':>8}{'#terms':>8}{'Var S':>9}{'Var res':>9}{'var share':>10}{'max|S|':>9}{'max res':>9}{'sup share':>10}{'N0':>4}{'mean0':>8}")
for T,gam in sorted(Z.items()):
    t=np.linspace(gam[0]+1e-6,gam[-1]-1e-6,200000)
    k=np.searchsorted(gam,t,side='right').astype(float)
    base=k-theta_rs(t)/pi-1.0
    N0=round(-base.mean()); S=base+N0
    t=t[::20]; S=S[::20]
    v0=S.var(); m0=np.abs(S).max()
    for x in (1e3,1e5):
        ns,lam=primepow(x); w=lam/(np.sqrt(ns)*np.log(ns))
        Sx=np.zeros_like(t)
        for i in range(0,len(ns),512):
            Sx+= (np.sin(np.outer(t,np.log(ns[i:i+512])))*w[i:i+512]).sum(axis=1)
        Sx*=-(1/pi); res=S-Sx
        print(f"{T:>8.0e}{x:>8.0e}{len(ns):>8d}{v0:>9.4f}{res.var():>9.4f}{1-res.var()/v0:>10.4f}"
              f"{m0:>9.4f}{np.abs(res).max():>9.4f}{1-np.abs(res).max()/m0:>10.4f}{N0:>4d}{base.mean()+N0:>8.4f}")
