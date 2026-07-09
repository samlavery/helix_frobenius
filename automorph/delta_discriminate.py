import numpy as np
# Does the EXACT theta-modularity test discriminate? Delta: theta(1/y)=y^12 theta(y) (exact for genuine tau).
NB=400; P=np.zeros(NB+1);P[0]=1
for n in range(1,NB+1): P[n:]-=P[:NB+1-n].copy()
R=np.zeros(NB+1);R[0]=1;base=P.copy();e=24
while e:
    if e&1: R=np.convolve(R,base)[:NB+1]
    base=np.convolve(base,base)[:NB+1]; e>>=1
tau=np.zeros(NB+1); tau[1:]=R[:NB]
def th(c,y):
    n=np.arange(1,NB+1); return np.sum(c[1:]*np.exp(-2*np.pi*n*y))
def modresid(c,label):
    ys=np.geomspace(0.2,1.0,7)   # y and 1/y both sampled; exact FE => theta(1/y)-y^12 theta(y)=0
    r=[abs(th(c,1/y)-y**12*th(c,y)) for y in ys]
    # normalize by |y^12 theta(y)| scale to compare fairly
    scale=[abs(y**12*th(c,y))+1e-300 for y in ys]
    rel=np.array(r)/np.array(scale)
    print(f"  {label:16s}: max abs resid={max(r):.2e}  max REL resid={max(rel):.2e}")
    return max(rel)
rng=np.random.default_rng(1)
g=modresid(tau,"genuine tau")
tr=tau.copy(); tr[1:]=tau[1:][::-1]; modresid(tr,"reversed tau")
ts=tau.copy(); ts[1:]=tau[1:]*rng.choice([-1,1],NB); modresid(ts,"sign-scrambled")
tm=tau.copy(); tm[1:]=tau[1:]*rng.standard_normal(NB); modresid(tm,"mag-scrambled")
print("  => if genuine REL resid << scrambled, the exact modularity test DISCRIMINATES (genuine test).")
