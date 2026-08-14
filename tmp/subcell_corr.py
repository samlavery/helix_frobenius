"""Add a pi/3 SUB-CELL correction, computed from the PREDICTED position (non-circular).
Residual drifts +0.047 / -0.004 / -0.041 across the three thirds of the pi cell."""
import numpy as np, mpmath as mp, sys
mp.mp.dps=15
def P(*a): print(*a); sys.stdout.flush()
X=4000
Lm=np.zeros(X+1)
for p in range(2,X+1):
    if all(p%q for q in range(2,int(p**0.5)+1)):
        q=p
        while q<=X: Lm[q]=np.log(p); q*=p
IDX=np.nonzero(Lm)[0]
def isp(n,p):
    while n%p==0: n//=p
    return n==1
m=np.array([isp(int(n),2) or isp(int(n),3) for n in IDX])
w=Lm[IDX][m]/(np.sqrt(IDX[m])*np.log(IDX[m])); ln=np.log(IDX[m])
S=lambda t: -(1/np.pi)*np.sum(w*np.sin(t*ln))
def invth(y,g): return float(mp.findroot(lambda t: mp.siegeltheta(t)-y, g))
NZ=500
true=np.array([float(mp.im(mp.zetazero(k))) for k in range(1,NZ+1)])
ns=np.arange(1,NZ+1)
sp=np.array([2*np.pi/np.log(t/(2*np.pi)) for t in true])
def run(subcorr=None):
    gam=np.array([invth((n-1.5)*np.pi, max(true[i],14.0)) for i,n in enumerate(ns)])
    for _ in range(3):
        Sv=np.array([S(t) for t in gam])
        if subcorr is not None:
            thp=np.array([float(mp.siegeltheta(t)) for t in gam])   # PREDICTED position
            k=np.floor(np.mod(3*thp/np.pi,3)).astype(int)
            Sv=Sv+subcorr[k]
        gam=np.array([invth((n-1.5-Sv[i])*np.pi, gam[i]) for i,n in enumerate(ns)])
    return (gam-true)/sp, gam
r0,g0=run()
P(f"before sub-cell correction: sd {r0.std():.5f} spacings")
# measure the drift from the FIRST HALF only, apply to the whole (no leakage)
th0=np.array([float(mp.siegeltheta(t)) for t in g0])
k0=np.floor(np.mod(3*th0/np.pi,3)).astype(int)
half=len(r0)//2
corr=np.array([ -np.pi*r0[:half][k0[:half]==j].mean()*sp[:half][k0[:half]==j].mean()/np.pi
                if (k0[:half]==j).sum()>3 else 0.0 for j in range(3)])
# convert residual (in spacings) to an S-offset: delta_theta = r*sp*dtheta/dt, and S shifts theta by -pi
dth=np.array([np.log(t/(2*np.pi))/2 for t in true])
corr=np.array([ (r0[:half][k0[:half]==j]*sp[:half]*dth[:half]/np.pi)[k0[:half]==j].mean()
                if (k0[:half]==j).sum()>3 else 0.0 for j in range(3)])
P(f"  fitted sub-cell S-offsets (first half only): {np.round(corr,5)}")
r1,_=run(corr)
P(f"after  sub-cell correction: sd {r1.std():.5f} spacings   -> {1-r1.std()/r0.std():+.1%}")
P(f"  second-half only (held out): before {r0[half:].std():.5f}  after {r1[half:].std():.5f}"
  f"  -> {1-r1[half:].std()/r0[half:].std():+.1%}")
P(f"\n  lag-1 autocorr before {np.corrcoef(r0[:-1],r0[1:])[0,1]:+.4f}"
  f"   after {np.corrcoef(r1[:-1],r1[1:])[0,1]:+.4f}")
