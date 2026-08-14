"""ATTEMPT 032 G4e.  c(lambda=1) measured = 0.748 +- 0.012 over four decades; 3/4 = F(1),
the paper's own  F(lambda) = lambda/(1+lambda^2/3).
PRE-REGISTERED PREDICTION (stated before this run):  c(lambda) = F(lambda), i.e.
   lambda = 1.0 -> 0.7500 ;  0.7 -> 0.6018 ;  0.5 -> 0.4615 ;  0.3 -> 0.2971 ; 1.3 -> 0.8523.
NULL: c is independent of lambda (then it is not F and the coincidence at lambda=1 is chance).
"""
import numpy as np, math, sys
def P(*a): print(*a); sys.stdout.flush()
TMP='/Users/samuellavery/work/helix_frobenius/tmp/'
def c_of(path,lam,pN=1/6,y=0.005,seed=32,poisson=False):
    z=np.sort(np.load(path)); Na=len(z); marg=60.0
    if poisson: z=np.sort(z[0]+(z[-1]-z[0])*np.random.default_rng(7).random(Na))
    Tc=0.5*(z[0]+z[-1]); l=math.log(Tc/(2*math.pi)); L=lam*l
    rng=np.random.default_rng(seed); npair=int(round(pN*Na))
    idx=rng.choice(Na,size=npair,replace=False); pg=z[idx]
    lo,hi=z[0]+marg,z[-1]-marg
    def build(yy):
        ag=np.concatenate([z,pg]); ab=np.zeros(Na+npair); ab[Na:]=-yy; ab[idx]=yy; return ag,ab
    ag0,_=build(0.0); mi=(ag0>lo)&(ag0<hi); Nr=int(mi.sum()); p_in=int(((pg>lo)&(pg<hi)).sum())
    def tot(yy,chunk=250):
        ag,ab=build(yy); rg,rb=ag[mi],ab[mi]; s=0.0
        for i in range(0,len(rg),chunk):
            x=(rg[i:i+chunk][:,None]-ag[None,:])-1j*(rb[i:i+chunk][:,None]-ab[None,:])
            with np.errstate(divide='ignore',invalid='ignore'):
                v=np.where(np.abs(x)<1e-13,L*L+0j,(np.sin(L*x/2.0)/(x/2.0))**2)
            s+=np.real(v).sum()
        return s
    u=L*y; m=(tot(y)-tot(0.0))/(L*L*Nr)
    return m/((p_in/Nr)*2*((math.sinh(u)/u)**2-1))
F=lambda lam: lam/(1+lam*lam/3)
P(f"    {'lambda':>7} {'F(lam)':>8} | " + " ".join(f"{n:>8}" for n in ('1e+04','1e+05','1e+06','1e+07'))
  + f" {'mean':>8} {'mean/F':>8} {'POIS 1e6':>9}")
for lam in (1.3,1.0,0.7,0.5,0.3):
    cs=[c_of(TMP+f'att010_zeros_{n}.npy',lam) for n in ('1e+04','1e+05','1e+06','1e+07')]
    cp=c_of(TMP+'att010_zeros_1e+06.npy',lam,poisson=True)
    mu=float(np.mean(cs))
    P(f"    {lam:7.2f} {F(lam):8.4f} | " + " ".join(f"{c:8.4f}" for c in cs)
      + f" {mu:8.4f} {mu/F(lam):8.4f} {cp:9.4f}")
P("\n    Poisson prediction if the damping is a repulsion effect: c_POIS = 1 at every lambda.")
