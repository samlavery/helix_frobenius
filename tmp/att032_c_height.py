"""ATTEMPT 032 G4d -- is the back-reaction damping c universal in height?
NULL: c drifts with T (then it is a finite-L artifact, not a structural damping)."""
import numpy as np, math, sys
def P(*a): print(*a); sys.stdout.flush()
TMP='/Users/samuellavery/work/helix_frobenius/tmp/'
def c_of(path,label,pN=1/6,y=0.005,seed=32,poisson=False):
    z=np.sort(np.load(path)); Na=len(z); marg=60.0
    if poisson:
        z=np.sort(z[0]+(z[-1]-z[0])*np.random.default_rng(7).random(Na))
    Tc=0.5*(z[0]+z[-1]); L=math.log(Tc/(2*math.pi))
    rng=np.random.default_rng(seed); npair=int(round(pN*Na))
    idx=rng.choice(Na,size=npair,replace=False); pg=z[idx]
    lo,hi=z[0]+marg,z[-1]-marg
    def build(yy):
        ag=np.concatenate([z,pg]); ab=np.zeros(Na+npair); ab[Na:]=-yy; ab[idx]=yy
        return ag,ab
    ag0,_=build(0.0); mi=(ag0>lo)&(ag0<hi); Nr=int(mi.sum()); p_in=int(((pg>lo)&(pg<hi)).sum())
    def tot(yy,chunk=250):
        ag,ab=build(yy); rg,rb=ag[mi],ab[mi]; s=0.0
        for i in range(0,len(rg),chunk):
            x=(rg[i:i+chunk][:,None]-ag[None,:])-1j*(rb[i:i+chunk][:,None]-ab[None,:])
            with np.errstate(divide='ignore',invalid='ignore'):
                v=np.where(np.abs(x)<1e-13,L*L+0j,(np.sin(L*x/2.0)/(x/2.0))**2)
            s+=np.real(v).sum()
        return s
    m=(tot(y)-tot(0.0))/(L*L*Nr)
    u=L*y; pred=(p_in/Nr)*2*((math.sinh(u)/u)**2-1)
    P(f"    {label:>16} Tc={Tc:10.4g} L={L:7.4f} N={Na:5d}  c = {m/pred:.5f}")
    return m/pred
P("G4d  damping c at fixed y=0.005 across four decades of height (true zeros):")
for nm in ('1e+03','1e+04','1e+05','1e+06','1e+07'):
    c_of(TMP+f'att010_zeros_{nm}.npy',nm)
P("\n     Poisson controls at the same heights:")
for nm in ('1e+03','1e+05','1e+07'):
    c_of(TMP+f'att010_zeros_{nm}.npy',nm+' POIS',poisson=True)
