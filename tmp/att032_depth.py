"""ATTEMPT 032 -- G4 corrected.  The pre-registered self-pair law shift = (p/N)Delta(y)
FAILED its 2% test (measured/predicted = 0.766, constant in y over four decades).  This stage
characterises the deficit, which is a genuine finding, and re-derives the blinding depth from
the MEASURED law.

DC-FIRST NOTE (why a deficit must exist and why its DC part is zero):
  moving one zero to depth y changes every cross term by Re F(a - i dy) - F(a),
  F(x) = (sin(Lx/2)/(x/2))^2.  F is entire of exponential type L and decays like |a|^{-2} along
  horizontal lines, so int_R F(a - iy) da = int_R F(a) da = 2 pi L by contour shift:
  THE SMOOTH (DC) BACKGROUND RESPONSE VANISHES IDENTICALLY.  What survives is the sum-minus-
  integral, i.e. the PAIR CORRELATION of the background at scale y.  So the deficit is an AC
  effect and must be sensitive to zero repulsion.
PRE-REGISTERED CONTROL: a POISSON background (no repulsion) must give a DIFFERENT deficit.
  NULL: Poisson and the true zeros give the same deficit -> the deficit is not a correlation
  effect and the DC argument above is wrong.
"""
import numpy as np, math, sys
from scipy.optimize import brentq
def P(*a): print(*a); sys.stdout.flush()
TMP='/Users/samuellavery/work/helix_frobenius/tmp/'
z=np.sort(np.load(TMP+'att010_zeros_1e+06.npy')); Na=len(z); marg=60.0
Tc=0.5*(z[0]+z[-1]); l_c=math.log(Tc/(2*math.pi)); L=l_c
ETc=1/L+(l_c**2+math.exp(L))*math.log(l_c)/(Tc*l_c)+Tc**(-0.5)
P(f"T_c={Tc:.6g}  L={L:.5f}  N={Na}  E_T={ETc:.5f}  mean gap 2pi/l = {2*math.pi/l_c:.5f}")

def run(base_z, pN, seed=32):
    Nb=len(base_z); npair=max(1,int(round(pN*Nb)))
    rng=np.random.default_rng(seed)
    idx=rng.choice(Nb,size=npair,replace=False); pg=base_z[idx]
    lo,hi=base_z[0]+marg, base_z[-1]-marg
    def build(y):
        ag=np.concatenate([base_z,pg]); ab=np.zeros(Nb+npair); ab[Nb:]=-y; ab[idx]=y
        return ag,ab
    ag0,_=build(0.0); mi=(ag0>lo)&(ag0<hi); Nr=int(mi.sum())
    p_in=int(((pg>lo)&(pg<hi)).sum())
    def tot(y,chunk=250):
        ag,ab=build(y); rg,rb=ag[mi],ab[mi]; s=0.0
        for i in range(0,len(rg),chunk):
            x=(rg[i:i+chunk][:,None]-ag[None,:])-1j*(rb[i:i+chunk][:,None]-ab[None,:])
            with np.errstate(divide='ignore',invalid='ignore'):
                v=np.where(np.abs(x)<1e-13,L*L+0j,(np.sin(L*x/2.0)/(x/2.0))**2)
            s+=np.real(v).sum()
        return s
    b0=tot(0.0)
    def shift(y): return (tot(y)-b0)/(L*L*Nr)
    return shift, p_in/Nr, Nr, p_in

def Delta(y): u=L*y; return 2*((math.sinh(u)/u)**2-1)

P("\n"+"="*96)
P("G4a  the deficit c(y) := measured shift / [ (p_in/N_rows) * Delta(y) ]  -- true zeta zeros")
P(f"    {'p/N':>7} {'y':>8} {'L y':>7} {'measured':>13} {'self-pair pred':>15} {'c':>8}")
tab={}
for pN in (1/6, 1/20, 1/60):
    sh,frac,Nr,p_in=run(z,pN)
    cs=[]
    for y in (0.001,0.01,0.05,0.1,0.2):
        m=sh(y); pr=frac*Delta(y); cs.append(m/pr)
        P(f"    {pN:7.4f} {y:8.4f} {L*y:7.4f} {m:13.8f} {pr:15.8f} {m/pr:8.4f}")
    tab[pN]=(sh,frac,cs)
    P(f"        -> p_in={p_in} N_rows={Nr} frac={frac:.5f}   c(small y) = {cs[0]:.4f}")
P("\n"+"="*96)
P("G4b  POISSON CONTROL (must fail by MISSING STRUCTURE: no level repulsion).")
rngp=np.random.default_rng(7)
span=z[-1]-z[0]
pois=np.sort(z[0]+span*rngp.random(Na))
shp,fracp,Nrp,p_inp=run(pois,1/6,seed=32)
P(f"    {'y':>8} {'zeta c':>9} {'Poisson c':>10}")
shz,fracz,csz=tab[1/6]
for k,y in enumerate((0.001,0.01,0.05,0.1,0.2)):
    cp=shp(y)/(fracp*Delta(y))
    P(f"    {y:8.4f} {csz[k]:9.4f} {cp:10.4f}")
P("    NULL for the control: the two columns agree -> the deficit is not a correlation effect.")

P("\n"+"="*96)
P("G4c  BLINDING DEPTH from the MEASURED law   c * (p/N) * Delta(y*) = E_T")
sh,frac,cs=tab[1/6]
c0=cs[0]
lo,hi=1e-4,0.4
for _ in range(30):
    mid=0.5*(lo+hi)
    if sh(mid)<ETc: lo=mid
    else: hi=mid
ymeas=0.5*(lo+hi)
ynaive=brentq(lambda y: frac*Delta(y)-ETc,1e-6,1.0)
ysmall=(1/L)*math.sqrt(3*ETc/(2*frac))
P(f"    p/N (effective) = {frac:.5f}   E_T = {ETc:.5f}")
P(f"    MEASURED       y* = {ymeas:.6f}")
P(f"    self-pair law  y* = {ynaive:.6f}   (measured/law = {ymeas/ynaive:.4f})")
P(f"    small-y formula   = {ysmall:.6f}   (1/L)sqrt(3 E_T/(2 p/N))")
P(f"    y* / mean gap     = {ymeas/(2*math.pi/l_c):.5f}")
P(f"    y* * log T        = {ymeas*math.log(Tc):.5f}")
P(f"    X^(2 y*)          = {math.exp(L)**(2*ymeas):.4f}")
P("\n    ASYMPTOTIC (E_T ~ log l /(2 pi l), l = log(T/2pi), p/N = 1/6):")
P(f"    {'T':>8} {'L':>8} {'E_T':>9} {'y*_small':>10} {'y*/gap':>9} {'y* log T':>9}")
for T in (1e6,1e7,1e12,1e30,1e100,1e1000):
    l=math.log(T/(2*math.pi)); ET=1/l+math.log(l)/(2*math.pi*l)+T**-0.5
    ys=(1/l)*math.sqrt(3*ET/(2*(1/6)))
    P(f"    {T:8.0e} {l:8.3f} {ET:9.5f} {ys:10.6f} {ys/(2*math.pi/l):9.5f} {ys*math.log(T):9.4f}")
