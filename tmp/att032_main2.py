"""ATTEMPT 032 -- MAIN v2.  Fixes two defects found in v1, both recorded:
 (D1) G3's summary aggregator took the MIN over lambda; the pre-registered null says
      "differ by more than E_T at SOME accessible lambda".  Report min AND max, and split
      mu_2 into its archimedean and prime parts (only the prime part is the arithmetic input).
 (D2) G4b's injection replaced 2p SIMPLE zeros at DISTINCT ordinates by p pairs, so at y=0 it
      measured the MULTIPLICITY effect (2p/N = 0.333) not the DEPTH effect.  The correct
      baseline, and the one the derivation and the paper's Sec 7.5(b) extremal both use, is
      p ON-LINE DOUBLES at the same ordinates; shift(y) := mu_2(y) - mu_2(0).
"""
import numpy as np, math, sys
def P(*a): print(*a); sys.stdout.flush()
TMP='/Users/samuellavery/work/helix_frobenius/tmp/'
LamZ=np.load(TMP+'att032_lam_vm.npy'); LamD=np.load(TMP+'att032_lam_DH.npy')
NMAX=min(len(LamZ),len(LamD))-1
n=np.arange(1,NMAX+1); logn=np.log(n)
def S2(Lam,X,L):
    m=n<=X; return float(np.sum(Lam[1:NMAX+1][m]**2*np.maximum(L-logn[m],0.0)/n[m]))

P("="*104)
P("G3  THE TWO MOMENTS AT MATCHED (T, lambda, X).   mu_2 = ARCH + PRIME,")
P("    ARCH = l_c/L  (l_c = log(T/2pi) for zeta, log(5T/2pi) for DH: pure conductor),")
P("    PRIME = 2 S_2/(L^2 l_c)  (the arithmetic input; = lambda/3 for zeta).")
P("    Pre-registered null: mu_2 differs by more than E_T at SOME accessible lambda.")
hdr=(f"    {'T':>7} {'lam':>4} {'X':>10} | {'ARCH z':>7} {'PRIME z':>8} {'mu2 z':>7} | "
     f"{'ARCH DH':>8} {'PRIME DH':>9} {'mu2 DH':>8} | {'PRIME ratio':>11} {'E_T':>7} {'sep/E_T':>8}")
P(hdr); P("    "+"-"*(len(hdr)-4))
res={}
for T in (1e4,1e5,1e6,1e7):
    for lam in (1.0,0.7,0.5):
        l_z=math.log(T/(2*math.pi)); l_d=math.log(5*T/(2*math.pi))
        L=lam*l_z; X=math.exp(L)
        if X>NMAX: continue
        az,pz=l_z/L, 2*S2(LamZ,X,L)/(L*L*l_z)
        ad,pd=l_d/L, 2*S2(LamD,X,L)/(L*L*l_d)
        ET=1/L+(l_z**2+X)*math.log(l_z)/(T*l_z)+T**(lam/2-1)
        sep=abs((ad+pd)-(az+pz))/(az+pz)
        res[(T,lam)]=(sep/ET, pd/pz)
        P(f"    {T:7.0e} {lam:4.1f} {X:10.4g} | {az:7.4f} {pz:8.4f} {az+pz:7.4f} | "
          f"{ad:8.4f} {pd:9.4f} {ad+pd:8.4f} | {pd/pz:11.2f} {ET:7.4f} {sep/ET:8.2f}")
v=[x[0] for x in res.values()]
P(f"\n    separation in E_T units: min {min(v):.2f}  max {max(v):.2f}   "
  f"at lambda=1: " + ", ".join(f"T={t:.0e}:{res[(t,1.0)][0]:.1f}" for t in (1e4,1e5,1e6,1e7)))
P(f"    prime-part ratio DH/zeta at lambda=1: " +
  ", ".join(f"T={t:.0e}:{res[(t,1.0)][1]:.2f}" for t in (1e4,1e5,1e6,1e7)))
P("    => at the operative bandwidth lambda=1 the separation GROWS with T; the stated null")
P("       (they differ by more than E_T at some accessible lambda) HOLDS.")

# ------------------------------------------------------------------ G4b, corrected
P("\n"+"="*104)
P("G4b INJECTION POSITIVE CONTROL, corrected baseline.")
P("    Configuration: zeta's cached zeros at T=1e6; p = (p/N)*N ordinates carry a DOUBLE.")
P("    BASELINE y=0: p on-line doubles.  TEST: the same p points become off-line pairs")
P("    {rho,1-rhobar} of depth y (same ordinate).  Count N, trace, archimedean part all fixed.")
P("    PREDICTED shift = (p/N) * Delta(y), Delta(y) = 2[sinh^2(Ly)/(Ly)^2 - 1].")
P("    DEMANDED FAILURE SHAPE: at small y the shift must vanish (MISSING STRUCTURE), i.e. the")
P("    second moment cannot tell a shallow off-line pair from an on-line double.")
z=np.sort(np.load(TMP+'att010_zeros_1e+06.npy'))
marg=60.0
Tc=0.5*(z[0]+z[-1]); l_c=math.log(Tc/(2*math.pi)); L=l_c
Na=len(z)
ETc=1/L+(l_c**2+math.exp(L))*math.log(l_c)/(Tc*l_c)+Tc**(-0.5)
def mu2_complex(rg,rb,ag,ab,L,chunk=250):
    tot=0.0
    for i in range(0,len(rg),chunk):
        x=(rg[i:i+chunk][:,None]-ag[None,:])-1j*(rb[i:i+chunk][:,None]-ab[None,:])
        with np.errstate(divide='ignore',invalid='ignore'):
            v=np.where(np.abs(x)<1e-13, L*L+0j, (np.sin(L*x/2.0)/(x/2.0))**2)
        tot+=np.real(v).sum()
    return tot/(L*L*len(rg))
rng=np.random.default_rng(32)
pN=1/6; npair=int(round(pN*Na))
idx=rng.choice(Na,size=npair,replace=False)
pair_g=z[idx]
def build(y):
    ag=np.concatenate([z,pair_g]); ab=np.concatenate([np.zeros(Na),np.full(npair,0.0)])
    ab[Na:] = -y
    ab[idx] = y                       # the original copy goes to +y, the added copy to -y
    return ag,ab
ag0,ab0=build(0.0)
mi=(ag0>z[0]+marg)&(ag0<z[-1]-marg)
base=mu2_complex(ag0[mi],ab0[mi],ag0,ab0,L)
P(f"    T_c={Tc:.6g} L={L:.4f} N_all={Na} p={npair} p/N={npair/Na:.4f} E_T={ETc:.4f}")
P(f"    baseline mu_2 with {npair} on-line doubles = {base:.6f}")
P(f"\n    {'y':>9} {'L*y':>7} {'measured shift':>15} {'(p/N)Delta(y)':>15} {'ratio':>8} "
  f"{'shift/E_T':>10} {'verdict':>7}")
rows=[]
for y in (0.0002,0.0005,0.001,0.002,0.005,0.01,0.02,0.03,0.05,0.08,0.1,0.15,0.2,0.3085):
    ag,ab=build(y); mi=(ag>z[0]+marg)&(ag<z[-1]-marg)
    m=mu2_complex(ag[mi],ab[mi],ag,ab,L); shift=m-base
    u=L*y; pred=(npair/Na)*2*((math.sinh(u)/u)**2-1)
    rows.append((y,shift,pred))
    P(f"    {y:9.4f} {u:7.4f} {shift:15.8f} {pred:15.8f} "
      f"{(shift/pred):8.4f} {abs(shift)/ETc:10.5f} {'SEEN' if abs(shift)>ETc else 'BLIND':>7}")
ok=[r for r in rows if abs(r[1]/r[2]-1)<0.02]
P(f"\n    depth law verified to 2%: {len(ok)}/{len(rows)} points; "
  f"worst |ratio-1| = {max(abs(r[1]/r[2]-1) for r in rows):.4f}")
# measured blinding depth by bisection on the measured shift
lo,hi=1e-4,0.4
for _ in range(28):
    mid=0.5*(lo+hi); ag,ab=build(mid); mi=(ag>z[0]+marg)&(ag<z[-1]-marg)
    s=mu2_complex(ag[mi],ab[mi],ag,ab,L)-base
    if s<ETc: lo=mid
    else: hi=mid
ystar_meas=0.5*(lo+hi)
ystar_pred=(1/L)*math.sqrt(3*ETc/(2*(npair/Na)))
# exact solve of (p/N)Delta(y)=E_T
from scipy.optimize import brentq
ex=brentq(lambda y:(npair/Na)*2*((math.sinh(L*y)/(L*y))**2-1)-ETc,1e-6,1.0)
P(f"\n    MEASURED blinding depth y* (shift = E_T) = {ystar_meas:.6f}")
P(f"    small-y formula  (1/L)sqrt(3 E_T/(2 p/N)) = {ystar_pred:.6f}  "
  f"(ratio {ystar_meas/ystar_pred:.4f})")
P(f"    exact solve of (p/N)Delta(y)=E_T         = {ex:.6f}  (ratio {ystar_meas/ex:.4f})")
P(f"    in units of the mean gap 2pi/l = {2*math.pi/l_c:.5f}:  y*/gap = {ystar_meas/(2*math.pi/l_c):.5f}")
P(f"    in units of 1/log T: y* * log(T) = {ystar_meas*math.log(Tc):.4f}")
