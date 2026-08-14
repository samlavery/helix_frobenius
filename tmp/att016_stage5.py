"""ATTEMPT 016, stage 5 -- consolidation: the tau=1 line's decay law and its certificate mass.

PRE-REGISTERED (from the stage-1 derivation): mass m = K(1)/n = |<e^{-2 pi i S}>|^2 should
decay like (log T)^{-2} if S at zeros is Gaussian with Selberg's variance.
NULL P: m does NOT decay (slope 0 in log-log), i.e. the tau=1 line carries O(1) mass and
        could in principle power a band-limited certificate.
"""
import numpy as np, os
from math import log, pi, sqrt, exp
HERE = os.path.dirname(os.path.abspath(__file__))
def theta(t):
    t = np.asarray(t, float)
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)
print("="*100)
print("P.  DECAY LAW of the tau=1 delta mass  m = |<e^{-2 pi i S}>|^2, and the certificate budget.")
print("="*100)
print(f"  {'T':>9}{'Tc':>12}{'log Tc':>9}{'n':>7}{'K(1)':>10}{'m':>10}{'var S':>9}"
      f"{'m_gauss':>10}{'m/m_gauss':>11}")
X=[];Y=[]
for T in (1e3,1e4,1e5,1e6,1e7):
    g=np.load(os.path.join(HERE,f"att010_zeros_{T:.0e}.npy"))
    u=theta(g)/np.pi; u-=u[0]; n=len(u)
    k1=abs(np.exp(2j*np.pi*u).sum())**2/n
    r=np.arange(n)-u; r-=r.mean(); v=r.var()
    Tc=(g[0]+g[-1])/2; m=k1/n; mg=exp(-4*pi*pi*v)
    print(f"  {T:>9.0e}{Tc:>12.1f}{log(Tc):>9.4f}{n:>7}{k1:>10.3f}{m:>10.5f}{v:>9.5f}"
          f"{mg:>10.5f}{m/mg:>11.4f}")
    X.append(log(log(Tc))); Y.append(log(m))
A=np.polyfit(X,Y,1)
print(f"\n  log-log fit  m ~ (log T)^p :  p = {A[0]:+.3f}   (Gaussian+Selberg predicts p = -2)")
print(f"  extrapolated mass at T=10^30 (log T=69.1): {exp(A[1])*69.1**A[0]:.2e}"
      f"   [with p=-2 exactly and the 1e7 anchor: {0.00359*(16.118/69.1)**2:.2e}]")
print("\n  CERTIFICATE BUDGET.  A band-limited pair-correlation certificate reads")
print("  int K(tau) hhat(tau) dtau over |tau|<=lambda.  A point mass at tau=1 contributes")
print("  m*hhat(1), NOT K(1).  Zeta23 needs +0.015 in the on-line proportion to pass 0.68185.")
print(f"  Available at T=1e7: m = {0.00359:.5f}  (and hhat(1)=0 for any hhat that vanishes at")
print("  the band edge, which the optimal ones do).  Ramp mass on (0,1) for scale: 0.500.")
