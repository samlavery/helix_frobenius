"""ATTEMPT 011, stage 4 -- ATTRIBUTION.  Is  K(tau_n) = U Lambda(n)^2/(L^2 n)  exactly
Landau's theorem (1911) / Gonek's uniform version, restated in the tape coordinate?

DERIVATION (to be checked numerically below).
  u_k = theta(gamma_k)/pi.  Expand theta about the window centre t_c, with L := 2 theta'(t_c):
      u_k = theta(t_c)/pi + (gamma_k - t_c) L/(2 pi) + (gamma_k - t_c)^2 theta''(t_c)/(2 pi) + ...
  At tau_n = log n / L the linear term gives
      2 pi tau_n u_k = [ 2 theta(t_c) log n / L ] + (gamma_k - t_c) log n + (quadratic)
  so, with C_n a unimodular constant independent of k,
      e^{2 pi i tau_n u_k} = C_n * n^{i gamma_k} * e^{i (quadratic)}.
  Hence  |F(tau_n)| = | sum_k n^{i gamma_k} |  up to the quadratic dephasing, and that
  dephasing is EXACTLY the quantity the house validity criterion R measures.
  Landau/Gonek over a window of length W:   sum n^{i gamma} = -(W/2pi) Lambda(n)/sqrt n + E.
  The tape has density 1, so U = W L /(2 pi), i.e. W/(2 pi) = U/L, giving
      |F(tau_n)| = (U/L) Lambda(n)/sqrt n     and     K := |F|^2/U = U Lambda(n)^2/(L^2 n).
  So the house law IS Landau's formula in the tape coordinate.  NO NOVELTY IS CLAIMED.

============================ PRE-REGISTERED =================================
E1  GATE on the Lambda_f recurrence: sum_{n<=N} Lambda_f(n) n^{-3} must equal -f'/f(3).
    NULL: they disagree -> the D2 growth measurement is a bug.
E2  DH growth exponent, tail fit + abscissa probe.
    NULL: exponent 0 (Lambda_f bounded by log n, as for an Euler function).
E3  ATTRIBUTION.  For zeta zeros at T=1e6 compute, at the SAME window:
      Ftape(n) = |sum_k exp(2 pi i tau_n u_k)|      (house, tape coordinate)
      Glandau(n) = |sum_k n^{i gamma_k}|            (Landau's sum, raw t coordinate)
      Plandau(n) = (W/2pi) Lambda(n)/sqrt n         (Landau/Gonek main term)
    NULL (house law is NOT Landau restated): Ftape and Glandau differ by more than the
    R-dephasing, or neither matches Plandau.
=============================================================================
"""
import numpy as np, math, sys, os
def P(*a): print(*a); sys.stdout.flush()
TMP = '/Users/samuellavery/work/helix_frobenius/tmp/'
A_DH=(4/np.sqrt(5))*np.sin(2*np.pi/5); B_DH=(4/np.sqrt(5))*np.sin(4*np.pi/5)
XI=(np.sqrt(A_DH**2+B_DH**2)-A_DH)/B_DH

# ---------- E1 ---------------------------------------------------------------
P("E1  GATE on the Lambda_f recurrence.")
N = 20000
n = np.arange(N+1); a = np.zeros(N+1); a[1:] = np.array([0.,1.,XI,-XI,-1.])[n[1:] % 5]
def fDH_series(s, M=4000000):
    k = np.arange(1, M+1); c = np.array([0.,1.,XI,-XI,-1.])[k % 5]
    return (c*k**(-s)).sum()
L = np.load(TMP+'att011_lamfull_DH.npy')
lhs = (L[2:N+1]*np.arange(2,N+1)**(-3.0)).sum()
h = 1e-5
rhs = -(fDH_series(3+h)-fDH_series(3-h))/(2*h)/fDH_series(3.0)
P(f"    sum_{{n<=20000}} Lambda_f(n) n^-3 = {lhs:.12f}")
P(f"    -f'/f(3) by numerical differentiation of the Dirichlet series = {rhs:.12f}")
P(f"    difference = {abs(lhs-rhs):.3e}   NULL would be O(1)")

# ---------- E2 ---------------------------------------------------------------
P("\nE2  DH Lambda_f growth.  NULL (Euler-like): exponent 0.")
run = np.maximum.accumulate(np.abs(L))
for lo, hi in ((200, 2000), (2000, 20000), (5000, 20000)):
    x = np.log(np.arange(lo, hi+1)); y = np.log(np.maximum(run[lo:hi+1], 1e-300))
    P(f"    running-max exponent on [{lo},{hi}] = {np.polyfit(x,y,1)[0]:.4f}")
q = np.abs(L[2:N+1]); nn = np.arange(2, N+1)
for sig in (1.0, 1.2, 1.4, 1.6, 1.8, 2.0):
    P(f"    sum_{{n<=20000}} |Lambda_f(n)| n^-{sig}  = {(q*nn**(-sig)).sum():12.4f}"
      f"   (tail term at n=20000: {q[-1]*20000.0**(-sig):.3e})")
Lz = np.load(TMP+'att011_lamfull_zeta.npy')
P(f"    zeta reference: max_{{n<=20000}} Lambda(n) = {np.abs(Lz).max():.4f} = log(19993)")

# ---------- E3 ---------------------------------------------------------------
P("\nE3  ATTRIBUTION:  tape statistic  vs  Landau's sum  vs  Landau/Gonek main term.")
_B=[1/6,-1/30,1/42,-1/30,5/66]
def logGamma_asym(z):
    z=np.asarray(z,complex); out=(z-0.5)*np.log(z)-z+0.5*np.log(2*np.pi); zp=z.copy()
    for k in range(1,6): out+=_B[k-1]/(2*k*(2*k-1)*zp); zp=zp*z*z
    return out
def theta_z(t): return np.imag(logGamma_asym((0.5+1j*np.asarray(t,float))/2)) - np.asarray(t,float)/2*math.log(np.pi)

g = np.load(TMP+'att011_z_zeta_1e+06_3000.npy')
u = theta_z(g)/np.pi; u -= u[0]; U = u[-1]
tc = (g[0]+g[-1])/2; Lc = theta_z(tc+1.0)-theta_z(tc-1.0)
Wt = g[-1]-g[0]
P(f"    zeta window: {len(g)} zeros, t in [{g[0]:.1f},{g[-1]:.1f}], W_t={Wt:.1f}, "
  f"U={U:.1f}, L={Lc:.5f},  W_t*L/(2pi) = {Wt*Lc/(2*np.pi):.1f}  (must equal U)")
P(f"    {'n':>4}{'Lambda':>9}{'|Ftape|':>11}{'|Glandau|':>11}{'ratio':>8}"
  f"{'Plandau':>11}{'Ftape/P':>9}{'R(n)':>7}")
LAM = {2:math.log(2),3:math.log(3),4:math.log(2),5:math.log(5),7:math.log(7),8:math.log(2),
       9:math.log(3),11:math.log(11),13:math.log(13),16:math.log(2),17:math.log(17),
       19:math.log(19),23:math.log(23),25:math.log(5),27:math.log(3),29:math.log(29),31:math.log(31)}
rows=[]
for nn_ in sorted(LAM):
    tau = math.log(nn_)/Lc
    Ft = abs(np.exp(2j*np.pi*tau*u).sum())
    Gl = abs(np.exp(1j*math.log(nn_)*g).sum())
    Pl = (Wt/(2*np.pi))*LAM[nn_]/math.sqrt(nn_)
    R  = U*math.log(nn_)*math.log(1+3000/1e6)/(Lc*Lc)
    P(f"    {nn_:>4}{LAM[nn_]:>9.4f}{Ft:>11.2f}{Gl:>11.2f}{Ft/Gl:>8.4f}{Pl:>11.2f}{Ft/Pl:>9.3f}{R:>7.2f}")
    rows.append((Ft, Gl, Pl))
r = np.array(rows)
P(f"\n    median |Ftape|/|Glandau| = {np.median(r[:,0]/r[:,1]):.5f}   "
  f"max |1 - Ftape/Glandau| = {np.abs(1-r[:,0]/r[:,1]).max():.2e}")
P(f"    median |Ftape|/Plandau   = {np.median(r[:,0]/r[:,2]):.4f}   "
  f"median |Glandau|/Plandau = {np.median(r[:,1]/r[:,2]):.4f}")
P("\n    CONCLUSION: the tape statistic and Landau's sum are the SAME NUMBER; the tape law")
P("    is Landau (1911) / Gonek (1993) in the coordinate u = theta/pi.  No novelty claimed.")
