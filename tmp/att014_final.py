"""ATTEMPT 014, final -- (a) re-do the T=1e7 tape block with the repaired (denser-seeded)
zeta' zero set, (b) the sensitivity calculation that names the blocker.

BLOCKER ARITHMETIC.  Landau's theorem is unconditionally about sum_rho x^rho.  The tape
instrument (att010) measures sum_gamma x^{i gamma}.  They agree iff every beta = 1/2, so the
att010 law IS the RH form of Landau.  How sensitive is the discrepancy to off-line zeros?
For a self-dual FE object the off-line zeros come in pairs beta = 1/2 +- delta at the same
gamma, so each pair contributes 2 cosh(delta log x) to the weighted sum and 2 to the unweighted:
      |A_u/A_w| = 1 / cosh(delta log x)   if ALL zeros are off-line at +-delta (coherent case),
      |A_u - A_w| ~ 2 sqrt(N_off) (cosh(delta log x) - 1)   (incoherent case).
The measured scatter of obs/pred for zeta is ~3%, so that is the detection threshold.
"""
import numpy as np, math, sys
from att014_afe import theta, zprime_coeffs, zeta_coeffs
def P(*a): print(*a); sys.stdout.flush()
TWOPI = 2*math.pi

C = zprime_coeffs(2.3); Z = zeta_coeffs(2.3)
LAM = [(math.log(float(r)), str(r), a*a*math.exp(-math.log(float(r))))
       for r, a in sorted(C.items(), key=lambda kv: float(kv[0])) if 0.2 < math.log(float(r)) <= 1.65]
ZL = {round(math.log(n), 12): (n, L*L/n) for n, L in Z.items()}

g = np.load("att010_zeros_1e+07.npy"); r = np.load("att014_zpz_1e+07.npy")
t0, t1 = float(g[0]), float(g[-1]); tc = (t0+t1)/2; W = t1-t0
L = math.log(tc/TWOPI); rho = math.log(tc/(4*math.pi))/L
uz = theta(g)/np.pi; uz -= uz[0]; Uz = uz[-1]
o = np.argsort(r.imag); gp = r.imag[o]; bp = r.real[o]-0.5
up = theta(gp)/np.pi; up -= up[0]; Up = up[-1]
P(f"T=1e7 REPAIRED  zeta zeros {len(g)}  zeta' zeros {len(r)}  ratio {len(r)/len(g):.5f}  "
  f"n/U {len(up)/Up:.5f}  rho_pred {rho:.5f}  [NULL 1.0]  Berndt {W/TWOPI*math.log(tc/(4*math.pi)):.1f}")
P(f"  beta'-1/2 median {np.median(bp):.5f}  mean {bp.mean():.5f}  max {bp.max():.4f}  "
  f"#(beta'>1)={int((bp>0.5).sum())}")
P(f"  {'lambda':>9}{'r':>7}{'tau':>8} | {'K_zp':>9}{'pred':>9}{'H1 o/p':>8} | {'Kw_zp':>9}{'H2 o/p':>8} | "
  f"{'K_zeta':>9}{'o/p':>7}")
r1, r2 = [], []
for lam, rs, A in LAM:
    tau = lam/L
    E = np.exp(2j*np.pi*tau*up)
    kp = abs(E.sum())**2/len(up)
    kw = abs((E*np.exp(lam*bp)).sum())**2/len(up)
    kz = abs(np.exp(2j*np.pi*tau*uz).sum())**2/len(uz)
    pred = Up*Up*A/(L*L*len(up))
    zz = ZL.get(round(lam, 12))
    predz = Uz*Uz*zz[1]/(L*L*len(uz)) if zz else float('nan')
    r1.append(kp/pred); r2.append(kw/pred)
    zs = f"{kz:>9.2f}{kz/predz:>7.2f}" if zz else f"{kz:>9.2f}{'--':>7}"
    P(f"  {lam:>9.5f}{rs:>7}{tau:>8.4f} | {kp:>9.2f}{pred:>9.2f}{kp/pred:>8.2f} | {kw:>9.2f}{kw/pred:>8.2f} | {zs}")
r1 = np.array(r1); r2 = np.array(r2)
P(f"  -> H1 (unweighted) median {np.median(r1):.3f}  IQR {np.percentile(r1,25):.3f}-{np.percentile(r1,75):.3f}")
P(f"  -> H2 (beta'-weighted) median {np.median(r2):.3f}  IQR {np.percentile(r2,25):.3f}-{np.percentile(r2,75):.3f}")
P(f"  measured E[2^(beta'-1/2)] = {np.mean(2.0**bp):.4f}  vs  2^median = {2**np.median(bp):.4f} "
  f"(the far-right tail, not the median, sets the weighted sum)")
P("")
P("BLOCKER: sensitivity of the unweighted/weighted ratio to off-line zeros (x = 2, n = 4000 zeros)")
P(f"  {'delta':>8}{'coherent A_u/A_w':>20}{'N_off needed (incoherent, 3% at 3% thresh)':>46}")
n_win = 4000.0; thr = 0.03*(n_win/L)*math.log(2)/math.sqrt(2)   # 3% of the predicted |A_w| at x=2
for d in (0.001, 0.01, 0.05, 0.1, 0.2, 0.3):
    coh = 1/math.cosh(d*math.log(2))
    need = (thr/(2*(math.cosh(d*math.log(2))-1)))**2
    P(f"  {d:>8.3f}{coh:>20.6f}{need:>46.3e}")
P(f"  window holds only {n_win:.0f} zeros, so 'N_off needed' above ~4e3 is unreachable: "
  f"the detector is blind for delta < 0.3.")
P(f"  (predicted |A_w| at x=2 is (W/2pi)Lambda(2)/sqrt2 = {(n_win/L)*math.log(2)/math.sqrt(2):.1f}; "
  f"3% of it is {thr:.2f})")
