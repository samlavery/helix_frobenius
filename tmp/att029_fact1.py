"""ATTEMPT 029, stage 6 -- DIRECT test of FACT 1 (the functional equation kills the first order)
on REAL data with MAXIMALLY COHERENT displacements.

Stage 3 established that zeta-prime's arithmetic is carried entirely by the betas: the
ordinate-only Landau sum is 8% of the prediction, the beta-weighted sum is 101%.  That makes
zeta-prime's (d_j, gamma_j) the most adversarial data available -- the displacement is perfectly
correlated with the arithmetic phase.  So: take those SAME pairs and ask what an FE would do.

CONSTRUCTION.  For each zeta-prime zero (1/2+d_j, gamma_j) and each scale s in (1, 1/2, 1/4, ...):
   UNPAIRED (no FE, what zeta-prime actually is):   A_unp(s) = sum_j r^{s d_j} r^{i gamma_j}
   FE-PAIRED (each zero replaced by 1/2 +- s d_j at the SAME ordinate, as a self-dual FE forces):
                                                    A_par(s) = sum_j 2 cosh(s d_j log r) r^{i gamma_j}
   ORDINATE-ONLY (what the instrument sees):        A_ord     = sum_j r^{i gamma_j}   (x2 when paired)
   DEFICIT      Delta_unp(s) = A_ord/A_unp(s) - 1 ,  Delta_par(s) = A_ord/(A_par(s)/2) - 1.

PRE-REGISTERED PREDICTIONS (Facts 1 and 2, before running):
   |Delta_unp(s)| ~ s^1   (first order: 1 - r^{d} = -d log r + O(d^2))
   |Delta_par(s)| ~ s^2   (second order: 2 - 2cosh(d log r) = -(d log r)^2 + O(d^4))
   measured by the slope of log|Delta| against log s.
NULL-8: the two slopes are the SAME, i.e. the FE pairing does not suppress the deficit and
   Fact 1 is wrong.  Then the ordinate deficit is a first-order location readout for
   FE-symmetric functions too, and the route is OPEN.

CONTROL (must fail by MISSING STRUCTURE): shuffle the d_j against the gamma_j, destroying the
   correlation that carries the arithmetic.  Both deficits must then collapse toward the
   incoherent floor -- this shows the signal is the CORRELATION, not the mere presence of
   off-line displacement.
"""
import numpy as np, math, sys
from math import log, sqrt, pi
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from att014_afe import zprime_coeffs

def P(*a): print(*a); sys.stdout.flush()
TMP = '/Users/samuellavery/work/helix_frobenius/tmp/'
SC = (1.0, 0.5, 0.25, 0.125, 0.0625)

if __name__ == "__main__":
    P(__doc__)
    C = zprime_coeffs(2.2)
    freqs = sorted(((float(k), v) for k, v in C.items() if 0.3 < log(float(k)) < 2.0 and abs(v) > 0.5),
                   key=lambda z: z[0])
    for tag, fn in (('1e5','att014_zpz_1e+05.npy'), ('1e6','att014_zpz_1e+06.npy')):
        z = np.load(TMP+fn); gam = z.imag; d = z.real - 0.5
        W = gam.max()-gam.min()
        P(f"\n### zeta-prime T={tag}: {len(z)} zeros, W={W:.0f}, median d = {np.median(d):.4f}")
        P(f"  {'r':>8}" + "".join(f"{'|Dunp| s='+str(s):>16}" for s in SC))
        Uslope, Pslope, ratio1 = [], [], []
        for x, c in freqs:
            lr = log(x); e = np.exp(1j*gam*lr)
            Aord = e.sum()
            du, dp = [], []
            for s in SC:
                Au = (e*np.exp(s*d*lr)).sum()
                Ap = (e*np.cosh(s*d*lr)).sum()
                du.append(abs(Aord/Au - 1)); dp.append(abs(Aord/Ap - 1))
            du = np.array(du); dp = np.array(dp)
            ls = np.log(np.array(SC))
            su = np.polyfit(ls, np.log(du), 1)[0]; sp = np.polyfit(ls, np.log(dp), 1)[0]
            Uslope.append(su); Pslope.append(sp); ratio1.append(dp[0]/du[0])
            P(f"  {x:>8.4f}" + "".join(f"{v:>16.5f}" for v in du) + f"   slope {su:+.3f}")
            P(f"  {'  paired':>8}" + "".join(f"{v:>16.5f}" for v in dp) + f"   slope {sp:+.3f}"
              f"   suppression at s=1: {dp[0]/du[0]:.4f}")
        P(f"  -> UNPAIRED  median slope d log|Delta|/d log s = {np.median(Uslope):+.3f}   [predicted +1]")
        P(f"  -> FE-PAIRED median slope                      = {np.median(Pslope):+.3f}   [predicted +2]")
        P(f"  -> FE suppression factor at s=1 (real zeta-prime displacements):"
          f" median {np.median(ratio1):.4f}")
        P(f"  NULL-8 refuted iff the paired slope is ~2 and the unpaired ~1.")
        # ---- control: destroy the d <-> gamma correlation
        rng = np.random.default_rng(29)
        dsh = rng.permutation(d)
        du0, dp0 = [], []
        for x, c in freqs:
            lr = log(x); e = np.exp(1j*gam*lr); Aord = e.sum()
            du0.append(abs(Aord/((e*np.exp(dsh*lr)).sum()) - 1))
            dp0.append(abs(Aord/((e*np.cosh(dsh*lr)).sum()) - 1))
        P(f"  CONTROL (d shuffled against gamma, structure removed):"
          f"  unpaired median |Delta| {np.median(du0):.5f}  paired {np.median(dp0):.5f}"
          f"   [unshuffled: {np.median([abs(np.exp(1j*gam*log(x)).sum()/((np.exp(1j*gam*log(x))*np.exp(d*log(x))).sum())-1) for x,_ in freqs]):.5f}]")
