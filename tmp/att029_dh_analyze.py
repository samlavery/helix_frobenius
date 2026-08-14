"""ATTEMPT 029, stage 5b -- DH analysis with the FE MIRROR PARTNERS restored.

Stage 5 seeded Newton only to the RIGHT of the line, so it found 137 zeros with beta > 1/2 and
only 21 of their partners.  The self-dual FE makes the partner exact: if (beta, gamma) is a
zero then so is (1-beta, gamma).  Restoring them:

CENSUS GATE (the whole stage rests on it):  3032 on-line + 2*137 off-line = 3306
against delta theta_f/pi = 3306.53 over t in [100,3100].  Slack 0.53, i.e. |S| < 1.  COMPLETE.

Measured objects, all on the SAME certified-complete zero set:
   a_on (n)  = (2pi/W) sum_{on-line}  n^{i gamma}
   a_all(n)  = a_on + (2pi/W) * 2 * sum_{pairs} n^{i gamma}          [every ordinate, no betas]
   a_bet(n)  = a_on + (2pi/W) * sum_{pairs} 2 cosh(d log n) n^{i gamma}   [Landau's actual sum]
   prediction  -Lambda_f(n)/sqrt n,  Lambda_f from the recursion a_n log n = sum_{d|n} Lambda_f(d) a_{n/d}.
"""
import numpy as np, math, sys
from math import log, sqrt, pi
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from att029_dh_offline import lam_f_dh, theta_f, vonm, CHI4RE, T0, T1

def P(*a): print(*a); sys.stdout.flush()
TMP = '/Users/samuellavery/work/helix_frobenius/tmp/'

if __name__ == "__main__":
    P(__doc__)
    on = np.load(TMP+'att029_dh_on.npy'); r = np.load(TMP+'att029_dh_off.npy')
    W = T1-T0
    right = r[r.real > 0.5]; left = r[r.real < 0.5]
    # dedupe the pairs by ordinate: the 21 left ones must be mirrors of 21 of the 137
    gr = np.sort(right.imag); gl = np.sort(left.imag)
    matched = sum(1 for g in gl if np.min(np.abs(gr-g)) < 1e-5)
    P(f"pairs: {len(right)} with beta>1/2, {len(left)} with beta<1/2, of which {matched} are"
      f" mirrors of a located right partner (so {len(left)-matched} unmatched)")
    gam_p = right.imag; d_p = right.real - 0.5
    Npair = len(gam_p); Noff = 2*Npair; Non = len(on); Nth = (theta_f(T1)-theta_f(T0))/pi
    P(f"CENSUS GATE: on-line {Non} + 2*{Npair} = {Non+Noff} vs delta theta_f/pi = {Nth:.2f}"
      f"   slack {Nth-Non-Noff:+.2f}  -> {'COMPLETE' if abs(Nth-Non-Noff) < 2 else 'INCOMPLETE'}")
    f_off = Noff/Nth
    P(f"   f_off = {f_off:.4f};  displacement d: median {np.median(d_p):.4f} mean {d_p.mean():.4f}"
      f" min {d_p.min():.4f} max {d_p.max():.4f}")
    k = 2*pi/W
    floor_all = k*sqrt(Non+Noff); floor_off = k*sqrt(Noff)
    P(f"   incoherent floors: all zeros {floor_all:.4f}, off-line only {floor_off:.4f}\n")
    LF = lam_f_dh(200)
    P(f"{'n':>4}{'n%5':>4}{'Lam_f':>9}{'pred':>9} | {'a_on':>8}{'a_offO':>8}{'a_offB':>8}"
      f"{'a_all':>8}{'a_bet':>8} | {'on/p':>7}{'all/p':>7}{'bet/p':>7} | {'|a_off|/fl':>11}")
    rows = []
    for n in range(2, 80):
        if LF[n] == 0 or abs(LF[n]) < 1e-9: continue
        ln = log(n); e = np.exp(1j*gam_p*ln)
        a_on = k*np.exp(1j*on*ln).sum()
        a_oO = k*2*e.sum()
        a_oB = k*(2*np.cosh(d_p*ln)*e).sum()
        a_all = a_on + a_oO; a_bet = a_on + a_oB
        pred = -LF[n]/sqrt(n)
        rows.append((n, a_on.real/pred, a_all.real/pred, a_bet.real/pred, abs(a_oO)/floor_off,
                     a_on, a_oO, a_bet, pred))
        P(f"{n:>4}{n%5:>4}{LF[n]:>9.4f}{pred:>9.4f} | {a_on.real:>8.4f}{a_oO.real:>8.4f}"
          f"{a_oB.real:>8.4f}{a_all.real:>8.4f}{a_bet.real:>8.4f} | "
          f"{a_on.real/pred:>7.3f}{a_all.real/pred:>7.3f}{a_bet.real/pred:>7.3f} | "
          f"{abs(a_oO)/floor_off:>11.2f}")
    R = np.array([(x[1], x[2], x[3], x[4]) for x in rows])
    big = np.array([abs(x[8]) > 0.25 for x in rows])       # lines the window can actually resolve
    P(f"\nMedians over ALL {len(rows)} lines with Lambda_f != 0:")
    P(f"   a_on /pred = {np.median(R[:,0]):.4f}   a_all/pred = {np.median(R[:,1]):.4f}"
      f"   a_bet/pred = {np.median(R[:,2]):.4f}")
    P(f"Medians over the {big.sum()} lines with |pred| > 0.25 (resolvable above the {floor_all:.3f} floor):")
    P(f"   a_on /pred = {np.median(R[big,0]):.4f}  => Delta_online = {np.median(R[big,0])-1:+.4f}"
      f"   [Fact 3 predicts {-f_off:+.4f}]")
    P(f"   a_all/pred = {np.median(R[big,1]):.4f}  => Delta_all    = {np.median(R[big,1])-1:+.4f}")
    P(f"   a_bet/pred = {np.median(R[big,2]):.4f}  => Delta_beta   = {np.median(R[big,2])-1:+.4f}")
    P(f"\nNULL-6 (Landau unusable for DH): a_bet/pred = {np.median(R[big,2]):.4f}"
      f"  -> {'NULL HOLDS' if abs(np.median(R[big,2])-1) > 0.15 else 'NULL REFUTED: Landau HOLDS for DH with the true Lambda_f'}")
    P(f"NULL-5 (no FE suppression): |Delta_all| / |Delta_online| = "
      f"{abs(np.median(R[big,1])-1)/abs(np.median(R[big,0])-1):.3f}"
      f"  -> {'NULL HOLDS' if abs(np.median(R[big,1])-1)/abs(np.median(R[big,0])-1) > 0.7 else 'NULL REFUTED: the FE suppresses the ordinate deficit'}")
    P(f"NULL-7 (off-line zeros carry no arithmetic): median |a_off|/floor over resolvable lines"
      f" = {np.median(R[big,3]):.2f}  (3.0 = 3 sigma)")
    P(f"   -> {'NULL HOLDS' if np.median(R[big,3]) < 3 else 'NULL REFUTED: the off-line zeros are COHERENT'}")
    # the n = 2,3 mod 5 anomaly
    an = [x for x in rows if x[0] % 5 in (2,3) and vonm(x[0]) > 0 and x[0] < 40]
    P(f"\nThe n = 2,3 mod 5 anomaly (bisector law predicts NO line; true Lambda_f predicts one):")
    P(f"  {'n':>4}{'a_on':>9}{'a_off':>9}{'a_all':>9}{'a_bet':>9}{'pred_f':>9}{'bet/pred':>10}")
    for x in an:
        P(f"  {x[0]:>4}{x[5].real:>9.4f}{x[6].real:>9.4f}{(x[5]+x[6]).real:>9.4f}"
          f"{x[7].real:>9.4f}{x[8]:>9.4f}{x[3]:>10.3f}")
