"""ATTEMPT 030, stage 3 -- BASIS-FREE instruments, to separate mechanism (R) from mechanism (W).

Stage 1 showed the attempt-015 crossing point n* moves 174 -> 90 -> 46 -> 35 as the window
ratio goes 1.5 -> 2 -> 3 -> 4, and 90 -> 53 -> 151 across detrend bases.  So the number "138"
is not an invariant of the data: it is a property of {dyadic window} x {4-parameter detrend}.
Two instruments here carry NO window fit at all.

 (i) FINITE-DIFFERENCE R^2.  Delta^k annihilates every polynomial of degree < k in n exactly.
     R2_k = 1 - sum (D^k Y - D^k O)^2 / sum (D^k Y)^2 on the same windows, k = 2 and 4.
     Zero fitted parameters, zero basis choice.

 (ii) MATCHED FILTER at the Szego tone, with the amplitude PREDICTED EXACTLY (DC-first).
     Szego 8.22.1 gives, for lambda_n^{arith,chi} and each prime power m,
         contribution = a_m n^{1/4} cos(omega_m sqrt n - 3 pi/4),
         omega_m = 2 sqrt(log m),   a_m = Lambda(m) chi(m) / (sqrt(pi) sqrt(m) (log m)^{3/4}),
     with an overall minus sign from lambda^arith = -sum_m ... .  So
         A_m := (2/V) * sum_window  Hann * [Y_n / n^{1/4}] e^{-i omega_m sqrt n} d(sqrt n)
     must satisfy |A_m| -> |a_m| and arg A_m -> -3pi/4 + pi (the minus sign) = +pi/4.
     For m=2: |a_2| = log2/(sqrt(pi) sqrt2 (log2)^{3/4}) = 0.36397.  PHASE IS THE STRONGER TEST.
     The turn-on is read off as the smallest sqrt(n) at which |A_2|/|a_2| first exceeds 1/2
     AND the phase is within 0.5 rad of the prediction.

STATED NULL (pre-registered)
  N5  the difference-R^2 shows NO threshold at all -- i.e. R2_k is already > 0.5 well below
      n = 138 on zeta, so the "switch-on" was entirely the window/detrend absorption.
  N6  the matched-filter turn-on point does not order as gamma_1(chi)^2 log m_1
      (zeta 138.5 > chi_-3 44.8 > chi_5 30.6 > chi_8 26.4), within the stated resolution.
RESOLUTION, computed BEFORE running: a Hann window of length V in sqrt(n) has Rayleigh
  resolution 2pi/V and a main lobe of half-width 2*(2pi/V).  To keep DC leakage out of
  omega_2 = 1.6651 we need 2*(2pi/V) < 1.6651, i.e. V > 7.55.  We use V = 8.0, which localises
  the turn-on only to +-4 in sqrt(n), i.e. a factor ~3 in n near n=100.  This is a hard limit:
  the four predicted turn-ons sit at sqrt(n) = 11.77, 6.69, 5.53, 5.14, a span of 6.6, so the
  filter can separate zeta from the three characters but NOT the three characters from each
  other.  Said in advance so it cannot be spun afterwards.
"""
import sys, os, math, time
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from att030_zeta import prime_powers, laguerre1_dot, laguerre0, line_prediction_zeta, score
from att030_dirichlet import CHARS, chi_line_prediction
def P(*a): print(*a); sys.stdout.flush()

def diffR2(Y, O, lo, hi, k):
    y = np.diff(Y[lo-1:hi], n=k); o = np.diff(O[lo-1:hi], n=k)
    return 1 - np.sum((y-o)**2)/np.sum(y**2), np.corrcoef(y, o)[0, 1]

def matched(Y, omega, V=8.0, step=0.25, nmax=2500):
    """|A|, arg A on Hann windows of length V in sqrt(n), centred at v0."""
    n = np.arange(1, len(Y)+1, dtype=float)
    v = np.sqrt(n); g = Y/n**0.25
    out = []
    v0 = 3.0
    while v0 + V <= math.sqrt(nmax):
        k = (v >= v0) & (v <= v0+V)
        if k.sum() > 30:
            vv = v[k]; gg = g[k]
            w = 0.5 - 0.5*np.cos(2*math.pi*(vv-v0)/V)
            dv = np.gradient(vv)
            A = 2*np.sum(w*gg*np.exp(-1j*omega*vv)*dv)/(V*0.5)
            out.append((v0+V/2, abs(A), np.angle(A)))
        v0 += step
    return np.array(out)

if __name__ == "__main__":
    t0 = time.time(); P(__doc__); P("="*104)
    NMAX = 2500
    names = ['zeta'] + list(CHARS)
    Ys = {'zeta': np.load(os.path.join(HERE, 'att030_Yzeta_r997.npy'))[:NMAX]}
    Os = {'zeta': line_prediction_zeta(NMAX, 32)}
    for nm, (q, a, chi) in CHARS.items():
        Ys[nm] = np.load(os.path.join(HERE, f'att030_Y_{nm}.npy'))[:NMAX]
        Os[nm] = chi_line_prediction(NMAX, 32, q, chi)
    g1 = {'zeta': 14.134725141734693, 'chi_-3': 8.039737155681467,
          'chi_5': 6.648453344727715, 'chi_8': 4.899973997007036}
    m1 = {'zeta': 2, 'chi_-3': 2, 'chi_5': 2, 'chi_8': 3}

    wins = [(10,20),(20,40),(40,80),(80,160),(160,320),(320,640),(640,1250),(1250,2500)]
    for k in (2, 4):
        P(f"\n(i) FINITE-DIFFERENCE R^2, Delta^{k} (kills every polynomial of degree < {k}), "
          f"M = 32, NO fit")
        P(f"  {'window':>14}" + "".join(f"{n:>13}" for n in names))
        for lo, hi in wins:
            row = f"  [{lo:>4},{hi:>5}]"
            for nm in names:
                R2, _ = diffR2(Ys[nm], Os[nm], lo, hi, k); row += f"{R2:>13.4f}"
            P(row)

    P("\n  crossing point n* from Delta^2-R^2 (first dyadic-grid n with R2>=0.5, staying):")
    grid = np.unique(np.round(np.exp(np.linspace(math.log(10), math.log(1200), 200))).astype(int))
    for nm in names:
        got = None
        for n0 in grid:
            n1 = 2*n0
            if n1 > NMAX: break
            R2, _ = diffR2(Ys[nm], Os[nm], n0, n1, 2)
            if R2 >= 0.5:
                ok = all(diffR2(Ys[nm], Os[nm], int(n0*f), min(NMAX, int(2*n0*f)), 2)[0] >= 0.5
                         for f in (1.3, 1.8, 2.6) if int(2*n0*f) <= NMAX)
                if ok: got = n0; break
        pred = g1[nm]**2*math.log(m1[nm])
        P(f"    {nm:>8}  n*(Delta^2) = {str(got):>6}   gamma_1^2 log m_1 = {pred:7.1f}"
          f"   ratio = {(got/pred if got else float('nan')):.3f}")

    P("\n(ii) MATCHED FILTER at omega = 2 sqrt(log m_1), Hann V=8 in sqrt(n)")
    P("     predicted |a| and phase +pi/4 = 0.7854; obs/pred and phase reported vs window centre")
    for nm in names:
        m = m1[nm]; om = 2*math.sqrt(math.log(m))
        chi_m = 1.0 if nm == 'zeta' else CHARS[nm][2](m)
        a_pred = abs(math.log(m)/(math.sqrt(math.pi)*math.sqrt(m)*math.log(m)**0.75))
        M = matched(Ys[nm], om, 8.0, 0.5, NMAX)
        pred_v = math.sqrt(g1[nm]**2*math.log(m))
        P(f"\n   {nm}  m_1={m}  omega={om:.4f}  |a_pred|={a_pred:.4f} (chi(m_1)={chi_m:+.0f})"
          f"   predicted turn-on at sqrt(n) = {pred_v:.2f}  (n = {pred_v**2:.0f})")
        P(f"     {'sqrt n':>8}{'n':>8}{'|A|':>9}{'obs/pred':>10}{'arg A':>9}"
          f"{'|arg-pi/4|':>12}")
        for v0, aa, ph in M:
            if v0 > 30: break
            d = abs(((ph - math.pi/4 + math.pi) % (2*math.pi)) - math.pi)
            P(f"     {v0:>8.2f}{v0*v0:>8.0f}{aa:>9.4f}{aa/a_pred:>10.3f}{ph:>9.3f}{d:>12.3f}")
        hit = None
        for v0, aa, ph in M:
            d = abs(((ph - math.pi/4 + math.pi) % (2*math.pi)) - math.pi)
            if aa/a_pred >= 0.5 and d <= 0.5:
                hit = v0; break
        P(f"     TURN-ON (|A|/a>=0.5 and |arg-pi/4|<=0.5): sqrt(n) = {hit}   "
          f"n = {hit*hit if hit else None}")
    P(f"\n[{time.time()-t0:.0f}s] stage 3 done")
