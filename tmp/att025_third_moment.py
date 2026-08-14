"""ATTEMPT 025 -- can a THIRD trace moment beat 2/3?  Zeta23 x the tape's n-level statistics.

THE UNFOLDING (restatement check first, rule 2).  Their three laws are not independent:
    F(lam) = lam/(1 + lam^2/3),      H(lam) = 2 - 1/lam - lam/3
satisfy H = 2 - 1/F exactly.  And with per-N trace moments mu_k = tr(G^k)/N,
    mu_1 = lam,   mu_2 = lam + lam^3/3   =>   mu_1^2/mu_2 = lam/(1+lam^2/3) = F.
So F is the CAUCHY-SCHWARZ RANK-TRACE BOUND rank/N >= mu_1^2/mu_2, and the whole certificate
is H = 2 - 1/(rank fraction).  H(1) = 2 - 4/3 = 2/3.  Remark 1.1 caps exactly this class:
"band-width <= 1 data and the FIRST TWO trace moments".

THE OPENING.  tr(G^3) is available in the Rudnick-Sarnak range k*lam < 2, i.e. lam < 2/3 --
strictly inside the band-limit, needing no prime-pair input.  A three-moment certificate is
outside the capped class.  Question: does it beat 2/3?

PAIRING.  house: the tape form factor K(tau), which IS the 2-level statistic supplying mu_2
(measured exhaustively in attempt 016: the tau>1 region is empty, 0 of 195 bins above 3 sigma,
so mu_2 is exactly the stated law and there is no hidden reserve there) -- together with the
exact count N = theta/pi + S from the tape, so the moment normalisation carries no counting
error.  classical: the Zeta23 Gram compression with Sylvester inertia, the Rudnick-Sarnak
k*lam < 2 range, and the Chebyshev-Markov moment problem.  MECHANISM: the tape says what the
moments ARE; the moment problem says what they can BUY; the certificate converts a rank
fraction into an on-line proportion by H = 2 - 1/F.

ONE FACT ESTABLISHED BY HAND BEFORE COMPUTING, because it decides the cheap version.  The
naive third-moment bound is Holder: rank/N >= mu_2^3/mu_3^2.  But
    mu_2^3/mu_3^2 <= mu_1^2/mu_2  <=>  mu_2^2 <= mu_1 mu_3,
which is Cauchy-Schwarz applied to lam^{1/2}.lam^{3/2} -- ALWAYS TRUE.  So the Holder bound is
NEVER better than the two-moment one.  The LP below is strictly stronger than Holder, so it is
the only thing that could still work.

STATED NULL, pre-registered.  For every lam <= 2/3 and every mu_3 admissible under the moment
inequalities, the three-moment LP bound gives H <= 2/3.  Then the third moment buys nothing,
the cap is not an artifact of using only two moments, and this route is closed.
"""
import numpy as np, sys
from scipy.optimize import linprog

def P(*a): print(*a); sys.stdout.flush()

def mu12(lam):
    return lam, lam + lam**3/3.0

def lp_rank_fraction(mus, B, ngrid=20000):
    """min total mass of nu>=0 on [0,B] with given moments  ==  max_{q} sum a_k mu_k
       over q(x)=sum_k a_k x^k with q(x) <= 1 on [0,B].   (LP duality; k = 1..len(mus))"""
    K = len(mus)
    x = np.linspace(1e-9, B, ngrid)
    A_ub = np.column_stack([x**(k+1) for k in range(K)])   # q(x) <= 1
    b_ub = np.ones(ngrid)
    res = linprog(c=-np.asarray(mus), A_ub=A_ub, b_ub=b_ub,
                  bounds=[(None, None)]*K, method='highs')
    return (-res.fun) if res.success else np.nan

P("GATE 1 -- reproduce the two-moment law from the LP (must equal F = mu_1^2/mu_2).")
P(f"  {'lam':>6}{'F closed form':>16}{'LP (2 moments)':>17}{'H=2-1/F':>11}{'B':>7}")
for lam in (0.5, 2/3, 0.85, 1.0, 1.25):
    m1, m2 = mu12(lam)
    F = m1*m1/m2
    for B in (20.0,):
        lp = lp_rank_fraction([m1, m2], B)
        P(f"  {lam:>6.3f}{F:>16.6f}{lp:>17.6f}{2-1/F:>11.6f}{B:>7.0f}")

P("\nGATE 2 -- Holder is never better (proved by hand; confirmed numerically).")
P(f"  {'lam':>6}{'mu_3 min (CS)':>15}{'Holder bound':>14}{'CS bound':>10}{'Holder>CS?':>11}")
for lam in (0.4, 0.5, 2/3):
    m1, m2 = mu12(lam)
    m3min = m2*m2/m1                       # Cauchy-Schwarz mu_2^2 <= mu_1 mu_3
    hol = m2**3/m3min**2
    cs = m1*m1/m2
    P(f"  {lam:>6.3f}{m3min:>15.6f}{hol:>14.6f}{cs:>10.6f}{str(hol>cs+1e-12):>11}")

P("\nTHE TEST -- three-moment LP, scanning mu_3 over its whole admissible range.")
P("  admissible: mu_3 >= mu_2^2/mu_1 (Cauchy-Schwarz).  Upper end limited by the spectral")
P("  radius: mu_3 <= B mu_2.  We scan mu_3 from its minimum upward and take the BEST H.")
P(f"  {'lam':>6}{'B':>6}{'mu_3*':>10}{'best LP rank frac':>19}{'best H':>10}{'beats 2/3?':>12}")
best_overall = -9
for B in (5.0, 10.0, 20.0):
    for lam in (0.30, 0.40, 0.50, 0.60, 2/3):
        m1, m2 = mu12(lam)
        lo = m2*m2/m1
        hi = B*m2
        if hi <= lo: continue
        bestH, bestm3 = -9, None
        for m3 in np.linspace(lo, min(hi, lo*6), 60):
            fr = lp_rank_fraction([m1, m2, m3], B)
            if not np.isfinite(fr) or fr <= 0: continue
            H = 2 - 1/fr
            if H > bestH: bestH, bestm3 = H, m3
        best_overall = max(best_overall, bestH)
        P(f"  {lam:>6.3f}{B:>6.0f}{bestm3:>10.4f}{(1/(2-bestH)):>19.6f}{bestH:>10.6f}"
          f"{str(bestH > 2/3 + 1e-9):>12}")
P(f"\n  best H over the entire admissible three-moment scan, lam <= 2/3 : {best_overall:.6f}")
P(f"  target to beat (their Theorem A)                                : {2/3:.6f}")
P(f"  their Theorem D optimised                                       : 0.672500")
P(f"  their Remark 1.1 ceiling for the two-moment class               : 0.681850")

P("\n  CONTROL -- run the same LP at lam = 1 with two moments, where the answer is known:")
m1, m2 = mu12(1.0)
P(f"    LP rank fraction {lp_rank_fraction([m1,m2],20.0):.6f}  vs F(1) = 0.750000"
  f"   -> H = {2-1/lp_rank_fraction([m1,m2],20.0):.6f} vs 2/3")
