"""ATTEMPT 015, stage 1 -- lambda_n EXACTLY, three independent routes.

    lambda_n = sum over nontrivial rho of [ 1 - (1 - 1/rho)^n ]        (Li 1997)

GENERATING FUNCTION (the frame everything below uses).  With  s = 1/(1-z),

    F(z) := log xi(1/(1-z)) = log xi(1) + sum_{n>=1} (lambda_n / n) z^n .

xi(s) = (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s), so F splits EXACTLY, with no estimate:

    F(z) = A(z) + G(z),
    A(z) = -log 2 - log(1-z) - (log pi)/(2(1-z)) + logGamma( 1/(2(1-z)) )     [ARCHIMEDEAN]
    G(z) = log[ (s-1) zeta(s) ]                                              [ARITHMETIC]

    lambda_n = lambda_n^arch + lambda_n^arith,  lambda_n^X = n [z^n] X(z).

ROUTE (i)  BOMBIERI-LAGARIAS.  d/ds log[(s-1)zeta(s)] = sum_j eta_j (s-1)^j, and
    G'(z) = sum_j eta_j z^j (1-z)^{-(j+2)}  =>  lambda_n^arith = sum_{k=1..n} C(n,k) eta_{k-1}.
eta_j is obtained EXACTLY from the Laurent/Stieltjes data of zeta at s=1 (Taylor coefficients
of (s-1)zeta(s), taken by Cauchy DFT at dps=80).  eta_0 = gamma_Euler is the check.

ROUTE (i-b)  DIRECT CAUCHY on F(z) on |z| = r.  The map z -> 1/(1-z) sends |z|<r to the disk
    |s - 1/(1-r^2)| < r/(1-r^2),
which is tangent to the critical line at s=1/2 and has |Im s| < r/(1-r^2).  For r = 0.8 that
is |Im s| < 2.23, a region where xi provably has no zero (first zero at 14.13).  So this route
is UNCONDITIONAL -- it does not assume anything about zeros.

ROUTE (ii)  DIRECT SUM OVER ZEROS.  On the critical line 1 - 1/rho = (t+i/2)/(t-i/2), so
    lambda_n = sum_{gamma>0} 4 sin^2( n arctan(1/(2 gamma)) )        [manifestly >= 0]
plus a tail beyond the last computed zero, evaluated by the EXACT smooth density theta'/pi
(not by the log(t/2pi)/2pi approximation) with the S-boundary term put in explicitly and the
remaining |int f' S| bounded by Trudgian's 2014 |S| bound.

STATED NULL for stage 1 (pre-registered): the three routes DISAGREE beyond their stated
error bars.  If that happens the attempt is BROKEN and stages 2-3 are void.
"""
import sys, time, math, os
import numpy as np
from mpmath import mp, mpf, mpc

def P(*a):
    print(*a); sys.stdout.flush()

NMAX = 40
mp.dps = 80

# ---------------------------------------------------------------- helpers
def dft_coeffs(fun, r, N, nmax, dps):
    """Taylor coefficients c_0..c_nmax of an analytic fun on |z|<=r, by DFT on the circle."""
    mp.dps = dps
    vals = []
    for j in range(N):
        z = mpc(r) * mp.expjpi(mpf(2*j)/N)
        vals.append(fun(z))
    cs = []
    for n in range(nmax+1):
        acc = mpc(0)
        for j in range(N):
            acc += vals[j] * mp.expjpi(mpf(-2*j*n)/N)
        cs.append((acc / N) / mpf(r)**n)
    return cs

# ---------------------------------------------------------------- route (i): eta_j
def eta_constants(J, R=mpf(2), N=256, dps=80):
    """eta_0..eta_J from the Taylor expansion of (s-1)zeta(s) at s=1.
       (s-1)zeta(s) is ENTIRE, so the Cauchy DFT is valid for any radius R."""
    mp.dps = dps
    f = lambda w: (w) * mp.zeta(1 + w) if w != 0 else mpf(1)
    a = dft_coeffs(lambda w: (w * mp.zeta(1+w)) if abs(w) > 0 else mpf(1), R, N, J+2, dps)
    # a[k] = Taylor coeffs of (s-1)zeta(s) at s=1, a[0] = 1
    # b = log of that series
    K = J + 2
    b = [mpf(0)]*(K+1)
    # log(1 + u) with u = sum_{k>=1} a[k] w^k, via  b' = a'/a  (series division)
    # do it by: b_n = a_n - (1/n) sum_{k=1}^{n-1} k b_k a_{n-k}
    for n in range(1, K+1):
        acc = a[n]
        for k in range(1, n):
            acc -= mpf(k)*b[k]*a[n-k]/mpf(n)
        b[n] = acc
    eta = [mpf(i+1)*b[i+1] for i in range(J+1)]
    return eta, a

# ---------------------------------------------------------------- route (i-b): F, A, G
def A_of_z(z):
    one = mpf(1)
    w = one/(one - z)                      # = s
    return (-mp.log(2) - mp.log(one - z) - mp.log(mp.pi)*w/2
            + mp.loggamma(w/2))

def G_of_z(z):
    one = mpf(1)
    s = one/(one - z)
    return mp.log((s - 1)*mp.zeta(s))

# ---------------------------------------------------------------- main
if __name__ == "__main__":
    t0 = time.time()
    P(__doc__)
    P("="*100)
    P("ROUTE (i): eta_j from Stieltjes/Laurent data, lambda_n^arith = sum_k C(n,k) eta_{k-1}")
    eta, acoef = eta_constants(NMAX, R=mpf(2), N=512, dps=80)
    mp.dps = 60
    P(f"  eta_0            = {mp.nstr(eta[0], 30)}")
    P(f"  gamma_Euler      = {mp.nstr(mp.euler, 30)}     (must match: eta_0 = gamma)")
    P(f"  |eta_0 - gamma|  = {mp.nstr(abs(eta[0]-mp.euler), 5)}")
    P(f"  eta_1 = {mp.nstr(eta[1],20)}   eta_2 = {mp.nstr(eta[2],20)}   eta_5 = {mp.nstr(eta[5],20)}")
    P(f"  eta_20 = {mp.nstr(eta[20],10)}   eta_39 = {mp.nstr(eta[39],10)}   "
      f"(decay ~ |rho_1 - 1|^-j = 14.14^-j)")

    lam_arith_i = []
    for n in range(1, NMAX+1):
        acc = mpf(0)
        for k in range(1, n+1):
            acc += mp.binomial(n, k)*eta[k-1]
        lam_arith_i.append(acc)

    P("\nROUTE (i-b): direct Cauchy DFT of F = A + G on |z| = 0.8  (region |Im s| < 2.23, "
      "provably zero-free)")
    r, Ndft = mpf('0.8'), 512
    cA = dft_coeffs(A_of_z, r, Ndft, NMAX, 60)
    cG = dft_coeffs(G_of_z, r, Ndft, NMAX, 60)
    mp.dps = 60
    lam_arch = [mpf(n)*cA[n].real for n in range(1, NMAX+1)]
    lam_arith_ib = [mpf(n)*cG[n].real for n in range(1, NMAX+1)]
    maximag = max(abs(cA[n].imag) for n in range(1, NMAX+1)) + \
              max(abs(cG[n].imag) for n in range(1, NMAX+1))
    P(f"  max |Im c_n| (should be ~0, coefficients are real) = {mp.nstr(maximag,5)}")

    P("\n  n      lambda_n^arith  route(i)      route(i-b)          |diff|")
    worst = mpf(0)
    for n in (1,2,3,5,10,20,30,40):
        d = abs(lam_arith_i[n-1] - lam_arith_ib[n-1])
        worst = max(worst, d/max(abs(lam_arith_i[n-1]), mpf(1)))
        P(f"  {n:>3}   {mp.nstr(lam_arith_i[n-1],20):>24}  {mp.nstr(lam_arith_ib[n-1],20):>24}   "
          f"{mp.nstr(d,4)}")
    P(f"  worst RELATIVE disagreement (i) vs (i-b) over n=1..40: {mp.nstr(worst,4)}")

    lam = [lam_arch[i] + lam_arith_ib[i] for i in range(NMAX)]

    P("\n  known values check:  lambda_1 = 0.0230957089661210...  lambda_2 = 0.0923457352880...")
    P(f"                       lambda_1 = {mp.nstr(lam[0],22)}")
    P(f"                       lambda_2 = {mp.nstr(lam[1],22)}")
    P(f"                       lambda_3 = {mp.nstr(lam[2],22)}")
    P(f"                       lambda_4 = {mp.nstr(lam[3],22)}")

    # save
    out = {}
    mp.dps = 50
    out['lam']        = [mp.nstr(x, 40) for x in lam]
    out['lam_arch']   = [mp.nstr(x, 40) for x in lam_arch]
    out['lam_arith']  = [mp.nstr(x, 40) for x in lam_arith_ib]
    out['lam_arith_i']= [mp.nstr(x, 40) for x in lam_arith_i]
    out['eta']        = [mp.nstr(x, 40) for x in eta]
    import json
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           'att015_lambda_exact.json'), 'w') as fh:
        json.dump(out, fh, indent=1)
    P(f"\n  wrote att015_lambda_exact.json    [{time.time()-t0:.1f}s]")

    P("\n" + "="*100)
    P("SPLIT (item 2 of the brief): archimedean vs arithmetic, both EXACT.")
    P(f"  {'n':>4}{'lambda_n':>20}{'arch part':>20}{'arith part':>20}{'arith/lambda':>14}")
    for n in list(range(1,11)) + [15,20,25,30,35,40]:
        P(f"  {n:>4}{mp.nstr(lam[n-1],14):>20}{mp.nstr(lam_arch[n-1],14):>20}"
          f"{mp.nstr(lam_arith_ib[n-1],14):>20}"
          f"{float(lam_arith_ib[n-1]/lam[n-1]):>14.5f}")
