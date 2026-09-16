"""(O5) EXPLICIT bounds on |Xi| over a disc -- derived, not quoted.

Xi(z) = (1/4+z^2) * pi^{-s/2} * Gamma(s/2) * zeta(s),   s = 1/2 + i z.

For |z - m| <= r (m real, m > r) every factor is bounded explicitly:

  Re s  = 1/2 - Im(z-m)  in [1/2-r, 1/2+r],     Im s in [m-r, m+r]

* |1/4 + z^2| <= 1/4 + (|m|+r)^2.
* |pi^{-s/2}| = pi^{-Re s/2} <= pi^{-(1/2-r)/2}.
* |Gamma(w)|, w = s/2: Stirling with the CLASSICAL explicit remainder, valid for Re w > 0,
      |log Gamma(w) - [(w-1/2) log w - w + (1/2)log 2pi]| <= |B_2| / (2*1*|w|) = 1/(12|w|),
  and Re[(w-1/2)log w - w] is bounded by interval arithmetic on (Re w, Im w), using that
  Re w < 1/2 so the coefficient (Re w - 1/2) is negative.
* |zeta(s)|: bounded TERM BY TERM from the same Euler-Maclaurin expansion the certified
  evaluator uses -- no literature constant is needed, because every term is an explicit
  function of (m, r, N, K).

Everything below is an upper bound, not an estimate.
"""
from mpmath import mp, mpf, mpc, bernoulli, factorial, sqrt, log, exp, atan, pi as MPPI

def _re_loggamma_upper(a_lo, a_hi, b_lo, b_hi):
    """Upper bound on Re[(w-1/2) log w - w] + (1/2)log 2pi + 1/(12|w|) for
       Re w in [a_lo,a_hi] (a_lo > 0), Im w in [b_lo,b_hi] (b_lo > 0).

       Each product below is LINEAR in each factor separately, so its maximum over the
       box is attained at a corner; we take the max over corners rather than assume a
       sign, which keeps the bound valid for any admissible box."""
    assert 0 < a_lo <= a_hi and 0 < b_lo <= b_hi
    logw_min = log(a_lo**2 + b_lo**2)/2
    logw_max = log(a_hi**2 + b_hi**2)/2
    arg_min  = atan(b_lo/a_hi)
    arg_max  = atan(b_hi/a_lo)
    t1 = max((a - mpf(1)/2)*L for a in (a_lo, a_hi) for L in (logw_min, logw_max))
    t2 = max(-(b*A) for b in (b_lo, b_hi) for A in (arg_min, arg_max))
    t3 = -a_lo
    w_abs_min = sqrt(a_lo**2 + b_lo**2)
    return t1 + t2 + t3 + log(2*MPPI)/2 + 1/(12*w_abs_min)

def zeta_region_bound(m, r, N=None, K=12):
    """upper bound on |zeta(1/2+iz)| for |z-m| <= r."""
    m, r = mpf(m), mpf(r)
    assert m > r > 0
    s_lo = mpf(1)/2 - r                      # min of Re s
    im_hi = m + r
    s_abs = sqrt((mpf(1)/2 + r)**2 + im_hi**2)
    if N is None: N = max(16, int(m/2) + 20)
    tot = mpf(0)
    for n in range(1, N): tot += mp.power(n, -s_lo)
    tot += mp.power(N, -s_lo)/2
    tot += mp.power(N, 1 - s_lo)/(m - r)         # |s-1| >= |Im s| >= m-r
    for k in range(1, K+1):
        rf = mpf(1)
        for j in range(2*k-1): rf *= (s_abs + j)
        tot += abs(bernoulli(2*k))/factorial(2*k) * rf * mp.power(N, -s_lo-2*k+1)
    rf2 = mpf(1)
    for j in range(2*K+1): rf2 *= (s_abs + j)
    tot += rf2 * abs(bernoulli(2*K+2))/factorial(2*K+2) * mp.power(N, -s_lo-2*K-1) \
           * (s_abs + 2*K+1)/(s_lo + 2*K + 1)
    return tot

def xi_region_bound(m, r, K=12, h=0):
    """M(m,r) with |Xi(z)| <= M for |z - c| <= r, c = m + i*h, |h| + r < 1/2.

    The constraint |h| + r < 1/2 is genuine and not a coding limit: it is what keeps
    Re(s/2) > 0, which is the hypothesis of the Stirling remainder bound used below.
    Discs about the real axis (h = 0) with r < 1/2 are the case the paper needs."""
    m, r, h = mpf(m), mpf(r), mpf(h)
    if abs(h) + r >= mpf(1)/2:
        raise ValueError("need |h| + r < 1/2 so that Re(s/2) > 0 (Stirling's hypothesis)")
    poly = mpf(1)/4 + (abs(m) + r)**2
    pifac = mp.power(MPPI, -(mpf(1)/2 - r)/2)
    # w = s/2 = 1/4 - Im(z-m)/2 + i (Re z)/2
    a_lo, a_hi = mpf(1)/4 - (abs(h) + r)/2, mpf(1)/4 + (abs(h) + r)/2
    b_lo, b_hi = (m - r)/2, (m + r)/2
    gam = exp(_re_loggamma_upper(a_lo, a_hi, b_lo, b_hi))
    zb = zeta_region_bound(m, r, K=K)
    return poly * pifac * gam * zb
