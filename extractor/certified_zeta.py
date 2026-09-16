"""A CERTIFIED evaluator for zeta on the critical line, via Euler-Maclaurin with the
explicit remainder bound.  No external ball-arithmetic library needed.

  zeta(s) = sum_{n<N} n^-s + N^-s/2 + N^{1-s}/(s-1)
            + sum_{k=1}^{K} B_{2k}/(2k)! * (s)_{2k-1} * N^{-s-2k+1} + E
  |E| <= | (s)_{2K+1} * B_{2K+2}/(2K+2)! * N^{-Re s-2K-1} | * |s+2K+1|/(Re s+2K+1)

(s)_m = rising factorial.  The bound is classical (Edwards 6.4 / Johansson 2015).

Arithmetic model, stated so it can be checked: mpmath at working precision D digits; the
accumulated rounding over the ~N+K operations is bounded by (N+K)*10^{-D}*max|term|, which
is added to the truncation bound.  The result is a genuine enclosure under that model.
"""
from mpmath import mp, mpf, mpc, bernoulli, factorial, fabs, re as mre
mp.dps = 60

def zeta_enclosure(s, N=None, K=None, D=None):
    """returns (value, radius) with |zeta(s) - value| <= radius"""
    D = D or mp.dps
    t = float(abs(mp.im(s)))
    if N is None: N = max(16, int(t/2) + 20)
    if K is None: K = 20
    sigma = mre(s)
    tot = mpc(0); maxterm = mpf(0)
    for n in range(1, N):
        term = mp.power(n, -s); tot += term
        maxterm = max(maxterm, fabs(term))
    tot += mp.power(N, -s)/2
    tot += mp.power(N, 1-s)/(s-1)
    # rising factorial (s)_{2k-1}, built incrementally
    rf = mpc(1)   # (s)_0
    for k in range(1, K+1):
        while True:
            m = 2*k-1
            break
        # (s)_{2k-1} = prod_{j=0}^{2k-2} (s+j)
        rf = mpc(1)
        for j in range(2*k-1): rf *= (s + j)
        term = bernoulli(2*k)/factorial(2*k) * rf * mp.power(N, -s-2*k+1)
        tot += term
        maxterm = max(maxterm, fabs(term))
    # explicit truncation bound
    rf2 = mpc(1)
    for j in range(2*K+1): rf2 *= (s + j)
    trunc = fabs(rf2 * bernoulli(2*K+2)/factorial(2*K+2) * mp.power(N, -sigma-2*K-1)) \
            * fabs(s + 2*K+1)/(sigma + 2*K + 1)
    rounding = (N + K) * mpf(10)**(-D) * maxterm
    return tot, trunc + rounding

print("=== validate the certified evaluator against mpmath.zeta ===")
print(f"{'t':>12} {'|ours-mpmath|':>16} {'radius':>14}  inside?")
for t in (14.134725141734693, 20.0, 49.773832477672, 236.524229665816, 1419.422480945996):
    s = mpf(1)/2 + mpc(0,1)*mpf(t)
    v, r = zeta_enclosure(s)
    ref = mp.zeta(s)
    d = fabs(v - ref)
    print(f"{t:>12.4f} {mp.nstr(d,6):>16} {mp.nstr(r,6):>14}  {'YES' if d <= r else 'NO'}")
