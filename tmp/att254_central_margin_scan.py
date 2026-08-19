#!/usr/bin/env python3
"""
att254 — CENTRAL JENSEN MARGIN SCAN, d = 2..12.

The question (ledger 271 follow-up): our support rungs' margins collapsed
super-exponentially (1.6e-5 at L=0.9 -> 9.9e-9 at log 3), which is why
fixed-support certificates die there.  Do the CENTRAL (Jensen) rungs behave
the same way, or is the centre the softer face of the same object?

Objects.  K(u) = 4 sum_{n>=1} (2 pi^2 n^4 e^{9u/2} - 3 pi n^2 e^{5u/2}) e^{-pi n^2 e^{2u}}
(the repo kernel), m_j = int_0^inf u^j K(u) du, and the JENSEN sequence
    gamma_k = k! * m_{2k} / (2k)!          [xiCentralCoeff in the Lean file]
for which the d=2 rung is exactly the classical 3 m_2^2 > m_0 m_4.
Central Jensen polynomial:  J_d(X) = sum_{j<=d} C(d,j) gamma_j X^j.

MARGIN (scale-invariant, comparable across d, and generalizing the d=2 slack):
the smallest RELATIVE perturbation of a SINGLE coefficient gamma_j that
destroys hyperbolicity, minimized over j.  At d=2 this must reproduce the
classical figure (m_0 m_4 / (3 m_2^2) = 0.9304 -> about 7.5%).

CONTROLS (pre-registered):
  C1  m_0 m_4 / m_2^2 must equal 2.7911 (CNV/repo figure) and K(0)=1.78678760187
      (ledger 266 Taylor coefficient c0).
  C2  d <= 8 must come out hyperbolic — those rungs are proven
      (CNV 1986 d=2; Dimitrov-Lucas d=3; GORZ 2019 d<=8).  A non-hyperbolic
      verdict there is an instrument failure, not a discovery.
  C3  d=2 margin must match the closed-form slack computed directly.
FALSIFIER for the "centre is softer" hypothesis: margins collapsing at a rate
comparable to the support rungs (orders of magnitude per rung).
"""
import mpmath as mp
import math

mp.mp.dps = 50

NMAX = 14          # theta index cutoff: e^{-pi n^2} at n=14 is ~1e-268
DMAX = 12

def K(u):
    u = mp.mpf(u)
    s = mp.mpf(0)
    e2 = mp.e ** (2 * u)
    a = mp.e ** (9 * u / 2)
    b = mp.e ** (5 * u / 2)
    for n in range(1, NMAX + 1):
        n2 = mp.mpf(n) ** 2
        s += (2 * mp.pi ** 2 * n2 ** 2 * a - 3 * mp.pi * n2 * b) * mp.e ** (-mp.pi * n2 * e2)
    return 4 * s

def moment(j):
    return mp.quad(lambda u: u ** j * K(u), [0, mp.mpf('0.25'), mp.mpf('0.5'),
                                             1, 2, 4])

def controls(m):
    print("== CONTROLS ==")
    k0 = K(0)
    print(f"  C1a K(0)          = {mp.nstr(k0, 12)}   (ledger 266: 1.78678760187)")
    r = m[0] * m[4] / m[2] ** 2
    print(f"  C1b m0*m4/m2^2    = {mp.nstr(r, 10)}   (CNV/repo: 2.7911)")
    print(f"      slack of the d=2 rung: 1 - m0m4/(3 m2^2) = "
          f"{mp.nstr(1 - r / 3, 6)}  (repo: 6.96%)")

def jensen_coeffs(gam, d):
    """descending-order coefficient list of J_d."""
    return [mp.binomial(d, j) * gam[j] for j in range(d, -1, -1)]

def is_hyperbolic(coeffs, tol=mp.mpf('1e-18')):
    try:
        rts = mp.polyroots(coeffs, maxsteps=200, extraprec=400)
    except Exception:
        return None, None
    scale = max(abs(r) for r in rts)
    worst = max(abs(mp.im(r)) for r in rts) / scale
    return worst < tol, rts

def coeff_margin(gam, d, j, sign, lo=mp.mpf(0), hi=mp.mpf(4), iters=44):
    """largest eps with gamma_j -> gamma_j (1 + sign*eps) still hyperbolic."""
    def ok(eps):
        g = list(gam)
        g[j] = gam[j] * (1 + sign * eps)
        h, _ = is_hyperbolic(jensen_coeffs(g, d))
        return bool(h)
    if ok(hi):
        return None                      # no failure found in range
    for _ in range(iters):
        mid = (lo + hi) / 2
        if ok(mid):
            lo = mid
        else:
            hi = mid
    return lo

def main():
    print("== MOMENTS ==")
    m = {}
    for j in range(0, 2 * DMAX + 1, 2):
        m[j] = moment(j)
        if j <= 8 or j % 6 == 0:
            print(f"  m_{j:<2} = {mp.nstr(m[j], 12)}")
    controls(m)

    gam = [mp.factorial(k) * m[2 * k] / mp.factorial(2 * k) for k in range(DMAX + 1)]
    print("== JENSEN SEQUENCE gamma_k = k! m_2k/(2k)! ==")
    for k in range(DMAX + 1):
        print(f"  gamma_{k:<2} = {mp.nstr(gam[k], 10)}")

    print("== HYPERBOLICITY + MARGINS ==")
    print(f"  {'d':>3} {'hyperbolic':>11} {'min gap/spread':>15} {'margin':>12} {'arg j':>6} {'known':>7}")
    results = []
    for d in range(2, DMAX + 1):
        coeffs = jensen_coeffs(gam, d)
        hyp, rts = is_hyperbolic(coeffs)
        reals = sorted(mp.re(r) for r in rts)
        gaps = [reals[i + 1] - reals[i] for i in range(len(reals) - 1)]
        spread = reals[-1] - reals[0]
        mingap = min(gaps) / spread if spread != 0 else mp.mpf(0)
        best, bestj = None, None
        for j in range(d + 1):
            for sgn in (1, -1):
                e = coeff_margin(gam, d, j, mp.mpf(sgn))
                if e is not None and (best is None or e < best):
                    best, bestj = e, (j, sgn)
        known = "proven" if d <= 8 else "OPEN"
        print(f"  {d:>3} {str(hyp):>11} {mp.nstr(mingap, 6):>15} "
              f"{mp.nstr(best, 6) if best is not None else 'none':>12} "
              f"{str(bestj):>6} {known:>7}", flush=True)
        results.append((d, hyp, mingap, best, bestj))

    print("== THE LAW ==")
    prev = None
    for d, hyp, mingap, best, bestj in results:
        if best is None:
            continue
        ratio = (prev / best) if prev else None
        print(f"  d={d:<3} margin {mp.nstr(best, 6):>12}"
              + (f"   previous/this = {mp.nstr(ratio, 5)}" if ratio else ""))
        prev = best
    print("  (support-rung comparison: 1.6e-5 -> 9.9e-9 across three rungs,")
    print("   i.e. ~10x per 0.05 of support; see ledger 255/271.)")

if __name__ == "__main__":
    main()
