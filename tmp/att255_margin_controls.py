#!/usr/bin/env python3
"""
att255 — IS THE CENTRAL MARGIN DECAY GENERIC?  (the control att254 lacked)

att254 measured, for the Xi moments, a geometric margin law ratio ~4.7 per
Jensen rung.  I read that as a limitation.  Sam: wrong.  The decisive question
is whether the SAME law holds for a sequence whose Laguerre-Polya membership is
known outright — if so the decay is a property of the CRITERION, not of zeta,
and it says nothing about difficulty.

Sequences (all in the Jensen normalization gamma_k = k! m_2k/(2k)!, where
Xi_c(t) = sum (-1)^k m_2k t^2k/(2k)!):

  (A) ZETA          m_2k = int_0^inf u^2k K(u) du         [att254 values]
  (B) SINC control  m_2k = 1/(2k+1)  =>  Xi_c = sin t / t  — ALL ZEROS REAL (LP)
  (C) COS control   m_2k = 1         =>  Xi_c = cos t      — ALL ZEROS REAL (LP)
  (D) FALSIFIER     m_0 = 3, m_2k = 1 (k>=1) => Xi_c = 2 + cos t — NO real zeros,
      not LP; the scan MUST report non-hyperbolic at some d or the instrument
      is blind.

Same margin as att254: smallest relative perturbation of a single gamma_j that
destroys hyperbolicity, minimized over j (scale-invariant in X).
"""
import mpmath as mp

mp.mp.dps = 40
DMAX = 10

def jensen_coeffs(gam, d):
    return [mp.binomial(d, j) * gam[j] for j in range(d, -1, -1)]

def is_hyperbolic(coeffs, tol=mp.mpf('1e-15')):
    try:
        rts = mp.polyroots(coeffs, maxsteps=200, extraprec=300)
    except Exception:
        return None
    scale = max(abs(r) for r in rts)
    if scale == 0:
        return True
    return max(abs(mp.im(r)) for r in rts) / scale < tol

def coeff_margin(gam, d, j, sign, hi=mp.mpf(4), iters=34):
    def ok(eps):
        g = list(gam)
        g[j] = gam[j] * (1 + sign * eps)
        return bool(is_hyperbolic(jensen_coeffs(g, d)))
    if ok(hi):
        return None
    lo = mp.mpf(0)
    for _ in range(iters):
        mid = (lo + hi) / 2
        if ok(mid):
            lo = mid
        else:
            hi = mid
    return lo

def scan(name, gam, dmax=DMAX):
    print(f"== {name} ==", flush=True)
    print(f"  {'d':>3} {'hyperbolic':>11} {'margin':>13} {'ratio':>8}")
    prev = None
    out = []
    for d in range(2, dmax + 1):
        hyp = is_hyperbolic(jensen_coeffs(gam, d))
        if not hyp:
            print(f"  {d:>3} {str(hyp):>11} {'--':>13} {'--':>8}   <-- NOT hyperbolic")
            out.append((d, hyp, None))
            continue
        best = None
        for j in range(d + 1):
            for sgn in (1, -1):
                e = coeff_margin(gam, d, j, mp.mpf(sgn))
                if e is not None and (best is None or e < best):
                    best = e
        ratio = (prev / best) if (prev and best) else None
        print(f"  {d:>3} {str(hyp):>11} "
              f"{mp.nstr(best, 6) if best else 'none':>13} "
              f"{mp.nstr(ratio, 5) if ratio else '--':>8}", flush=True)
        prev = best
        out.append((d, hyp, best))
    return out

def main():
    # (A) zeta: recompute the moments exactly as att254
    NMAX = 14
    def K(u):
        u = mp.mpf(u); s = mp.mpf(0)
        e2 = mp.e ** (2 * u); a = mp.e ** (9 * u / 2); b = mp.e ** (5 * u / 2)
        for n in range(1, NMAX + 1):
            n2 = mp.mpf(n) ** 2
            s += (2 * mp.pi ** 2 * n2 ** 2 * a - 3 * mp.pi * n2 * b) * \
                 mp.e ** (-mp.pi * n2 * e2)
        return 4 * s
    mz = {2 * k: mp.quad(lambda u: u ** (2 * k) * K(u),
                         [0, mp.mpf('0.25'), mp.mpf('0.5'), 1, 2, 4])
          for k in range(DMAX + 1)}
    gam_zeta = [mp.factorial(k) * mz[2 * k] / mp.factorial(2 * k) for k in range(DMAX + 1)]
    gam_sinc = [mp.factorial(k) / mp.factorial(2 * k + 1) for k in range(DMAX + 1)]
    gam_cos = [mp.factorial(k) / mp.factorial(2 * k) for k in range(DMAX + 1)]
    gam_bad = [mp.factorial(k) / mp.factorial(2 * k) for k in range(DMAX + 1)]
    gam_bad[0] = mp.mpf(3)

    print(f"  control check: zeta m0m4/m2^2 = "
          f"{mp.nstr(mz[0] * mz[4] / mz[2] ** 2, 8)} (CNV 2.7911)")
    a = scan("(A) ZETA", gam_zeta)
    b = scan("(B) SINC  = sin t / t   [LP, all zeros real]", gam_sinc)
    c = scan("(C) COS   = cos t       [LP, all zeros real]", gam_cos)
    d = scan("(D) FALSIFIER = 2 + cos t   [NOT LP — must fail]", gam_bad)

    print("== VERDICT ==")
    def geo(o):
        rs = []
        vals = [x[2] for x in o if x[2]]
        for i in range(1, len(vals)):
            rs.append(vals[i - 1] / vals[i])
        return rs
    for nm, o in (("zeta", a), ("sinc", b), ("cos", c)):
        rs = geo(o)
        if rs:
            tail = rs[-4:]
            print(f"  {nm:>5}: late ratios {[mp.nstr(r, 4) for r in tail]}")
    nonhyp = [x[0] for x in d if x[1] is False]
    print(f"  falsifier non-hyperbolic at d = {nonhyp if nonhyp else 'NEVER (instrument blind!)'}")

if __name__ == "__main__":
    main()
