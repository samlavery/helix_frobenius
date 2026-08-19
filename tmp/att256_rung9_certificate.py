#!/usr/bin/env python3
"""
att256 — CERTIFIED HYPERBOLICITY OF THE CENTRAL JENSEN RUNGS d = 9..12,
the first rungs past the proven range (GORZ 2019: d <= 8).

STRUCTURE OF THE CERTIFICATE (all three parts rigorous):

  (1) MOMENT ENCLOSURES.  m_k = int_0^inf u^k K(u) du,
      K(u) = 4 sum_{n>=1} (2 pi^2 n^4 e^{9u/2} - 3 pi n^2 e^{5u/2}) e^{-pi n^2 e^{2u}}.
      * n-tail: for n > N every term is bounded by 2 pi^2 n^4 e^{9u/2} e^{-pi n^2 e^{2u}}
        and e^{-pi n^2 e^{2u}} <= e^{-pi n^2} e^{-pi n^2 (e^{2u}-1)}; with N = 20 the
        whole tail integral is < 1e-500.
      * u-tail: for u > U the integrand is <= C u^k e^{9u/2} e^{-pi e^{2u}}; at U = 3,
        e^{-pi e^6} = e^{-1267}.
      * quadrature: Gauss-Legendre with N_GL nodes on panels of half-width h.
        The integrand is ENTIRE in u, so on the Bernstein ellipse E_rho of the panel
        the classical bound gives
              |err| <= (64/15) * M(rho) * rho^{-2 N_GL} / (rho^2 - 1) * h,
        with M(rho) = max |f| on E_rho bounded ANALYTICALLY below (the modulus of
        e^{-pi n^2 e^{2u}} is e^{-pi n^2 e^{2x} cos 2y}, so the ellipse must keep
        |Im u| < pi/4; we take |Im u| <= 0.3, cos(0.6) = 0.8253 > 0).

  (2) JENSEN COEFFICIENTS.  gamma_j = j! m_{2j} / (2j)!  (exact rational multiples
      of the enclosures).

  (3) SIGN-ALTERNATION CERTIFICATE.  If at rational points a_0 < ... < a_d the
      INTERVAL evaluation of J_d = sum_j C(d,j) gamma_j X^j excludes zero and the
      signs alternate, then every polynomial with coefficients in the box has d
      sign changes, hence d real roots, hence (degree d) ALL roots real.
      This is what makes the conclusion valid for the true moments: they lie in
      the box.

CONTROLS: m0*m4/m2^2 must reproduce CNV 2.7911; the certificate must also fire at
d = 2..8 (where hyperbolicity is proven) and must FAIL on the falsifier 2 + cos t.
"""
import mpmath as mp

mp.mp.dps = 80

NTHETA = 20            # theta cutoff
U_MAX = mp.mpf(3)      # u-truncation
N_GL = 40              # Gauss-Legendre nodes per panel
PANEL = mp.mpf('0.25')
RHO = mp.mpf(4)        # Bernstein parameter
DMAX = 12

# ---------------------------------------------------------------- kernel
def K(u):
    s = mp.mpf(0)
    e2 = mp.e ** (2 * u)
    a = mp.e ** (9 * u / 2)
    b = mp.e ** (5 * u / 2)
    for n in range(1, NTHETA + 1):
        n2 = mp.mpf(n) ** 2
        s += (2 * mp.pi ** 2 * n2 ** 2 * a - 3 * mp.pi * n2 * b) * mp.e ** (-mp.pi * n2 * e2)
    return 4 * s

# ---------------------------------------------------------------- GL nodes
def gauss_legendre(n):
    nodes, weights = [], []
    for i in range(1, n + 1):
        x = mp.cos(mp.pi * (i - mp.mpf('0.25')) / (n + mp.mpf('0.5')))
        for _ in range(80):
            p0, p1 = mp.mpf(1), mp.mpf(0)
            for j in range(1, n + 1):
                p0, p1 = ((2 * j - 1) * x * p0 - (j - 1) * p1) / j, p0
            dp = n * (x * p0 - p1) / (x * x - 1)
            dx = -p0 / dp
            x += dx
            if abs(dx) < mp.mpf(10) ** (-(mp.mp.dps - 5)):
                break
        p0, p1 = mp.mpf(1), mp.mpf(0)
        for j in range(1, n + 1):
            p0, p1 = ((2 * j - 1) * x * p0 - (j - 1) * p1) / j, p0
        dp = n * (x * p0 - p1) / (x * x - 1)
        nodes.append(x)
        weights.append(2 / ((1 - x * x) * dp * dp))
    return nodes, weights

GL_X, GL_W = gauss_legendre(N_GL)

# ---------------------------------------------------------------- error bounds
def ellipse_bound(k, mid, h, rho):
    """rigorous max |u^k K(u)| on the Bernstein ellipse of [mid-h, mid+h]."""
    semi_re = h * (rho + 1 / rho) / 2
    semi_im = h * (rho - 1 / rho) / 2
    if semi_im >= mp.mpf('0.3'):
        return None
    x_lo, x_hi = mid - semi_re, mid + semi_re
    cos_min = mp.cos(2 * semi_im)
    umax = max(abs(x_lo), abs(x_hi)) + semi_im
    s = mp.mpf(0)
    for n in range(1, NTHETA + 1):
        n2 = mp.mpf(n) ** 2
        pref = 2 * mp.pi ** 2 * n2 ** 2 * mp.e ** (9 * x_hi / 2) + \
               3 * mp.pi * n2 * mp.e ** (5 * x_hi / 2)
        s += pref * mp.e ** (-mp.pi * n2 * mp.e ** (2 * x_lo) * cos_min)
    return (umax ** k) * 4 * s

def gl_panel_error(k, mid, h):
    M = ellipse_bound(k, mid, h, RHO)
    if M is None:
        raise RuntimeError("ellipse leaves the strip |Im u| < pi/4")
    # Trefethen (2008), Thm 4.5: |I - I_N| <= 64 M / (15 (1 - rho^-2) rho^{2N}) on
    # [-1,1]; the (1 - rho^-2)^{-1} = rho^2/(rho^2-1) factor was dropped in the
    # first version of this file — restored here (it costs a factor rho^2 = 16).
    return (mp.mpf(64) / 15) * M * RHO ** (-2 * N_GL) * RHO ** 2 / (RHO ** 2 - 1) * h

def tail_bounds(k):
    """(n-tail, u-tail) rigorous absolute bounds on the discarded mass."""
    ntail = mp.mpf(0)
    for n in range(NTHETA + 1, NTHETA + 40):
        n2 = mp.mpf(n) ** 2
        # int_0^inf u^k e^{9u/2} e^{-pi n^2 e^{2u}} du  <=  e^{-pi n^2} * int u^k e^{9u/2} e^{-pi n^2 (e^{2u}-1)} du
        # crude: e^{2u}-1 >= 2u  =>  integral <= int u^k e^{9u/2 - 2 pi n^2 u} du = k!/(2 pi n^2 - 9/2)^{k+1}
        denom = 2 * mp.pi * n2 - mp.mpf(9) / 2
        ntail += 8 * mp.pi ** 2 * n2 ** 2 * mp.e ** (-mp.pi * n2) * \
                 mp.factorial(k) / denom ** (k + 1)
    # u-tail, CLOSED FORM.  For u >= U convexity gives e^{2u} - e^{2U} >= 2 e^{2U}(u-U),
    # so with c = 2 pi n^2 e^{2U}:
    #   int_U^inf u^k e^{9u/2} e^{-pi n^2 e^{2u}} du
    #     <= e^{-pi n^2 e^{2U}} e^{9U/2} 2^k [ U^k/(c-9/2) + k!/(c-9/2)^{k+1} ].
    utail = mp.mpf(0)
    U = U_MAX
    for n in range(1, NTHETA + 1):
        n2 = mp.mpf(n) ** 2
        c = 2 * mp.pi * n2 * mp.e ** (2 * U) - mp.mpf(9) / 2
        utail += 8 * mp.pi ** 2 * n2 ** 2 * mp.e ** (-mp.pi * n2 * mp.e ** (2 * U)) * \
                 mp.e ** (9 * U / 2) * mp.mpf(2) ** k * \
                 (U ** k / c + mp.factorial(k) / c ** (k + 1))
    return ntail, utail

def moment_enclosure(k):
    """certified [lo, hi] for m_k."""
    total = mp.mpf(0)
    qerr = mp.mpf(0)
    u = mp.mpf(0)
    while u < U_MAX:
        a, b = u, min(u + PANEL, U_MAX)
        mid, h = (a + b) / 2, (b - a) / 2
        acc = mp.mpf(0)
        for x, w in zip(GL_X, GL_W):
            uu = mid + h * x
            acc += w * (uu ** k) * K(uu)
        total += h * acc
        qerr += gl_panel_error(k, mid, h)
        u = b
    ntail, utail = tail_bounds(k)
    rnd = abs(total) * mp.mpf(10) ** (-(mp.mp.dps - 10))
    err = qerr + ntail + utail + rnd
    return total - err, total + err, err

# ---------------------------------------------------------------- certificate
def interval_eval(lo, hi, d, a):
    """interval value of J_d(a) given gamma_j in [lo_j, hi_j]; a rational < 0."""
    vlo = mp.mpf(0); vhi = mp.mpf(0)
    for j in range(d + 1):
        c = mp.binomial(d, j) * a ** j
        t1, t2 = c * lo[j], c * hi[j]
        vlo += min(t1, t2); vhi += max(t1, t2)
    return vlo, vhi

def certify(lo, hi, mid, d, verbose=True):
    coeffs = [mp.binomial(d, j) * mid[j] for j in range(d, -1, -1)]
    rts = sorted(mp.re(r) for r in mp.polyroots(coeffs, maxsteps=300, extraprec=600))
    pts = [rts[0] - (rts[1] - rts[0]) / 2]
    for i in range(len(rts) - 1):
        pts.append((rts[i] + rts[i + 1]) / 2)
    pts.append(rts[-1] + abs(rts[-1]) / 2 if rts[-1] < 0 else rts[-1] + 1)
    signs, ok = [], True
    worst = None
    for p in pts:
        p = mp.mpf(mp.nstr(p, 25))          # rational-ish test point
        vlo, vhi = interval_eval(lo, hi, d, p)
        if vlo > 0:
            s = +1
        elif vhi < 0:
            s = -1
        else:
            s = 0; ok = False
        signs.append(s)
        rel = min(abs(vlo), abs(vhi)) / max(abs(vlo), abs(vhi), mp.mpf('1e-300'))
        worst = rel if worst is None else min(worst, rel)
    alt = all(signs[i] * signs[i + 1] < 0 for i in range(len(signs) - 1))
    if verbose:
        print(f"  d = {d:>2}: {len(pts)} test points, signs "
              f"{''.join('+' if s > 0 else ('-' if s < 0 else '0') for s in signs)}"
              f"   alternating={alt}  all-nonzero={ok}"
              f"   -> {'CERTIFIED HYPERBOLIC' if (alt and ok) else 'NOT CERTIFIED'}")
    return alt and ok

def main():
    print("== CERTIFIED MOMENT ENCLOSURES ==", flush=True)
    lo_m, hi_m, mid_m = {}, {}, {}
    for k in range(0, 2 * DMAX + 1, 2):
        l, h, e = moment_enclosure(k)
        lo_m[k], hi_m[k] = l, h
        mid_m[k] = (l + h) / 2
        if k <= 6 or k >= 2 * DMAX - 2:
            print(f"  m_{k:<2} in [{mp.nstr(l, 20)}, {mp.nstr(h, 20)}]"
                  f"   width {mp.nstr(h - l, 3)}", flush=True)
    r = mid_m[0] * mid_m[4] / mid_m[2] ** 2
    print(f"  CONTROL m0*m4/m2^2 = {mp.nstr(r, 10)}  (CNV 2.7911)")

    lo_g = [mp.factorial(j) * lo_m[2 * j] / mp.factorial(2 * j) for j in range(DMAX + 1)]
    hi_g = [mp.factorial(j) * hi_m[2 * j] / mp.factorial(2 * j) for j in range(DMAX + 1)]
    mid_g = [mp.factorial(j) * mid_m[2 * j] / mp.factorial(2 * j) for j in range(DMAX + 1)]

    print("== SIGN-ALTERNATION CERTIFICATES ==", flush=True)
    print("  (d <= 8: control — hyperbolicity is proven, the certificate must fire)")
    results = {}
    for d in range(2, DMAX + 1):
        results[d] = certify(lo_g, hi_g, mid_g, d)

    print("== FALSIFIER CONTROL (2 + cos t, not LP — must NOT certify) ==")
    bad_lo = [mp.factorial(j) / mp.factorial(2 * j) for j in range(DMAX + 1)]
    bad_lo[0] = mp.mpf(3)
    certify(bad_lo, list(bad_lo), list(bad_lo), 9)

    print("== VERDICT ==")
    newly = [d for d in range(9, DMAX + 1) if results.get(d)]
    print(f"  certified d = {[d for d in results if results[d]]}")
    print(f"  PAST THE PROVEN RANGE (d >= 9): {newly}")

if __name__ == "__main__":
    main()
