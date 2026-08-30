"""att541 -- C3 batch 4.  The SECOND tail primitive U and the QUADRATIC ramp V2.

Normalisation, fixed once (all cross-checked in att532/att538):

  Phi_R(u) = 2*P0(|u|),  Xi(x) = xi(1/2+ix) = int_R Phi_R(u) e^{ixu} du
  C(u,x)   = Wigner density of Phi_R;  int_R C du = Xi(x)^2
  T(r,x)   = int_r^inf (u-r) C(u,x) du            [ FIRST tail primitive ]
  U(R,x)   = int_R^inf T(r,x) dr = (1/2) int_R^inf (u-R)^2 C(u,x) du
           = V2(R,x)/2   [ SECOND tail primitive = QUADRATIC ramp / 2 ]

att532's S^{Py} = T/4.  Hence, from att532's validated Xi-route,

  T(r,x) = (1/(2 pi)) int_0^inf [Xi(x)^2 - Xi(x+t)Xi(x-t)] cos(2 r t) t^{-2} dt   (Bt)

and by an ABSOLUTELY convergent swap over the FINITE r-range [0,R],

  M(R,x) := int_0^R T(r,x) dr
          = (1/(4 pi)) int_0^inf [Xi(x)^2 - Xi(x+t)Xi(x-t)] sin(2 R t) t^{-3} dt   (Ms)

  U(R,x) = U(0,x) - M(R,x),   U(0,x) = L1(x)/16,  L1 = 2(Xi'^2 - Xi Xi'')

WHY THIS OBJECT.  Uniform T >= 0 is FAILED (T(0,60) = -2.4411414711711282366e-36).
But the target only needs  int_0^inf q(r) T(r,x) dr >= 0  for q = g_y'' , which is
NONNEGATIVE and NONDECREASING on [0,inf).  Layer-cake:
   int_0^inf q T = q(0) U(0) + int_0^inf q'(s) U(s) ds ,
so  U >= 0 everywhere  SUFFICES, and is strictly weaker than T >= 0.
U(0) >= 0 is exactly L1 >= 0 (att539 B1: no counterexample on [0,200]).

DC/AC discipline.  Own scale is Xi(x)^2 (8.46e-36 at x=60), never 1.
  DC piece  Xi(x)^2 * trig(t)/t^k  -- integrated EXACTLY on [T,inf):
     int_T^inf cos(at)/t^2 dt = cos(aT)/T - a(pi/2 - Si(aT))
     int_T^inf sin(at)/t^3 dt = sin(aT)/(2T^2) + (a/2)*[the above]
  AC piece  Xi(x+t)Xi(x-t)*trig/t^k -- decays like e^{-pi t/2}; bounded, never
  quadratured past T.
Only the AC is quadratured on [0,T].  Every reported sign carries a margin against
the AC tail bound.

USAGE: python3 att541_c3b4_ramp2.py <cmd> [args]
  profile x dps T        -- T(r,x) and U(R,x) on an r-grid, with margins
  scanU   dps T x0 x1 dx -- min_R U(R,x) over a hostile R-grid, x-scan
  consist x dps T        -- M(inf) vs L1/16 self-consistency
"""
import sys
import mpmath as mp

_XI_CACHE = {}


def xi(s):
    return mp.mpf(1) / 2 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Xi(v):
    # NB: the cache key must be the EXACT value, not a decimal truncation.  Keying on
    # mp.nstr(v,35) collapses the nearby probes that mp.diff uses and silently returns
    # L1 = 0; caught 2026-08-24 by L1(60) printing 0.0 against the known +6.83e-35.
    k = (mp.mpf(v), mp.mp.prec)
    if k not in _XI_CACHE:
        _XI_CACHE[k] = mp.re(xi(mp.mpf(1) / 2 + 1j * mp.mpf(v)))
    return _XI_CACHE[k]


_GL = {}


def gl_nodes(n):
    key = (n, mp.mp.dps)
    if key not in _GL:
        _GL[key] = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(
            mp.mpf(-1), mp.mpf(1), n, mp.mp.prec)
    return _GL[key]


def panel_int(f, a, b, deg=5):
    nodes = gl_nodes(deg)
    a, b = mp.mpf(a), mp.mpf(b)
    half, mid = (b - a) / 2, (a + b) / 2
    return half * mp.fsum(w * f(mid + half * t) for t, w in nodes)


def edges_of(T, panel):
    T = mp.mpf(T)
    e = [mp.mpf(0)]
    q = mp.mpf('1e-8')
    while q < panel:
        e.append(q)
        q *= 10
    q = mp.mpf(panel)
    while q < T:
        e.append(q)
        q += mp.mpf(panel)
    e.append(mp.mpf(T))
    return e


def dc_cos2(a, T):
    """int_T^inf cos(a t) t^{-2} dt, exact."""
    T = mp.mpf(T)
    if a == 0:
        return 1 / T
    return mp.cos(a * T) / T - a * (mp.pi / 2 - mp.si(a * T))


def dc_sin3(a, T):
    """int_T^inf sin(a t) t^{-3} dt, exact."""
    T = mp.mpf(T)
    if a == 0:
        return mp.mpf(0)
    return mp.sin(a * T) / (2 * T ** 2) + (a / 2) * dc_cos2(a, T)


def ac_tail_bound(x, T, k):
    """Bound on |int_T^inf Xi(x+t)Xi(x-t) trig / t^k dt|.

    |Xi(x+t)Xi(x-t)| decays like e^{-pi t/2}; sample the ratio over [T, T+4] and
    use a geometric majorant, so the bound is measured, not assumed."""
    T = mp.mpf(T)
    f0 = abs(Xi(x + T) * Xi(x - T))
    f1 = abs(Xi(x + T + 1) * Xi(x - T - 1))
    if f0 == 0:
        return mp.mpf(0)
    rate = -mp.log(f1 / f0) if f1 > 0 else mp.mpf(4)
    if rate <= 0:
        rate = mp.mpf('1e-3')
    return f0 / (rate * T ** k)


def T_of(x, r, T=150, deg=5, panel=mp.mpf('0.5')):
    """T(r,x) via (Bt).  Returns (value, ac_bound)."""
    x, r = mp.mpf(x), mp.mpf(r)
    X2 = Xi(x) ** 2

    def f(t):
        if t == 0:
            return mp.mpf(0)
        return (X2 - Xi(x + t) * Xi(x - t)) * mp.cos(2 * r * t) / t ** 2

    e = edges_of(T, panel)
    tot = mp.fsum(panel_int(f, e[i], e[i + 1], deg) for i in range(len(e) - 1))
    tot += X2 * dc_cos2(2 * r, T)
    return tot / (2 * mp.pi), ac_tail_bound(x, T, 2) / (2 * mp.pi)


def M_of(x, R, T=150, deg=5, panel=mp.mpf('0.5')):
    """M(R,x) = int_0^R T dr via (Ms).  Returns (value, ac_bound)."""
    x, R = mp.mpf(x), mp.mpf(R)
    X2 = Xi(x) ** 2

    def f(t):
        if t == 0:
            return mp.mpf(0)
        return (X2 - Xi(x + t) * Xi(x - t)) * mp.sin(2 * R * t) / t ** 3

    e = edges_of(T, panel)
    tot = mp.fsum(panel_int(f, e[i], e[i + 1], deg) for i in range(len(e) - 1))
    tot += X2 * dc_sin3(2 * R, T)
    return tot / (4 * mp.pi), ac_tail_bound(x, T, 3) / (4 * mp.pi)


def L1_of(x):
    """L1(x) = 2(Xi'(x)^2 - Xi(x) Xi''(x)) = -d^2/dh^2 [Xi(x+h)Xi(x-h)]|_0."""
    x = mp.mpf(x)
    d1 = mp.diff(Xi, x, 1)
    d2 = mp.diff(Xi, x, 2)
    return 2 * (d1 ** 2 - Xi(x) * d2)


def U_of(x, R, U0, T=150, deg=5, panel=mp.mpf('0.5')):
    m, b = M_of(x, R, T, deg, panel)
    return U0 - m, b


# --------------------------------------------------------------------------
def cmd_consist(x, dps, T):
    mp.mp.dps = dps
    x = mp.mpf(x)
    L1 = L1_of(x)
    print('# att541 consistency, x=%s dps=%d T=%s' % (x, dps, T))
    print('  Xi(x)     = %s' % mp.nstr(Xi(x), 20))
    print('  Xi(x)^2   = %s' % mp.nstr(Xi(x) ** 2, 20))
    print('  L1(x)     = %s' % mp.nstr(L1, 20))
    print('  L1/16     = %s   <- predicted U(0) = M(inf)' % mp.nstr(L1 / 16, 20))
    for R in ('2', '3', '4', '6'):
        m, b = M_of(x, R, T)
        print('  M(%s)  = %-24s  ac<=%-12s  rel.dev = %s'
              % (R, mp.nstr(m, 16), mp.nstr(b, 4),
                 mp.nstr(abs(m - L1 / 16) / abs(L1 / 16), 6)))
        sys.stdout.flush()


def cmd_profile(x, dps, T):
    mp.mp.dps = dps
    x = mp.mpf(x)
    L1 = L1_of(x)
    U0 = L1 / 16
    print('# att541 PROFILE  x=%s dps=%d T=%s' % (x, dps, T))
    print('#   Xi(x)^2 = %s   L1 = %s   U(0)=L1/16 = %s'
          % (mp.nstr(Xi(x) ** 2, 12), mp.nstr(L1, 12), mp.nstr(U0, 12)))
    print('#     r          T(r,x)                 acT        '
          'U(r,x)=U0-M(r)          acU        signT signU')
    grid = ['0', '0.02', '0.05', '0.1', '0.15', '0.2', '0.22', '0.25', '0.28',
            '0.3', '0.35', '0.4', '0.5', '0.6', '0.7', '0.8', '0.9', '1.0',
            '1.1', '1.2', '1.4', '1.6', '1.8', '2.0', '2.5', '3.0']
    for r in grid:
        tv, tb = T_of(x, r, T)
        uv, ub = U_of(x, r, U0, T)
        print('  %6s  %-22s %-10s %-22s %-10s  %s %s'
              % (r, mp.nstr(tv, 14), mp.nstr(tb, 3), mp.nstr(uv, 14),
                 mp.nstr(ub, 3),
                 'NEG' if tv < 0 else '+', 'NEG<<<' if uv < 0 else '+'))
        sys.stdout.flush()


def cmd_scanU(dps, T, x0, x1, dx, rgrid=None):
    mp.mp.dps = dps
    if rgrid is None:
        rgrid = ['0', '0.05', '0.1', '0.2', '0.3', '0.5', '0.7', '1.0', '1.5', '2.0']
    print('# att541 scanU  dps=%d T=%s  R-grid=%s' % (dps, T, ','.join(rgrid)))
    print('#    x       L1(x)              min_R U(R,x)        argmin   any NEG?')
    x = mp.mpf(x0)
    while x <= mp.mpf(x1) + mp.mpf('1e-12'):
        L1 = L1_of(x)
        U0 = L1 / 16
        best, arg = None, None
        for r in rgrid:
            uv, _ = U_of(x, r, U0, T)
            if best is None or uv < best:
                best, arg = uv, r
        print('  %7s  %-18s %-20s %-8s %s'
              % (mp.nstr(x, 6), mp.nstr(L1, 10), mp.nstr(best, 12), arg,
                 'NEG <<<' if best < 0 else ''))
        sys.stdout.flush()
        x += mp.mpf(dx)


def cmd_hostile(x, dps, T, rmax='3.0', step='0.02'):
    """Fine r-sweep: count sign changes of T, and minimise U over the same grid."""
    mp.mp.dps = dps
    x = mp.mpf(x)
    L1 = L1_of(x)
    U0 = L1 / 16
    print('# att541 HOSTILE  x=%s dps=%d T=%s rmax=%s step=%s' % (x, dps, T, rmax, step))
    print('#   Xi(x)   = %s' % mp.nstr(Xi(x), 20))
    print('#   Xi(x)^2 = %s' % mp.nstr(Xi(x) ** 2, 20))
    print('#   L1(x)   = %s     (sign %s)' % (mp.nstr(L1, 20), '+' if L1 > 0 else 'NEG <<<'))
    print('#   U(0)=L1/16 = %s' % mp.nstr(U0, 20))
    r = mp.mpf(0)
    rmax, step = mp.mpf(rmax), mp.mpf(step)
    prev = None
    changes = []
    minU, argU, minUb = None, None, None
    rows = []
    while r <= rmax + mp.mpf('1e-12'):
        tv, tb = T_of(x, r, T)
        m, mb = M_of(x, r, T)
        uv = U0 - m
        ub = mb
        rows.append((r, tv, tb, uv, ub))
        s = 1 if tv > 0 else (-1 if tv < 0 else 0)
        if prev is not None and s != 0 and prev != 0 and s != prev:
            changes.append(mp.nstr(r, 6))
        if s != 0:
            prev = s
        if minU is None or uv < minU:
            minU, argU, minUb = uv, r, ub
        r += step
    print('#   T sign changes at r in: %s   (COUNT = %d)'
          % (','.join(changes) if changes else 'NONE', len(changes)))
    print('#   min_R U(R,x) = %s  at R = %s   ac<= %s   %s'
          % (mp.nstr(minU, 16), mp.nstr(argU, 6), mp.nstr(minUb, 4),
             'NEG <<<' if minU < 0 else 'NONNEG'))
    print('#     r          T(r,x)                 U(R,x)                 sT sU')
    for (r, tv, tb, uv, ub) in rows:
        print('  %8s  %-22s %-22s  %s %s'
              % (mp.nstr(r, 6), mp.nstr(tv, 14), mp.nstr(uv, 14),
                 'NEG' if tv < 0 else '+', 'NEG<<<' if uv < 0 else '+'))
    sys.stdout.flush()


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'hostile':
        cmd_hostile(a[1], int(a[2]), a[3], a[4] if len(a) > 4 else '3.0',
                    a[5] if len(a) > 5 else '0.02')
    elif a[0] == 'consist':
        cmd_consist(a[1], int(a[2]), a[3])
    elif a[0] == 'profile':
        cmd_profile(a[1], int(a[2]), a[3])
    elif a[0] == 'scanU':
        cmd_scanU(int(a[1]), a[2], a[3], a[4], a[5])
