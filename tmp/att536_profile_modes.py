"""att536 -- (a) the S_60(r) profile, (b) the theta-mode split.

(a) ATTACK 20, the CONSTRUCTIVE repair of the falsified STP.

    Khat(y,x) = 8 int_0^inf g''(r) S_x(r) dr,   g(u) = u sinh(2yu),
    g''(r) = 4y cosh(2yr) + 4y^2 r sinh(2yr)  >= 0 and INCREASING in r.

    Exact facts already in hand:
       int_0^inf S_x(r) dr = L1(x)/32 >= 0      (I4 + Laguerre, unconditional)
       S_x(0) < 0 at x = 60                     (att532, reproduced 13 digits)
       S_x'(0) = -Xi(x)^2/8 < 0                 (I6)
    So at x = 60 the profile r -> S_60(r) starts negative, goes MORE negative, and
    must climb back through zero to make the integral positive.  Because g'' is
    INCREASING, the weight suppresses exactly the (early, negative) region and
    up-weights the (late, positive) region.  The falsification of pointwise STP
    therefore does NOT propagate to Khat: it is fought by the weight's monotonicity.
    This measures where the crossover r0 sits and how much positive mass is above it.

(b) ATTACKS 7/8/9, the theta-mode split.
    Phi(|u|) = sum_{n>=1} phi_n(|u|),  phi_n(u) = (2 pi^2 n^4 e^{4.5u}
                                                  - 3 pi n^2 e^{2.5u}) e^{-pi n^2 e^{2u}}
    G_n(v) = 2 int_0^inf (sum_{m<=n} phi_m)(u) cos(vu) du   -- 1-D, no nesting.
    DIAGONAL vs OFF-DIAGONAL: is the ground mode alone already the whole story?
    DESIGN LAW (weil-cell-probe-null): the control must fail by MISSING structure,
    so the ground-mode object is read for whether it reproduces the sign pattern.
"""
import math
import sys

import mpmath as mp


def xi(s):
    return mp.pi ** (-s / 2) * mp.gamma(1 + s / 2) * (s - 1) * mp.zeta(s)


def Xi(z):
    return xi(mp.mpf(1) / 2 + 1j * z)


def XiR(v):
    return mp.re(Xi(mp.mpf(v)))


_GL = {}


def gl(n):
    k = (n, mp.mp.dps)
    if k not in _GL:
        _GL[k] = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(
            mp.mpf(-1), mp.mpf(1), n, mp.mp.prec)
    return _GL[k]


def panel(f, a, b, deg=4):
    nd = gl(deg)
    a, b = mp.mpf(a), mp.mpf(b)
    h, m = (b - a) / 2, (a + b) / 2
    return h * mp.fsum(w * f(m + h * t) for t, w in nd)


def S_B(x, r, T=120, deg=4, ph=mp.mpf('0.5')):
    """att532 form (B): cos OUTSIDE the bracket.  Adjudicated against att531."""
    x, r, T = mp.mpf(x), mp.mpf(r), mp.mpf(T)
    X2 = XiR(x) ** 2
    f = lambda t: (X2 - XiR(x + t) * XiR(x - t)) * mp.cos(2 * r * t) / t ** 2 if t else mp.mpf(0)
    ed, e = [mp.mpf(0)], mp.mpf('1e-8')
    while e < ph:
        ed.append(e); e *= 10
    e = ph
    while e < T:
        ed.append(e); e += ph
    ed.append(T)
    tot = mp.fsum(panel(f, ed[i], ed[i + 1], deg) for i in range(len(ed) - 1))
    a = 2 * r
    tail = X2 / T if a == 0 else X2 * (mp.cos(a * T) / T - a * (mp.pi / 2 - mp.si(a * T)))
    return (tot + tail) / (8 * mp.pi)


def L1(x):
    x = mp.mpf(x)
    return mp.diff(XiR, x, 1) ** 2 - XiR(x) * mp.diff(XiR, x, 2)


def cmd_profile(dps=30):
    mp.mp.dps = dps
    print('# att536 ATTACK 20: the S_60(r) profile and the weight monotonicity.')
    print('# exact anchors:  S_60(0) = -6.102853678e-37   (att532, 13-digit reproduction)')
    print('#                 int_0^inf S_60 dr = L1(60)/32 = %s'
          % mp.nstr(L1(60) / 32, 10))
    print('#                 S_60\'(0) = -Xi(60)^2/8 = %s' % mp.nstr(-XiR(60) ** 2 / 8, 10))
    print()
    print('#      r        S_60(r)               sign')
    prev = None
    cross = None
    for rs in ('0', '0.05', '0.1', '0.15', '0.2', '0.3', '0.4', '0.5',
               '0.7', '1.0', '1.4'):
        r = mp.mpf(rs)
        v = S_B(60, r)
        if prev is not None and prev[1] < 0 <= v:
            cross = (prev[0], rs)
        prev = (rs, v)
        print('   %7s   %-21s %s' % (rs, mp.nstr(v, 10), 'NEG' if v < 0 else '+'))
        sys.stdout.flush()
    print()
    if cross:
        print('# sign crossover r0 in (%s, %s]' % cross)
    print('# weight g\'\'(r) = 4y cosh(2yr) + 4y^2 r sinh(2yr), y small:')
    for ys in ('0.01', '0.1', '0.3'):
        y = mp.mpf(ys)
        g0 = 4 * y
        vals = [(rs, (4 * y * mp.cosh(2 * y * mp.mpf(rs))
                      + 4 * y ** 2 * mp.mpf(rs) * mp.sinh(2 * y * mp.mpf(rs))) / g0)
                for rs in ('0', '0.2', '0.5', '1.0', '1.4')]
        print('   y=%-5s  g\'\'(r)/g\'\'(0) at r=0,.2,.5,1,1.4 : %s'
              % (ys, ' '.join(mp.nstr(v, 6) for _, v in vals)))
    print('# g\'\'/g\'\'(0) >= 1 and increasing => the weight DOWN-weights the early')
    print('#   negative lobe and UP-weights the late positive lobe.  The pointwise')
    print('#   STP failure is therefore not inherited by Khat.')


def cmd_modes(dps=25):
    mp.mp.dps = dps
    print('# att536 ATTACKS 7/8/9: the theta-mode split.')

    def phisum(u, nmax):
        u = mp.mpf(u)
        t = mp.mpf(0)
        e2 = mp.e ** (2 * u)
        for n in range(1, nmax + 1):
            a = mp.pi * n * n * e2
            if a > 3000:
                break
            t += (2 * mp.pi ** 2 * n ** 4 * mp.e ** (mp.mpf('4.5') * u)
                  - 3 * mp.pi * n * n * mp.e ** (mp.mpf('2.5') * u)) * mp.e ** (-a)
        return t

    def Gn(v, nmax):
        """2 int_0^inf (sum_{m<=nmax} phi_m)(u) cos(vu) du -- the even extension's FT."""
        v = mp.mpf(v)
        f = lambda u: phisum(u, nmax) * mp.cos(v * u)
        return 2 * mp.fsum(panel(f, mp.mpf(i) / 20, mp.mpf(i + 1) / 20, 4)
                           for i in range(0, 80))

    print('#   G_n(v) = FT of the truncated even kernel;  G_inf = Xi(v)/2')
    print('#     v      G_1 (ground)         G_2                  G_5                  Xi(v)/2')
    for v in (0, 2, 5, 9, 14):
        print('  %6.1f  %-20s %-20s %-20s %s'
              % (v, mp.nstr(Gn(v, 1), 9), mp.nstr(Gn(v, 2), 9),
                 mp.nstr(Gn(v, 5), 9), mp.nstr(XiR(v) / 2, 9)))
        sys.stdout.flush()
    print()
    print('# DIAGONAL DOMINATION: |G_1 - G_inf| / |G_inf|  (how much the ground mode')
    print('# already carries; the rest is the off-diagonal remainder)')
    for v in (0, 2, 5, 9, 14):
        g1, gi = Gn(v, 1), XiR(v) / 2
        print('   v=%-5s  ground/full = %-14s   |off-diag|/|full| = %s'
              % (v, mp.nstr(g1 / gi, 8), mp.nstr(abs(g1 - gi) / abs(gi), 8)))
    print()
    print('# ground-mode defect density D^(1)_x(t) vs the full D_x(t), at x = 3:')
    print('#     t      D^(1)_3(t)           D_3(t) (full)        both signs agree?')
    x = mp.mpf(3)
    for ts in ('0.5', '1', '2', '4', '8'):
        t = mp.mpf(ts)
        d1 = (Gn(x, 1) ** 2 - Gn(x + t, 1) * Gn(x - t, 1)) / t ** 2
        df = (XiR(x) ** 2 / 4 - XiR(x + t) * XiR(x - t) / 4) / t ** 2
        print('  %6s   %-20s %-20s %s'
              % (ts, mp.nstr(d1, 9), mp.nstr(df, 9),
                 'yes' if (d1 > 0) == (df > 0) else 'NO -- mode split changes the sign'))
        sys.stdout.flush()


if __name__ == '__main__':
    a = sys.argv[1:]
    c = a[0] if a else 'profile'
    {'profile': cmd_profile, 'modes': cmd_modes}[c](*[int(t) for t in a[1:]])
