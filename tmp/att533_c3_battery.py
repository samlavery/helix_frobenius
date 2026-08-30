"""att533 -- C3/IsHB battery.  All objects in the Xi register; NOTHING is unit-1.

OBJECTS (Xi(v) = xi(1/2 + i v), real on R; Xi' etc. by mp.diff).

  Khat(y,x) = -Im[ Xi'(x+iy) * conj Xi(x+iy) ]                          [THE TARGET]
            = 2 int_0^inf u * (e^{-2yu} - e^{2yu})/(-2) ... = 8 int_0^inf u sinh(2yu) W_x(u) du
              in the att530 (Phi = P0) normalisation.
  C3  <=>  Khat(y,x) >= 0 for all x in R, y > 0  <=>  IsHB(xi + xi')  <=>  RH.

  W_x(u) : Wigner slice, What_x(eta) = G(eta/2+x) G(eta/2-x),  G = Xi/2 (P0 convention)
  S_x(r) = (1/(8 pi)) int_0^inf [Xi(x)^2 - Xi(x+t)Xi(x-t)] cos(2 r t) t^{-2} dt   [att532]
  D_x(t) = [Xi(x)^2 - Xi(x+t)Xi(x-t)]/t^2      (Wigner-Newman defect density)
           S_x(r) = (1/(32 pi)) * Dhat_x(2r) ;  global STP <=> D_x positive-definite.

DERIVED, TO BE CHECKED HERE (harmonic DC-first: the y-DC of C3):
  Khat(y,x) = y * L1(x) + O(y^3),   L1 = Xi'^2 - Xi Xi''      [the LAGUERRE expression]
  int_0^inf S_x(r) dr = L1(x)/32
So the y -> 0 endpoint of C3 is the Laguerre inequality (Csordas-Varga 1988,
UNCONDITIONAL), and the entire open content of C3 is the y-AC part.

subcommands: laguerre | khat | tails | lambda | modes | margin | scan
"""
import sys
import mpmath as mp


def xi(s):
    return mp.mpf(1) / 2 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Xi(z):
    """Xi(z) = xi(1/2 + i z); complex-analytic, real on the reals."""
    return xi(mp.mpf(1) / 2 + 1j * z)


def XiR(v):
    return mp.re(Xi(mp.mpf(v)))


def Khat(y, x):
    """-Im[Xi'(z) conj Xi(z)] at z = x + i y."""
    z = mp.mpc(x, y)
    d = mp.diff(Xi, z)
    return -mp.im(d * mp.conj(Xi(z)))


def L1(x):
    """Laguerre expression Xi'(x)^2 - Xi(x) Xi''(x) on the real axis."""
    x = mp.mpf(x)
    d1 = mp.diff(XiR, x, 1)
    d2 = mp.diff(XiR, x, 2)
    return d1 ** 2 - XiR(x) * d2


# ---------------------------------------------------------------- quadrature
_GL = {}


def gl(n):
    k = (n, mp.mp.dps)
    if k not in _GL:
        _GL[k] = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(
            mp.mpf(-1), mp.mpf(1), n, mp.mp.prec)
    return _GL[k]


def panel(f, a, b, deg=5):
    nd = gl(deg)
    a, b = mp.mpf(a), mp.mpf(b)
    h, m = (b - a) / 2, (a + b) / 2
    return h * mp.fsum(w * f(m + h * t) for t, w in nd)


def S_xi(x, r, T=150, deg=5, ph=mp.mpf('0.5')):
    """att532's closed form for the second tail primitive."""
    x, r, T = mp.mpf(x), mp.mpf(r), mp.mpf(T)
    Xx2 = XiR(x) ** 2

    def f(t):
        if t == 0:
            return mp.mpf(0)
        return (Xx2 - XiR(x + t) * XiR(x - t)) * mp.cos(2 * r * t) / t ** 2

    ed, e = [mp.mpf(0)], mp.mpf('1e-8')
    while e < ph:
        ed.append(e); e *= 10
    e = ph
    while e < T:
        ed.append(e); e += ph
    ed.append(T)
    tot = mp.fsum(panel(f, ed[i], ed[i + 1], deg) for i in range(len(ed) - 1))
    a = 2 * r
    tail = Xx2 / T if a == 0 else Xx2 * (mp.cos(a * T) / T - a * (mp.pi / 2 - mp.si(a * T)))
    return (tot + tail) / (8 * mp.pi)


def Sn_xi(x, n, T=150, deg=5, ph=mp.mpf('0.5')):
    """n-th tail primitive at r=0:  S^{(n)}_x(0) = int_0^inf u^{n-1}/(n-1)! W_x(u) du.

    In the tau register:  int_R h(u) W_x(u) du = (1/2 pi) int_R hhat(t) What(t) dt with
    What_x(eta) = G(eta/2+x)G(eta/2-x).  For h(u) = |u|^{n-1}/(n-1)! the transform is
    the finite part of  2 cos(pi n/2) Gamma(n) / |t|^n  ... -- rather than fight the
    distributional constants we integrate the tail primitive DIRECTLY in r:

      S^{(n)}_x(0) = int_0^inf r^{n-3}/(n-3)! * S_x(r) dr      (n >= 3),
    since S_x'' = W_x and repeated integration by parts with vanishing boundary data.
    n = 2 is S_x(0) itself.
    """
    if n == 2:
        return S_xi(x, 0, T, deg, ph)
    k = n - 3

    def g(r):
        return r ** k / mp.factorial(k) * S_xi(x, r, T, deg, ph)
    # S_x(r) decays superexponentially; r <= 3 is far past the support
    return mp.fsum(panel(g, mp.mpf(i) / 4, mp.mpf(i + 1) / 4, 4) for i in range(0, 12))


# ---------------------------------------------------------------- subcommands
def cmd_laguerre(dps=40):
    mp.mp.dps = dps
    print('# ATTACK 6 + 15:  y-DC of C3 is the Laguerre inequality.')
    print('#   claim A:  Khat(y,x)/y -> L1(x)  as y -> 0')
    print('#   claim B:  int_0^inf S_x(r) dr = L1(x)/32')
    print('#   x      L1(x)               Khat(y,x)/y  [y=1e-3]   ratio     '
          'int S / (L1/32)')
    for x in (0, 2, 5, 9, 14, 20, 30, 60):
        l1 = L1(x)
        kr = Khat(mp.mpf('1e-3'), x) / mp.mpf('1e-3')
        ints = mp.fsum(panel(lambda r: S_xi(x, r, T=120), mp.mpf(i) / 4,
                             mp.mpf(i + 1) / 4, 4) for i in range(0, 12))
        print('  %4d   %-19s %-19s %-9s %s'
              % (x, mp.nstr(l1, 10), mp.nstr(kr, 10),
                 mp.nstr(kr / l1, 6), mp.nstr(ints / (l1 / 32), 8)))
        sys.stdout.flush()


def cmd_khat(dps=40):
    """ATTACK 4/5: hostile scan of the target Khat(y,x); two independent readings."""
    mp.mp.dps = dps
    print('# ATTACK 4/5:  Khat(y,x) = -Im[Xi\' conj Xi]  hostile scan.')
    print('# normalised by y*|Xi(x+iy)|^2 so the number is O(1) (harmonic register).')
    ys = ['1e-4', '1e-3', '1e-2', '0.1', '0.3', '0.49', '0.5', '1', '2', '3']
    print('#    x  ' + ''.join('%11s' % y for y in ys))
    worst = (None, None, mp.inf)
    for x in [0, 1, 3, 6, 10, 14.134725, 15, 21.02, 25, 30, 40, 50, 59.347, 60,
              60.832, 70, 80, 90, 100]:
        row = '  %7.3f' % x
        for ys_ in ys:
            y = mp.mpf(ys_)
            z = mp.mpc(x, y)
            k = Khat(y, x)
            nrm = abs(Xi(z)) ** 2 * y
            v = k / nrm if nrm != 0 else mp.mpf(0)
            if v < worst[2]:
                worst = (x, ys_, v)
            row += '%11.4g' % float(v)
        print(row)
        sys.stdout.flush()
    print('#  min over grid of Khat/(y|Xi|^2) = %s at x=%s y=%s'
          % (mp.nstr(worst[2], 8), worst[0], worst[1]))
    print('#  (Khat >= 0 everywhere <=> RH; a robust NEGATIVE would refute RH.)')


def cmd_tails(dps=50):
    """ATTACK 1: tail primitives of orders 2..6 at the STP counterexample."""
    mp.mp.dps = dps
    print('# ATTACK 1: n-th tail primitives at r=0.  n=2 is the falsified STP.')
    print('#   x        n=2                  n=3                  n=4                  n=5')
    for x in (0, 14, 30, 59.347, 60, 60.832, 80):
        row = '  %8.3f' % x
        for n in (2, 3, 4, 5):
            row += '  %-19s' % mp.nstr(Sn_xi(x, n, T=120), 10)
        print(row)
        sys.stdout.flush()


def cmd_lambda(dps=40):
    """ATTACK 19: de Bruijn-Newman deformation -- where does S_x(0) recover its sign?

    Xi_lam(v) = int Phi(u) e^{lam u^2} e^{ivu} du.  In the tau register the only change
    is Xi -> Xi_lam; we compute Xi_lam by its own quadrature over the Phi plane, which
    is cheap at moderate |v| but hopeless at v = 60.  Instead we use the HEAT-FLOW form
    Xi_lam = e^{lam d^2/dv^2} Xi, i.e. the Gaussian smoothing
        Xi_lam(v) = (4 pi lam)^{-1/2} int Xi(v') e^{-(v-v')^2/(4 lam)} dv'
    valid for lam > 0 (de Bruijn).  Sign of S^{lam}_60(0) as lam grows.
    """
    mp.mp.dps = dps
    print('# ATTACK 19: heat-flow (de Bruijn-Newman) deformation at x=60.')
    print('# S^lam_60(0) with Xi_lam = Gaussian(4 lam)-smoothing of Xi.')

    def Xilam(v, lam):
        v, lam = mp.mpf(v), mp.mpf(lam)
        s = mp.sqrt(4 * lam)
        R = 8 * s
        f = lambda t: XiR(v + t) * mp.exp(-t ** 2 / (4 * lam))
        tot = mp.fsum(panel(f, -R + i * (2 * R / 64), -R + (i + 1) * (2 * R / 64), 4)
                      for i in range(64))
        return tot / (mp.sqrt(4 * mp.pi * lam))

    for lam in ('0', '0.001', '0.01', '0.05', '0.1', '0.3', '1.0'):
        lam = mp.mpf(lam)
        XX = (lambda v: XiR(v)) if lam == 0 else (lambda v: Xilam(v, lam))
        x = mp.mpf(60)
        Xx2 = XX(x) ** 2
        f = lambda t: (Xx2 - XX(x + t) * XX(x - t)) / t ** 2 if t != 0 else mp.mpf(0)
        ed, e = [mp.mpf(0)], mp.mpf('1e-8')
        while e < mp.mpf('0.5'):
            ed.append(e); e *= 10
        e = mp.mpf('0.5')
        while e < 120:
            ed.append(e); e += mp.mpf('0.5')
        tot = mp.fsum(panel(f, ed[i], ed[i + 1], 4) for i in range(len(ed) - 1))
        val = (tot + Xx2 / 120) / (8 * mp.pi)
        print('   lam=%-8s  Xi_lam(60)=%-16s  S=%-20s %s'
              % (mp.nstr(lam, 6), mp.nstr(XX(x), 8), mp.nstr(val, 10),
                 'NEG' if val < 0 else '+'))
        sys.stdout.flush()


def cmd_margin(dps=40):
    """ATTACK 13: the de Branges modulus margin  ‖E*‖/‖E‖  at hostile z."""
    mp.mp.dps = dps
    print('# ATTACK 13: HB modulus ratio ‖E*(z)‖/‖E(z)‖ for E = Xi + i Xi\'.')
    print('#   E(z)  = Xi(z) + i Xi\'(z),  E*(z) = Xi(z) - i Xi\'(z)')
    print('#   IsHB  <=>  ratio < 1 on Im z > 0.   ratio = 1 exactly on Im z = 0.')
    print('#      x       y        ratio            1-ratio')
    for x in (0, 6, 14.134725, 30, 60, 100):
        for ys in ('1e-3', '0.01', '0.1', '0.4', '0.499', '0.5', '1.0', '3.0'):
            y = mp.mpf(ys)
            z = mp.mpc(x, y)
            X = Xi(z); D = mp.diff(Xi, z)
            E = X + 1j * D
            Es = X - 1j * D
            rat = abs(Es) / abs(E)
            print('   %7.3f %8s  %-16s %s'
                  % (x, ys, mp.nstr(rat, 12), mp.nstr(1 - rat, 8)))
            sys.stdout.flush()


def cmd_modes(dps=30):
    """ATTACK 9: single-theta-mode control.  Does mode n=1 alone reproduce the failure?"""
    import math
    mp.mp.dps = dps
    print('# ATTACK 9: theta-mode split.  Phi = sum_n phi_n; test the ground mode alone.')

    def phi_n(u, n):
        u = float(u)
        a = math.pi * n * n * math.exp(2 * u)
        if a > 700:
            return 0.0
        return (2 * math.pi ** 2 * n ** 4 * math.exp(4.5 * u)
                - 3 * math.pi * n * n * math.exp(2.5 * u)) * math.exp(-a)

    def Gn(v, nmax):
        """int_R sum_{n<=nmax} phi_n(|u|) e^{ivu} du = 2 int_0^inf ... cos(vu) du."""
        f = lambda u: mp.fsum(mp.mpf(phi_n(u, n)) for n in range(1, nmax + 1)) * mp.cos(v * u)
        tot = mp.fsum(panel(f, mp.mpf(i) / 40, mp.mpf(i + 1) / 40, 5) for i in range(0, 160))
        # negative-u half by evenness of Phi (Phi(-u)=Phi(u) only for the FULL sum;
        # for a truncated sum use the explicit reflection Phi_trunc(|u|))
        return 2 * tot

    print('#   v     G_1(v) (ground mode)   G_3(v)              Xi(v)/2 (all modes)')
    for v in (0, 2, 5, 9, 14):
        print('  %5.1f  %-20s %-19s %s'
              % (v, mp.nstr(Gn(mp.mpf(v), 1), 10), mp.nstr(Gn(mp.mpf(v), 3), 10),
                 mp.nstr(XiR(v) / 2, 10)))
        sys.stdout.flush()
    print('# ground-mode Wigner-Newman defect D^{(1)}_x(t) at x = 3:')
    for t in ('0.5', '1', '2', '4'):
        t = mp.mpf(t)
        x = mp.mpf(3)
        d = (Gn(x, 1) ** 2 - Gn(x + t, 1) * Gn(x - t, 1)) / t ** 2
        dall = (XiR(x) ** 2 / 4 - XiR(x + t) * XiR(x - t) / 4) / t ** 2
        print('    t=%-5s  ground %-18s  all %s' % (mp.nstr(t, 4), mp.nstr(d, 8),
                                                    mp.nstr(dall, 8)))


def cmd_scan(dps=40, lo=0, hi=100, step=1):
    """ATTACK 3/20: sign map of S_x(0) over x in [0,100]."""
    mp.mp.dps = dps
    print('# ATTACK 3/20: sign map of S_x(0) (the falsified STP) over x in [%s,%s]'
          % (lo, hi))
    print('#      x     Xi(x)              S_x(0)               S_x(0)/Xi(x)^2   sign')
    x = mp.mpf(lo)
    neg = []
    while x <= mp.mpf(hi) + mp.mpf('1e-9'):
        v = S_xi(x, 0, T=120, deg=4)
        X = XiR(x)
        r = v / X ** 2 if X != 0 else mp.mpf('nan')
        if v < 0:
            neg.append(float(x))
        print('  %7s  %-18s %-20s %-16s %s'
              % (mp.nstr(x, 6), mp.nstr(X, 8), mp.nstr(v, 10), mp.nstr(r, 8),
                 'NEG <<<' if v < 0 else '+'))
        sys.stdout.flush()
        x += mp.mpf(step)
    print('# NEGATIVE at x = %s' % neg)


if __name__ == '__main__':
    a = sys.argv[1:]
    c = a[0] if a else 'laguerre'
    rest = [float(t) if '.' in t else int(t) for t in a[1:]]
    {'laguerre': cmd_laguerre, 'khat': cmd_khat, 'tails': cmd_tails,
     'lambda': cmd_lambda, 'margin': cmd_margin, 'modes': cmd_modes,
     'scan': cmd_scan}[c](*rest)
