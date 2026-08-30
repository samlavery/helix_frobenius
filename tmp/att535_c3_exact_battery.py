"""att535 -- C3/IsHB attack battery, EXACT-IDENTITY-FIRST.

Design law for this file: never run a nested arbitrary-precision integration when an
exact identity or an existing checkpoint decides the question.  Every quantity below
is either (a) a pointwise evaluation of Xi and its derivatives, or (b) a single 1-D
integral, or (c) reused from att531/att532.

REGISTER (harmonic discipline, rule 7 <1>): the object's own scale is Xi(x)^2, which
is 8.46e-36 at x = 60.  Nothing here is normalised to 1.  DC = the Xi(x)^2 common
mode, always evaluated exactly; AC = Xi(x+t)Xi(x-t).

THE TARGET, exactly:
    Khat(y,x) := -Im[ Xi'(x+iy) * conj Xi(x+iy) ]
    C3  <=>  Khat >= 0 for all x in R, y > 0
        <=>  IsHB(xi + xi')                       [XiStructureFunction.lean]
        <=>  seat energy >= 0                     [SeatScalarCriterion.lean]
        <=>  RH.

EXACT IDENTITIES USED (each derived by hand, each checked numerically here):
  I1   What_x(eta) = G(eta/2+x) G(eta/2-x),  G = Xi/2   [Wigner transform pair]
  I2   int_R u^{2m} W_x(u) du = (-1)^m * (d/d eta)^{2m} What_x(eta) |_{eta=0}
       => the ODD-order tail primitives at r=0 are EXACT derivative expressions,
          needing no quadrature at all:
          S^{(2m+1)}_x(0) = (1/2)(-1)^m What^{(2m)}_x(0) / (2m)!
  I3   D_x(0) = G'(x)^2 - G(x)G''(x) = L1(x)/4,  L1 := Xi'^2 - Xi Xi''
  I4   int_0^inf S_x(r) dr = D_x(0)/8 = L1(x)/32            [Fourier inversion at 0]
  I5   Khat(y,x) = y*L1(x) + O(y^3)                          [y-DC of the target]
  I6   S_x'(0) = -G(x)^2/2 = -Xi(x)^2/8

CONSEQUENCE, stated at exactly its strength: the y -> 0 endpoint of C3 is the
LAGUERRE INEQUALITY L1 >= 0 for the Riemann Xi function, which is unconditional
(Csordas-Varga 1988, Thm 2.1 area; cited in automorph/hp_pencil.tex sec:leanappendix).
So C3's entire open content is the y-AC part, and the pointwise STP failure at
(x,r) = (60,0) is consistent with I4, whose left side is a known-nonnegative number.

subcommands: identities | khat | tails | defect | moments | margin | lam | scan
"""
import math
import sys

import mpmath as mp


def xi(s):
    """Pole-free spelling of xi(s) = (1/2)s(s-1)pi^{-s/2}Gamma(s/2)zeta(s).

    Uses (1/2) s Gamma(s/2) = Gamma(1 + s/2), which is regular at s = 0.  The naive
    spelling raises "gamma function pole" at s = 0, reached in the margin scan at
    z = 0 + i/2 (since s = 1/2 + i z).  Algebraically identical elsewhere.
    """
    return mp.pi ** (-s / 2) * mp.gamma(1 + s / 2) * (s - 1) * mp.zeta(s)


def Xi(z):
    return xi(mp.mpf(1) / 2 + 1j * z)


def XiR(v):
    return mp.re(Xi(mp.mpf(v)))


def Khat(y, x):
    """THE TARGET.  -Im[Xi'(z) conj Xi(z)] at z = x + i y.  One evaluation, no quadrature."""
    z = mp.mpc(x, y)
    return -mp.im(mp.diff(Xi, z) * mp.conj(Xi(z)))


def L1(x):
    x = mp.mpf(x)
    return mp.diff(XiR, x, 1) ** 2 - XiR(x) * mp.diff(XiR, x, 2)


def What(eta, x):
    """I1: the Wigner transform pair, G = Xi/2."""
    eta = mp.mpf(eta)
    x = mp.mpf(x)
    return XiR(eta / 2 + x) * XiR(eta / 2 - x) / 4


def Stail_odd(x, m):
    """I2/I3: S^{(2m+1)}_x(0) = (1/2)(-1)^m What^{(2m)}_x(0)/(2m)!  -- EXACT, no quadrature."""
    d = mp.diff(lambda e: What(e, x), mp.mpf(0), 2 * m)
    return mp.mpf(1) / 2 * (-1) ** m * d / mp.factorial(2 * m)


# ---------------------------------------------------------------- 1-D quadrature
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
    """att532 form (B).  Single 1-D integral."""
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


# ---------------------------------------------------------------- commands
def cmd_identities(dps=35):
    """ATTACKS 6, 15, 16: verify I3, I5, I6 by pointwise evaluation only."""
    mp.mp.dps = dps
    print('# att535 IDENTITY AUDIT  (dps=%d).  No nested quadrature.' % dps)
    print()
    print('# I5:  Khat(y,x)/y -> L1(x) = Xi\'^2 - Xi Xi\'\'  as y -> 0.')
    print('#      This is the y-DC of the target: the endpoint of C3 IS the')
    print('#      Laguerre inequality, unconditional (Csordas-Varga 1988).')
    print('#   x        L1(x)                 Khat(1e-3,x)/1e-3     ratio')
    for x in (0, 2, 5, 9, 14, 20, 30, 60, 100):
        l1 = L1(x)
        kr = Khat(mp.mpf('1e-3'), x) / mp.mpf('1e-3')
        print('  %5s   %-21s %-21s %s'
              % (x, mp.nstr(l1, 12), mp.nstr(kr, 12), mp.nstr(kr / l1, 10)))
        sys.stdout.flush()
    print()
    print('# I3:  D_x(0) = lim [Xi(x)^2 - Xi(x+t)Xi(x-t)]/(4 t^2) = L1(x)/4')
    for x in (0, 14, 60):
        t = mp.mpf('1e-4')
        num = (XiR(x) ** 2 - XiR(x + t) * XiR(x - t)) / (4 * t ** 2)
        print('   x=%-5s  finite-diff D_x(0) = %-20s   L1/4 = %-20s  rel = %s'
              % (x, mp.nstr(num, 10), mp.nstr(L1(x) / 4, 10),
                 mp.nstr(abs(num - L1(x) / 4) / abs(L1(x) / 4), 6)))
    print()
    print('# I6:  S_x\'(0) = -Xi(x)^2/8   (boundary-term audit for the IBP)')
    for x in (0, 2, 14):
        h = mp.mpf('1e-3')
        d = (S_B(x, h) - S_B(x, 0)) / h
        print('   x=%-5s  (S(h)-S(0))/h = %-20s   -Xi^2/8 = %-20s  rel = %s'
              % (x, mp.nstr(d, 10), mp.nstr(-XiR(x) ** 2 / 8, 10),
                 mp.nstr(abs(d + XiR(x) ** 2 / 8) / (XiR(x) ** 2 / 8), 6)))
        sys.stdout.flush()


def cmd_tails(dps=35):
    """ATTACK 1: tail primitives.  ODD orders are EXACT (I2); n=2 is the falsified STP."""
    mp.mp.dps = dps
    print('# att535 ATTACK 1: tail primitives at r = 0.')
    print('#   n = 2 : S_x(0), the STP -- FALSIFIED at x = 60 (att532).')
    print('#   n = 2m+1 : EXACT via I2, no quadrature.  n=1 is Xi(x)^2/8 >= 0 always;')
    print('#              n=3 is L1(x)/32 >= 0 by the Laguerre inequality.')
    print('#     x         n=1 (exact)          n=2 (STP)            n=3 (exact)          n=5 (exact)')
    for x in (0, 14, 30, 59.347, 60, 60.832, 80, 100):
        row = '  %9.3f' % x
        row += '  %-20s' % mp.nstr(Stail_odd(x, 0), 10)
        row += '  %-20s' % mp.nstr(S_B(x, 0), 10)
        row += '  %-20s' % mp.nstr(Stail_odd(x, 1), 10)
        row += '  %-20s' % mp.nstr(Stail_odd(x, 2), 10)
        print(row)
        sys.stdout.flush()
    print()
    print('# cross-check of I2 at m=1 against I4: S^{(3)}_x(0) should equal L1(x)/32')
    for x in (0, 14, 60):
        print('   x=%-5s  S^{(3)} = %-20s   L1/32 = %-20s  rel = %s'
              % (x, mp.nstr(Stail_odd(x, 1), 10), mp.nstr(L1(x) / 32, 10),
                 mp.nstr(abs(Stail_odd(x, 1) - L1(x) / 32) / abs(L1(x) / 32), 6)))


def cmd_defect(dps=35):
    """ATTACKS 3, 17: locate the sign failure of the defect density D_x, pointwise."""
    mp.mp.dps = dps
    print('# att535 ATTACKS 3/17: the Wigner-Newman defect density')
    print('#   D_x(t) = [Xi(x)^2 - Xi(x+t)Xi(x-t)] / (4 t^2)')
    print('#   D_x >= 0 pointwise (the GLOBAL Wigner/log-concavity inequality)')
    print('#   would imply STP.  Where does it fail?  Pointwise evaluation only.')
    print('#     x        t         Xi(x)^2              Xi(x+t)Xi(x-t)       D_x(t)      sign')
    for x in (60,):
        for ts in ('0.5', '1', '2', '3', '5', '8', '12', '20', '30', '45', '58'):
            t = mp.mpf(ts)
            X2 = XiR(x) ** 2
            pr = XiR(x + t) * XiR(x - t)
            d = (X2 - pr) / (4 * t ** 2)
            print('  %7s %9s  %-20s %-20s %-11s %s'
                  % (x, ts, mp.nstr(X2, 8), mp.nstr(pr, 8), mp.nstr(d, 6),
                     'NEG <<<' if d < 0 else '+'))
            sys.stdout.flush()
    print('#  => D_60 is NOT nonnegative, so the pointwise route to STP is dead at x=60')
    print('#     independently of the (falsified) integrated statement.')
    print()
    print('# control at a benign abscissa (x = 0), same instrument:')
    for ts in ('0.5', '2', '8', '30'):
        t = mp.mpf(ts)
        d = (XiR(0) ** 2 - XiR(t) * XiR(-t)) / (4 * t ** 2)
        print('   x=0  t=%-5s  D = %-14s %s' % (ts, mp.nstr(d, 6), 'NEG' if d < 0 else '+'))


def cmd_khat(dps=30):
    """ATTACKS 4, 5: hostile scan of the target, x in [0,100], y in [1e-4, 3]."""
    mp.mp.dps = dps
    print('# att535 ATTACKS 4/5: Khat(y,x) = -Im[Xi\' conj Xi], the C3/IsHB defect.')
    print('# tabulated as Khat / (y * |Xi(x+iy)|^2)  -- O(1) in the harmonic register.')
    print('# Khat >= 0 everywhere <=> RH.  A ROBUST NEGATIVE WOULD REFUTE RH.')
    ys = ['1e-4', '1e-3', '1e-2', '0.1', '0.3', '0.49', '0.5', '1', '2', '3']
    print('#      x   ' + ''.join('%11s' % y for y in ys))
    worst = (None, None, mp.inf)
    neg = 0
    for x in [0, 1, 3, 6, 10, 14.134725, 15, 21.022, 25, 30, 40, 50,
              59.347, 60, 60.832, 70, 80, 90, 100]:
        row = '  %8.3f' % x
        for ys_ in ys:
            y = mp.mpf(ys_)
            z = mp.mpc(x, y)
            k = Khat(y, x)
            nrm = abs(Xi(z)) ** 2 * y
            v = k / nrm
            if v < worst[2]:
                worst = (x, ys_, v)
            if k < 0:
                neg += 1
            row += '%11.4g' % float(v)
        print(row)
        sys.stdout.flush()
    print('# grid minimum of Khat/(y|Xi|^2) = %s  at x=%s, y=%s'
          % (mp.nstr(worst[2], 8), worst[0], worst[1]))
    print('# raw negatives of Khat found on this grid: %d' % neg)


def cmd_margin(dps=30):
    """ATTACKS 13, 14: the de Branges modulus margin, directly."""
    mp.mp.dps = dps
    print('# att535 ATTACKS 13/14: HB modulus ratio for E = xi(1/2-iz) + xi\'(1/2-iz).')
    print('# Verified identification (att534 audit): E = Xi + i Xi\',  E* = Xi - i Xi\'.')
    print('# IsHB <=> ratio < 1 on Im z > 0;  ratio == 1 on Im z = 0 exactly.')
    print('#      x        y        ‖E*‖/‖E‖             1 - ratio')
    for x in (0, 6, 14.134725, 30, 60, 100):
        for ys in ('1e-3', '0.01', '0.1', '0.4', '0.499', '0.5', '1.0', '3.0'):
            y = mp.mpf(ys)
            z = mp.mpc(x, y)
            X, D = Xi(z), mp.diff(Xi, z)
            rat = abs(X - 1j * D) / abs(X + 1j * D)
            print('   %8.4f %8s  %-20s %s'
                  % (x, ys, mp.nstr(rat, 14), mp.nstr(1 - rat, 8)))
            sys.stdout.flush()


def cmd_moments(dps=30):
    """ATTACKS 10, 11, 12: the repo's moment data, Turan family C_j, Jensen at n=0."""
    mp.mp.dps = dps
    print('# att535 ATTACKS 10/11/12: kernel moments, Hankel PD, the C_j family,')
    print('# and the Jensen/Laguerre coefficients at n = 0.')
    print('# K = Lean riemannXiKernel = 4*P0 = 2*Riemann Phi.  m_k = int_0^inf u^k K du.')

    def K(u):
        u = mp.mpf(u)
        t = mp.mpf(0)
        for n in range(1, 30):
            a = mp.pi * n * n * mp.e ** (2 * u)
            if a > 3000:
                break
            t += (2 * mp.pi ** 2 * n ** 4 * mp.e ** (mp.mpf('4.5') * u)
                  - 3 * mp.pi * n * n * mp.e ** (mp.mpf('2.5') * u)) * mp.e ** (-a)
        return 4 * t

    m = {}
    for k in range(0, 15):
        m[k] = mp.fsum(panel(lambda u: u ** k * K(u), mp.mpf(i) / 8, mp.mpf(i + 1) / 8, 4)
                       for i in range(0, 32))
    print('#  k      m_k')
    for k in range(0, 9):
        print('  %3d   %s' % (k, mp.nstr(m[k], 14)))
    print()
    print('# central Turan  3 m_2^2 > m_0 m_4  (Csordas-Norfolk-Varga 1986, m=1 case)')
    print('   3 m_2^2      = %s' % mp.nstr(3 * m[2] ** 2, 12))
    print('   m_0 m_4      = %s' % mp.nstr(m[0] * m[4], 12))
    print('   m_0 m_4/m_2^2= %s   (paper reports 2.7911, margin 6.96%%)'
          % mp.nstr(m[0] * m[4] / m[2] ** 2, 10))
    print()
    print('# the C_j family (hp_pencil.tex sec:leanappendix item 4):')
    print('#   C_j = (1/4)[(2j+1) m_{2j}^2 - (2j-1) m_{2j-2} m_{2j+2}]')
    for j in range(1, 7):
        Cj = mp.mpf(1) / 4 * ((2 * j + 1) * m[2 * j] ** 2
                              - (2 * j - 1) * m[2 * j - 2] * m[2 * j + 2])
        ratio = ((2 * j + 1) * m[2 * j] ** 2) / ((2 * j - 1) * m[2 * j - 2] * m[2 * j + 2])
        print('   j=%d   C_j = %-22s ratio = %-12s %s'
              % (j, mp.nstr(Cj, 10), mp.nstr(ratio, 8), 'POS' if Cj > 0 else 'NEG <<<'))
    print()
    print('# Hankel moment matrices [m_{i+j}] positive definite? (xiMomentMatrix_posDef)')
    for n in (2, 3, 4, 5):
        A = mp.matrix(n, n)
        for i in range(n):
            for j in range(n):
                A[i, j] = m[i + j]
        try:
            mp.cholesky(A)
            print('   n=%d  Cholesky OK -> positive definite     det = %s'
                  % (n, mp.nstr(mp.det(A), 8)))
        except Exception as e:
            print('   n=%d  NOT PD: %s' % (n, e))
    print()
    print('# Jensen at n = 0: Xi(x) = sum_k (-1)^k a_k x^{2k}/(2k)!, a_k = int_R u^{2k} Phi')
    print('#   a_k = m_{2k}/2  (Phi = K/2 on the half line, doubled by evenness)')
    print('#   Jensen polynomial J^{d,0}(X) = sum_j binom(d,j) gam_j X^j, gam_j = a_j/(2j)!')
    gam = [m[2 * k] / 2 / mp.factorial(2 * k) for k in range(0, 6)]
    for d in (2, 3, 4):
        coef = [mp.binomial(d, j) * gam[j] for j in range(d + 1)]
        rts = mp.polyroots(list(reversed(coef)), maxsteps=200, extraprec=200)
        allreal = all(abs(mp.im(r)) < mp.mpf('1e-20') * max(1, abs(r)) for r in rts)
        print('   d=%d  roots %s  -> hyperbolic: %s'
              % (d, [mp.nstr(r, 6) for r in rts], allreal))


def cmd_lam(dps=25):
    """ATTACK 19: heat-flow (de Bruijn-Newman) deformation at the counterexample."""
    mp.mp.dps = dps
    print('# att535 ATTACK 19: heat flow Xi_lam = Gaussian(4 lam) smoothing of Xi.')
    print('# One 1-D smoothing integral per evaluation; no nesting beyond that.')
    print('# Question: does the STP sign at x = 60 recover under the flow?')

    def Xilam(v, lam):
        v, lam = mp.mpf(v), mp.mpf(lam)
        if lam == 0:
            return XiR(v)
        s = mp.sqrt(4 * lam)
        R = 7 * s
        f = lambda t: XiR(v + t) * mp.exp(-t ** 2 / (4 * lam))
        tot = mp.fsum(panel(f, -R + i * (2 * R / 24), -R + (i + 1) * (2 * R / 24), 4)
                      for i in range(24))
        return tot / mp.sqrt(4 * mp.pi * lam)

    for lams in ('0', '0.02', '0.1', '0.4', '1.0'):
        lam = mp.mpf(lams)
        XX = (lambda v: Xilam(v, lam))
        x = mp.mpf(60)
        X2 = XX(x) ** 2
        f = lambda t: (X2 - XX(x + t) * XX(x - t)) / t ** 2 if t else mp.mpf(0)
        ed, e = [mp.mpf(0)], mp.mpf('1e-6')
        while e < mp.mpf('0.5'):
            ed.append(e); e *= 10
        e = mp.mpf('0.5')
        while e < 100:
            ed.append(e); e += mp.mpf('1.0')
        tot = mp.fsum(panel(f, ed[i], ed[i + 1], 3) for i in range(len(ed) - 1))
        val = (tot + X2 / 100) / (8 * mp.pi)
        print('   lam=%-7s  Xi_lam(60)=%-18s  S^lam_60(0)=%-20s  %s'
              % (lams, mp.nstr(XX(x), 8), mp.nstr(val, 8),
                 'NEG' if val < 0 else 'POS -- sign recovered'))
        sys.stdout.flush()


def cmd_scan(dps=30, lo=0, hi=100, step=2):
    """ATTACKS 3/20: sign map of S_x(0) over x in [0,100], and the renormalised form."""
    mp.mp.dps = dps
    print('# att535 ATTACKS 3/20: sign map of S_x(0) over x in [%s,%s] step %s'
          % (lo, hi, step))
    print('#   also the renormalised ratios S_x(0)/Xi(x)^2 and S_x(0)/(L1(x)/32),')
    print('#   the latter comparing the falsified pointwise value against the')
    print('#   unconditionally nonnegative integral I4.')
    print('#      x     Xi(x)             S_x(0)              S/Xi^2        S/(L1/32)   sign')
    x = mp.mpf(lo)
    neg = []
    while x <= mp.mpf(hi) + mp.mpf('1e-9'):
        v = S_B(x, 0, T=120, deg=4)
        X = XiR(x)
        l = L1(x) / 32
        if v < 0:
            neg.append(float(x))
        print('  %7s  %-17s %-19s %-13s %-11s %s'
              % (mp.nstr(x, 6), mp.nstr(X, 8), mp.nstr(v, 10),
                 mp.nstr(v / X ** 2, 6) if X != 0 else 'inf',
                 mp.nstr(v / l, 6) if l != 0 else 'inf',
                 'NEG <<<' if v < 0 else '+'))
        sys.stdout.flush()
        x += mp.mpf(step)
    print('# NEGATIVE S_x(0) at x = %s' % neg)


if __name__ == '__main__':
    a = sys.argv[1:]
    c = a[0] if a else 'identities'
    {'identities': cmd_identities, 'khat': cmd_khat, 'tails': cmd_tails,
     'defect': cmd_defect, 'moments': cmd_moments, 'margin': cmd_margin,
     'lam': cmd_lam, 'scan': cmd_scan}[c](*[int(t) for t in a[1:]])
