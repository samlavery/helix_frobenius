"""att543 -- C3 batch 4.  THE CELL DENSITY IS A MACDONALD FUNCTION OF IMAGINARY ORDER.

Derivation (exact for the n=1 diagonal of the theta series; all steps reversible).

Riemann's kernel, even extension:
  phi(u) = Phi(|u|),  Phi(t) = sum_n (4 pi^2 n^4 e^{9t/2} - 6 pi n^2 e^{5t/2}) e^{-pi n^2 e^{2t}}
  Phi_1(t) = 2 pi e^{5t/2} (2 pi e^{2t} - 3) e^{-pi e^{2t}}

Cell (Wigner) density:
  C(u,x) = 2 int_R phi(u+v) phi(u-v) cos(2xv) dv

For u > 0 the n=1 diagonal is EXACT in closed form.  With a := 2 pi e^{2u}:
  Phi_1(u+v)Phi_1(u-v) = [16 pi^4 e^{9u} - 48 pi^3 e^{7u} cosh 2v + 36 pi^2 e^{5u}]
                          * e^{-a cosh 2v}
and with w = 2v, using  K_{i x}(a) = int_0^inf e^{-a cosh w} cos(xw) dw  and
int_0^inf cosh w e^{-a cosh w} cos(xw) dw = -dK/da:

  ***  C_11(u,x) = 2[ (16 pi^4 e^{9u} + 36 pi^2 e^{5u}) K_{ix}(a) + 48 pi^3 e^{7u} K'_{ix}(a) ]

As a -> inf, K'/K -> -1 and the bracket collapses to a PERFECT SQUARE:
  C_11 ~ 8 pi^2 e^{5u} (2 pi e^{2u} - 3)^2 K_{ix}(2 pi e^{2u})
so THE SIGN OF C AT LARGE u IS THE SIGN OF K_{ix}(2 pi e^{2u}).

K_{ix}(a) for real x is real; it oscillates for a < x and is POSITIVE and monotone
decreasing for a > x (turning point a = x).  Consequence, if it holds:

  C(u,x) > 0  for  u > u0(x) := (1/2) log(x / 2 pi)

so every ramp primitive is positive beyond u0, and uniform quadratic-ramp positivity
reduces to the COMPACT window 0 <= R <= u0(x).   u0(60) = 1.128,  u0(88) = 1.320.

INDEPENDENT CHECK of C, cancellation-free, from the batch-3 identity
int_R e^{-i lam u} C(u,x) du = Xi(x+lam/2) Xi(x-lam/2):
  C(u,x) = (2/pi) int_0^inf Xi(x+t) Xi(x-t) cos(2 t u) dt

Decision rule, PRE-REGISTERED:
  (a) Bessel formula vs Xi route agree to <= 1e-6 relative for u >= 0.3  -> identification CONFIRMED
  (b) sign(C) == sign(K_{ix}(2 pi e^{2u})) at every probe                -> sign law CONFIRMED
  (c) zero count of K_{ix}(a) on (2pi, x) matches batch-3's measured
      sign-change count of u -> C(u,x) on (0, 1.6]                       -> mechanism CONFIRMED
PREDICTION: all three confirm; (c) is the one that could fail, since batch-3 counted on
a fixed window |u| <= 1.6 rather than out to u0.

USAGE: python3 att543_c3b4_bessel.py <cmd>
   verify x        -- Bessel form vs Xi route, and the sign law, on a u-probe
   zeros  x        -- zeros of K_{ix}(a) on (2pi, x) and the implied sign-change count
"""
import sys
import mpmath as mp

_XI = {}


def xi(s):
    return mp.mpf(1) / 2 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Xi(v):
    k = (mp.mpf(v), mp.mp.prec)
    if k not in _XI:
        _XI[k] = mp.re(xi(mp.mpf(1) / 2 + 1j * mp.mpf(v)))
    return _XI[k]


def Kix(x, a):
    """K_{ix}(a), real for real x and a > 0."""
    return mp.re(mp.besselk(1j * mp.mpf(x), mp.mpf(a)))


def dKix(x, a):
    return mp.re(mp.diff(lambda t: mp.besselk(1j * mp.mpf(x), t), mp.mpf(a)))


def C_bessel(u, x):
    """The n=1 diagonal closed form."""
    u, x = mp.mpf(u), mp.mpf(x)
    a = 2 * mp.pi * mp.e ** (2 * u)
    p = mp.pi
    return 2 * ((16 * p ** 4 * mp.e ** (9 * u) + 36 * p ** 2 * mp.e ** (5 * u)) * Kix(x, a)
                + 48 * p ** 3 * mp.e ** (7 * u) * dKix(x, a))


def C_bessel_sq(u, x):
    """The large-a collapse:  8 pi^2 e^{5u} (2 pi e^{2u} - 3)^2 K_{ix}(a)."""
    u, x = mp.mpf(u), mp.mpf(x)
    a = 2 * mp.pi * mp.e ** (2 * u)
    return 8 * mp.pi ** 2 * mp.e ** (5 * u) * (2 * mp.pi * mp.e ** (2 * u) - 3) ** 2 * Kix(x, a)


def C_xi(u, x, T=60, deg=5, panel=mp.mpf('0.5')):
    """C(u,x) = (2/pi) int_0^inf Xi(x+t) Xi(x-t) cos(2 t u) dt."""
    u, x, T = mp.mpf(u), mp.mpf(x), mp.mpf(T)
    nodes = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(
        mp.mpf(-1), mp.mpf(1), deg, mp.mp.prec)

    def f(t):
        return Xi(x + t) * Xi(x - t) * mp.cos(2 * t * u)

    tot = mp.mpf(0)
    e = mp.mpf(0)
    while e < T:
        b = min(e + panel, T)
        half, mid = (b - e) / 2, (b + e) / 2
        tot += half * mp.fsum(w * f(mid + half * tt) for tt, w in nodes)
        e = b
    return 2 * tot / mp.pi


def cmd_verify(x, dps=30):
    mp.mp.dps = dps
    x = mp.mpf(x)
    u0 = mp.log(x / (2 * mp.pi)) / 2
    print('# att543 VERIFY  x = %s   dps=%d' % (mp.nstr(x, 10), dps))
    print('#   u0(x) = (1/2)log(x/2pi) = %s   <- predicted last sign change of C'
          % mp.nstr(u0, 10))
    print('#     u        C (Xi route)          C_11 (Bessel)         rel.diff      '
          'K_ix(a)              sign match')
    for us in ['0.2', '0.3', '0.4', '0.5', '0.6', '0.8', '1.0', '1.2', '1.5']:
        u = mp.mpf(us)
        a = 2 * mp.pi * mp.e ** (2 * u)
        cx = C_xi(u, x)
        cb = C_bessel(u, x)
        kk = Kix(x, a)
        rel = abs(cx - cb) / max(abs(cx), abs(cb)) if max(abs(cx), abs(cb)) > 0 else 0
        smatch = 'yes' if (cx > 0) == (kk > 0) else 'NO <<<'
        print('  %6s  %-21s %-21s %-13s %-20s %s'
              % (us, mp.nstr(cx, 12), mp.nstr(cb, 12), mp.nstr(rel, 4),
                 mp.nstr(kk, 12), smatch))
        sys.stdout.flush()
    print('#   (a > x  <=>  u > u0;  a(u) = 2 pi e^{2u})')


def cmd_zeros(x, dps=25):
    mp.mp.dps = dps
    x = mp.mpf(x)
    print('# att543 ZEROS of K_{ix}(a) for a in (2pi, x),  x = %s' % mp.nstr(x, 10))
    if x <= 2 * mp.pi:
        print('   x <= 2pi: no oscillatory window above a = 2pi.')
        return
    a = 2 * mp.pi
    step = mp.mpf('0.02')
    prev = Kix(x, a)
    zs = []
    while a < x:
        a += step
        cur = Kix(x, a)
        if prev != 0 and cur != 0 and (cur > 0) != (prev > 0):
            zs.append(a)
        prev = cur
    print('   zeros in (2pi, x): %d   at a = %s'
          % (len(zs), ', '.join(mp.nstr(z, 6) for z in zs)))
    print('   -> predicted sign changes of u -> C(u,x) on u in (0, u0]: %d' % len(zs))
    print('   -> predicted total on |u| <= 1.6 (even function, both sides): %d'
          % (2 * len(zs)))
    print('   u0(x) = %s' % mp.nstr(mp.log(x / (2 * mp.pi)) / 2, 8))
    print('   K_ix(a) for a just above x:  a=%s -> %s ; a=%s -> %s'
          % (mp.nstr(x * mp.mpf('1.05'), 6), mp.nstr(Kix(x, x * mp.mpf('1.05')), 8),
             mp.nstr(x * mp.mpf('2'), 6), mp.nstr(Kix(x, x * 2), 8)))


def cmd_count(x, umax, step, dps=30):
    """Direct sign-change count of u -> C(u,x) via the Xi route, on (0, umax]."""
    mp.mp.dps = dps
    x = mp.mpf(x)
    u0 = mp.log(x / (2 * mp.pi)) / 2
    print('# att543 DIRECT sign-change count of C(u,x), Xi route.  x=%s dps=%d'
          % (mp.nstr(x, 10), dps))
    print('#   u0(x) = %s ;  scanning u in (0, %s] step %s' % (mp.nstr(u0, 8), umax, step))
    u = mp.mpf(step)
    prev = None
    changes = []
    while u <= mp.mpf(umax) + mp.mpf('1e-12'):
        c = C_xi(u, x)
        s = 1 if c > 0 else (-1 if c < 0 else 0)
        if prev is not None and s != 0 and prev != 0 and s != prev:
            changes.append(mp.nstr(u, 6))
        if s != 0:
            prev = s
        print('   u=%-7s  C = %-22s %s' % (mp.nstr(u, 6), mp.nstr(c, 12),
                                           '+' if c > 0 else 'NEG'))
        u += mp.mpf(step)
    print('#   sign changes on (0,%s]: %d  at u = %s'
          % (umax, len(changes), ', '.join(changes) if changes else 'NONE'))
    sys.stdout.flush()


if __name__ == '__main__':
    if sys.argv[1] == 'count':
        cmd_count(sys.argv[2], sys.argv[3], sys.argv[4],
                  int(sys.argv[5]) if len(sys.argv) > 5 else 30)
    elif sys.argv[1] == 'verify':
        cmd_verify(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 30)
    elif sys.argv[1] == 'zeros':
        cmd_zeros(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 25)
