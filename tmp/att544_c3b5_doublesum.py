"""att544 -- C3 batch 5, TARGET A.  The EXACT full theta double sum for C(u,x).

NORMALISATION, pinned to the validated Xi transform (batch 3 N0, batch 4 att541):
    Xi(x) = xi(1/2+ix) = int_R phi(u) e^{ixu} du ,   phi(u) = Phi(|u|)
    Phi(t) = sum_{n>=1} Phi_n(t),
    Phi_n(t) = (4 pi^2 n^4 e^{9t/2} - 6 pi n^2 e^{5t/2}) e^{-pi n^2 e^{2t}}
             = 2 pi n^2 e^{5t/2} (2 pi n^2 e^{2t} - 3) e^{-pi n^2 e^{2t}}
    C(u,x) = 2 int_R phi(u+v) phi(u-v) cos(2xv) dv       (Wigner / cell density)
    int_R e^{-i lam u} C(u,x) du = Xi(x+lam/2) Xi(x-lam/2)   [constants re-derived, batch 5]

DERIVATION (exact, all n,m diagonal AND cross terms).  Put a = u+v, b = u-v.  Then
    Phi_n(u+v) Phi_m(u-v)
       = 4 pi^2 n^2 m^2 e^{5u} [A^2 - 6 A cosh(w) + 9] e^{-A cosh w},
    A := 2 pi n m e^{2u},   w := 2v + log(n/m),
because  pi(n^2 e^{2(u+v)} + m^2 e^{2(u-v)}) = 2 pi n m e^{2u} cosh(2v + log(n/m)) = A cosh w.
Then cos(2xv) = cos(x w) cos(x log(n/m)) + sin(x w) sin(x log(n/m)); the sin part is odd in
w and drops on the FULL line.  With K_{ix}(A) = int_0^inf e^{-A cosh w} cos(xw) dw:

  ***  J_nm(u,x) = 8 pi^2 n^2 m^2 e^{5u} cos(x log(n/m)) [ (A^2+9) K_{ix}(A) + 6 A K'_{ix}(A) ]

The arithmetic phase cos(x log(n/m)) is the PRIME CLOCK; the radial factor is a Macdonald
function of imaginary order at A = 2 pi n m e^{2u}.  Diagonal n=m gives phase 1.

WHETHER  C = sum_{n,m} J_nm  EXACTLY depends on whether the ANALYTIC series Phi(t) is EVEN.
If Phi(-t) = Phi(t) then phi = Phi on all of R and there is NO even-extension remainder.
That is claimed classical (Titchmarsh 2.16) but it is TESTED here, not assumed, because the
individual terms Phi_n are NOT even and the n-sum at t -> -inf is delicate.

USAGE: python3 att544_c3b5_doublesum.py <cmd>
   even  [dps]        -- is the analytic Phi series even?  (decides the remainder)
   check x u [N dps]  -- double sum vs the independent Xi route, with a term census
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


def Phi_n(n, t):
    """The n-th theta term, ANALYTIC (no |t|)."""
    n, t = mp.mpf(n), mp.mpf(t)
    e2 = mp.e ** (2 * t)
    return 2 * mp.pi * n ** 2 * mp.e ** (5 * t / 2) * (2 * mp.pi * n ** 2 * e2 - 3) \
        * mp.e ** (-mp.pi * n ** 2 * e2)


def Phi_series(t, N=None):
    """Phi(t) = sum_n Phi_n(t), analytic continuation of the series."""
    t = mp.mpf(t)
    if N is None:
        # need pi n^2 e^{2t} >> 1 ; for t very negative that is a LOT of terms
        e2 = mp.e ** (2 * t)
        N = int(mp.ceil(mp.sqrt(max(mp.mpf(60), 60 / (mp.pi * e2))))) + 5
    return mp.fsum(Phi_n(n, t) for n in range(1, N + 1)), N


def Kix(x, A):
    return mp.re(mp.besselk(1j * mp.mpf(x), mp.mpf(A)))


def dKix(x, A):
    return mp.re(mp.diff(lambda t: mp.besselk(1j * mp.mpf(x), t), mp.mpf(A)))


def F(A, x):
    """(A^2+9) K_{ix}(A) + 6 A K'_{ix}(A)."""
    A = mp.mpf(A)
    return (A ** 2 + 9) * Kix(x, A) + 6 * A * dKix(x, A)


def J_nm(n, m, u, x):
    n, m, u = mp.mpf(n), mp.mpf(m), mp.mpf(u)
    A = 2 * mp.pi * n * m * mp.e ** (2 * u)
    return 8 * mp.pi ** 2 * n ** 2 * m ** 2 * mp.e ** (5 * u) \
        * mp.cos(x * mp.log(n / m)) * F(A, x)


def C_xi(u, x, T=None, deg=5, panel=mp.mpf('0.5')):
    """Reference: C(u,x) = (2/pi) int_0^inf Xi(x+t) Xi(x-t) cos(2tu) dt."""
    u, x = mp.mpf(u), mp.mpf(x)
    if T is None:
        T = 2 * x + 40
    T = mp.mpf(T)
    nodes = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(
        mp.mpf(-1), mp.mpf(1), deg, mp.mp.prec)
    tot, e = mp.mpf(0), mp.mpf(0)
    while e < T:
        b = min(e + panel, T)
        half, mid = (b - e) / 2, (b + e) / 2
        tot += half * mp.fsum(w * Xi(x + mid + half * tt) * Xi(x - mid - half * tt)
                              * mp.cos(2 * (mid + half * tt) * u) for tt, w in nodes)
        e = b
    return 2 * tot / mp.pi


def cmd_even(dps=40):
    mp.mp.dps = dps
    print('# att544 TEST 0 -- is the ANALYTIC Phi series even?   dps=%d' % dps)
    print('#   if yes, phi = Phi on all of R and the double sum has NO remainder')
    print('#    t        Phi(t)                    Phi(-t)                   rel.diff      N(-t)')
    for ts in ['0.25', '0.5', '1.0', '1.5', '2.0']:
        t = mp.mpf(ts)
        p, _ = Phi_series(t)
        q, Nq = Phi_series(-t)
        rel = abs(p - q) / max(abs(p), abs(q))
        print('  %6s  %-25s %-25s %-13s %d'
              % (ts, mp.nstr(p, 16), mp.nstr(q, 16), mp.nstr(rel, 4), Nq))
        sys.stdout.flush()


def cmd_check(x, u, N=6, dps=30):
    mp.mp.dps = dps
    x, u = mp.mpf(x), mp.mpf(u)
    print('# att544 TEST 1 -- double sum vs Xi route.  x=%s u=%s N=%d dps=%d'
          % (mp.nstr(x, 8), mp.nstr(u, 6), N, dps))
    A11 = 2 * mp.pi * mp.e ** (2 * u)
    print('#   A_11 = 2 pi e^{2u} = %s ;  x = %s ;  A_11 %s x'
          % (mp.nstr(A11, 10), mp.nstr(x, 8), '>' if A11 > x else '<='))
    ref = C_xi(u, x)
    print('#   C (Xi route, reference) = %s' % mp.nstr(ref, 16))
    tot = mp.mpf(0)
    rows = []
    for n in range(1, N + 1):
        for m in range(1, N + 1):
            j = J_nm(n, m, u, x)
            tot += j
            rows.append((n, m, j))
    print('#   sum_{n,m<=%d} J_nm       = %s' % (N, mp.nstr(tot, 16)))
    den = max(abs(ref), abs(tot))
    print('#   rel.diff                = %s'
          % (mp.nstr(abs(ref - tot) / den, 6) if den > 0 else 'n/a'))
    rows.sort(key=lambda r: -abs(r[2]))
    print('#   term census (largest 12 by |J_nm|):')
    print('#     n  m   A_nm            cos(x log(n/m))      J_nm                  |J|/|J_11|')
    j11 = abs(J_nm(1, 1, u, x))
    for (n, m, j) in rows[:12]:
        A = 2 * mp.pi * n * m * mp.e ** (2 * u)
        print('     %2d %2d  %-15s %-20s %-21s %s'
              % (n, m, mp.nstr(A, 8), mp.nstr(mp.cos(x * mp.log(mp.mpf(n) / m)), 10),
                 mp.nstr(j, 12), mp.nstr(abs(j) / j11, 6) if j11 > 0 else 'n/a'))
    offdiag = mp.fsum(abs(j) for (n, m, j) in rows if not (n == 1 and m == 1))
    print('#   sum_{(n,m)!=(1,1)} |J_nm| / |J_11| = %s'
          % (mp.nstr(offdiag / j11, 8) if j11 > 0 else 'n/a'))
    sys.stdout.flush()


def cmd_dom(x, u0, u1, du, N=8, dps=30):
    """TARGET B: where does the (1,1) diagonal dominate ALL other n,m terms?

    If  sum_{(n,m)!=(1,1)} |J_nm|  <  J_11  and  F(A_11,x) > 0,  then C(u,x) > 0.
    This is the honest eventual-positivity criterion: it uses every cross term, and
    the arithmetic phases are bounded by |cos| <= 1 (worst case), never evaluated away.
    """
    mp.mp.dps = dps
    x = mp.mpf(x)
    print('# att544 TARGET B -- diagonal domination over the FULL double sum.  x=%s N=%d dps=%d'
          % (mp.nstr(x, 8), N, dps))
    print('#   criterion:  F(A_11,x) > 0  AND  sum_{(n,m)!=(1,1)}|J_nm| < J_11  ==>  C(u,x) > 0')
    print('#   sharp Sturm turning point A* = sqrt(x^2+1/4) = %s  ->  u* = %s'
          % (mp.nstr(mp.sqrt(x ** 2 + mp.mpf(1) / 4), 10),
             mp.nstr(mp.log(mp.sqrt(x ** 2 + mp.mpf(1) / 4) / (2 * mp.pi)) / 2, 10)))
    print('#     u       A_11          F(A_11,x)             J_11                  '
          'off/J_11        C>0 proved?')
    u = mp.mpf(u0)
    while u <= mp.mpf(u1) + mp.mpf('1e-12'):
        A11 = 2 * mp.pi * mp.e ** (2 * u)
        f11 = F(A11, x)
        j11 = J_nm(1, 1, u, x)
        off = mp.mpf(0)
        for n in range(1, N + 1):
            for m in range(1, N + 1):
                if n == 1 and m == 1:
                    continue
                off += abs(J_nm(n, m, u, x))
        ratio = off / abs(j11) if j11 != 0 else mp.inf
        ok = 'YES' if (f11 > 0 and j11 > 0 and ratio < 1) else ''
        print('  %6s  %-13s %-21s %-21s %-15s %s'
              % (mp.nstr(u, 5), mp.nstr(A11, 8), mp.nstr(f11, 10), mp.nstr(j11, 10),
                 mp.nstr(ratio, 8), ok))
        sys.stdout.flush()
        u += mp.mpf(du)


if __name__ == '__main__':
    if sys.argv[1] == 'dom':
        cmd_dom(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5],
                int(sys.argv[6]) if len(sys.argv) > 6 else 8,
                int(sys.argv[7]) if len(sys.argv) > 7 else 30)
    elif sys.argv[1] == 'even':
        cmd_even(int(sys.argv[2]) if len(sys.argv) > 2 else 40)
    elif sys.argv[1] == 'check':
        cmd_check(sys.argv[2], sys.argv[3],
                  int(sys.argv[4]) if len(sys.argv) > 4 else 6,
                  int(sys.argv[5]) if len(sys.argv) > 5 else 30)
