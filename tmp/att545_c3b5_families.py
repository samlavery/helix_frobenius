"""att545 -- C3 batch 5, TARGET C.  Three independent decomposition families, tested
BEFORE any formalization (target D).

Setting, from att544 (exact, remainder-free):
    C(u,x) = 8 pi^2 e^{5u} * Re sum_{n,m>=1} (n^2 n^{ix}) conj(m^2 m^{ix}) F(A_nm, x)
    A_nm = 2 pi n m e^{2u},  F(A,x) = (A^2+9)K_{ix}(A) + 6A K'_{ix}(A)
So C(u,x) is the QUADRATIC FORM of the matrix G_nm := F(A_nm,x) against c_n := n^2 n^{ix}.

FAMILY 1 -- mode pairing / Gram square.
   If G were positive semidefinite, C >= 0 for EVERY x at once, since C = c* G c.
   G_nm = f(log n + log m) is a multiplicative Hankel kernel, so (Widder) it is PSD for
   all node sets iff f is EXPONENTIALLY CONVEX.  F decays like e^{-A}, i.e. f decays
   DOUBLY exponentially in log A -- faster than any int e^{lam s} dmu(lam), mu >= 0.
   Prediction: the 2x2 minor F(A)F(4A) - F(2A)^2 is NEGATIVE.  Tested below.

FAMILY 2 -- ODE / integral representation of K_{ix}  (the productive one).
   Liouville normal form: y = K_{ix}(A), y'' + y'/A - (1 - x^2/A^2) y = 0.
   Put y = A^{-1/2} z  ->  z'' = q(A) z,  q(A) = 1 - (x^2 + 1/4)/A^2.
   q > 0 exactly for A > A* := sqrt(x^2 + 1/4).  On (A*,inf) the equation is
   disconjugate, so the recessive solution (the one decaying at infinity, = K_{ix})
   has NO zeros there.  Prediction: zero sign changes of K_{ix} above A*, and the
   largest zero sits just below A*.  Tested below.

FAMILY 3 -- positive-kernel / total-positivity factorization of the ramp.
   In the (a,b) chart, with h(u) = (u-s)^2/2 on u>s:
     U_x(s) = (1/8) Re int int ((a-s)+(b-s))_+^2 phi(a)phi(b) e^{ixa} e^{-ixb} da db
   so if K_s(al,be) := (al+be)_+^2 were a PSD kernel, then U_x(s) >= 0 for EVERY x and
   s at once and the leaf would close.
   Prediction: NOT PSD.  K(0,0)=0 but K(0,1)=1, so the 2x2 minor at nodes {0,1} is
   0*4 - 1^2 = -1 < 0.  Exact, no arithmetic needed.  Tested numerically too.

USAGE: python3 att545_c3b5_families.py <cmd>
   fam1 x u0 u1 du   -- exponential-convexity minor
   fam2 x            -- Sturm turning point: zeros of K_ix above/below A*
   fam3              -- PSD test of (al+be)_+^2
"""
import sys
import mpmath as mp


def Kix(x, A):
    return mp.re(mp.besselk(1j * mp.mpf(x), mp.mpf(A)))


def dKix(x, A):
    return mp.re(mp.diff(lambda t: mp.besselk(1j * mp.mpf(x), t), mp.mpf(A)))


def F(A, x):
    A = mp.mpf(A)
    return (A ** 2 + 9) * Kix(x, A) + 6 * A * dKix(x, A)


def cmd_fam1(x, u0, u1, du, dps=30):
    mp.mp.dps = dps
    x = mp.mpf(x)
    print('# att545 FAMILY 1 -- exponential convexity / Gram square.  x=%s' % mp.nstr(x, 8))
    print('#   PSD would need the 2x2 minor  F(A)F(4A) - F(2A)^2  >= 0  (nodes n=1,2)')
    print('#     u       A=A_11        F(A)                F(2A)               F(4A)'
          '               minor                sign')
    u = mp.mpf(u0)
    while u <= mp.mpf(u1) + mp.mpf('1e-12'):
        A = 2 * mp.pi * mp.e ** (2 * u)
        f1, f2, f4 = F(A, x), F(2 * A, x), F(4 * A, x)
        minor = f1 * f4 - f2 ** 2
        print('  %6s  %-13s %-19s %-19s %-19s %-20s %s'
              % (mp.nstr(u, 5), mp.nstr(A, 8), mp.nstr(f1, 8), mp.nstr(f2, 8),
                 mp.nstr(f4, 8), mp.nstr(minor, 8),
                 'NEG <<<' if minor < 0 else '+'))
        sys.stdout.flush()
        u += mp.mpf(du)


def cmd_fam2(x, dps=25):
    mp.mp.dps = dps
    x = mp.mpf(x)
    Astar = mp.sqrt(x ** 2 + mp.mpf(1) / 4)
    print('# att545 FAMILY 2 -- Sturm turning point.  x=%s' % mp.nstr(x, 8))
    print('#   A* = sqrt(x^2+1/4) = %s   (q(A) = 1 - (x^2+1/4)/A^2 > 0 above A*)'
          % mp.nstr(Astar, 14))
    # zeros above A*
    a, step = Astar, mp.mpf('0.05')
    prev, above = Kix(x, a), []
    while a < 4 * Astar:
        a += step
        cur = Kix(x, a)
        if prev != 0 and cur != 0 and (cur > 0) != (prev > 0):
            above.append(a)
        prev = cur
    print('   zeros of K_ix on (A*, 4A*): %d  %s'
          % (len(above), '<<< SturmFAIL' if above else '(none -- as predicted)'))
    # largest zero below A*
    a, step = Astar, mp.mpf('0.02')
    prev = Kix(x, a)
    last = None
    while a > mp.mpf('0.5'):
        a -= step
        cur = Kix(x, a)
        if prev != 0 and cur != 0 and (cur > 0) != (prev > 0):
            last = a
            break
        prev = cur
    print('   largest zero BELOW A*: %s   (gap A* - zero = %s)'
          % (mp.nstr(last, 10) if last else 'none found',
             mp.nstr(Astar - last, 8) if last else 'n/a'))
    print('   K_ix at A*, 1.2A*, 2A*: %s , %s , %s'
          % (mp.nstr(Kix(x, Astar), 8), mp.nstr(Kix(x, mp.mpf('1.2') * Astar), 8),
             mp.nstr(Kix(x, 2 * Astar), 8)))


def cmd_fam3(dps=25):
    mp.mp.dps = dps
    print('# att545 FAMILY 3 -- is K(al,be) = (al+be)_+^2 positive semidefinite?')
    print('#   EXACT 2x2 minor at nodes {0, 1}:  K(0,0)=0, K(0,1)=1, K(1,1)=4')
    print('#     det = 0*4 - 1^2 = -1  < 0   ==>  NOT PSD.')
    print('#   Same mechanism as batch-3 attack 21: the kernel VANISHES at a node')
    print('#   (K(0,0)=0) while an off-diagonal entry does not, so PSD is impossible.')
    for nodes in ([mp.mpf(-1), mp.mpf(0), mp.mpf(1)],
                  [mp.mpf(k) / 2 for k in range(-2, 5)]):
        n = len(nodes)
        M = mp.matrix(n, n)
        for i in range(n):
            for j in range(n):
                t = nodes[i] + nodes[j]
                M[i, j] = t ** 2 if t > 0 else mp.mpf(0)
        ev = mp.eigsy(M, eigvals_only=True)
        print('   nodes %s' % [mp.nstr(t, 4) for t in nodes])
        print('     eigenvalues: %s' % ', '.join(mp.nstr(e, 6) for e in ev))
        print('     min eigenvalue = %s  %s'
              % (mp.nstr(min(ev), 8), 'NEG <<< not PSD' if min(ev) < 0 else '+'))


if __name__ == '__main__':
    c = sys.argv[1]
    if c == 'fam1':
        cmd_fam1(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5])
    elif c == 'fam2':
        cmd_fam2(sys.argv[2])
    elif c == 'fam3':
        cmd_fam3()
