"""ATTEMPT 028 -- ENGINE.  Cancellation-free Lambda for the D=-23 class-group L-functions.

020's NAMED BLOCKER.  The two-sided incomplete-gamma expansion of
    Lambda(s) = (sqrt23/2pi)^s Gamma(s) Z(s) = sum_n coef(n)[x^{-s}Gamma(s,x) + x^{s-1}Gamma(1-s,x)]
represents a quantity of size |Gamma(1/2+it)| ~ e^{-pi t/2} as a sum of O(1) terms.  Loss =
(pi/2) t / ln 10 = 0.682 t digits.  At t=600 that is 409 digits.

THE FIX (this file).  Rotate the Mellin contour to the ray arg y = alpha = pi/2 - delta.
Lambda(s) = int_0^{inf e^{i alpha}} phi(y) y^{s-1} dy   (Re s > 1, then continue), split at
y_0 = e^{i alpha}, and use the theta transformation Theta(1/y) = y Theta(y).  With
phi(y) = sum_n coef(n) e^{-c n y},  c = 2 pi / sqrt(23),  and Theta = K0 + 2 phi (K0 = the
number of classes summed, so the pole coefficient is pc = K0/2), one gets for s = 1/2 + it

    Lambda(1/2+it) = 2 Re[ e^{i alpha s} ( I(t) - pc/s ) ],
    I(t) = int_0^inf phi(e^{i alpha} e^v) e^{v s} dv.

|e^{i alpha s}| = e^{-alpha t}, and |Lambda| ~ e^{-pi t/2}, so the cancellation is only
e^{-delta t}: delta*t/ln10 digits, INDEPENDENT of the representation length, and delta is ours
to choose.  delta = 0.025 at t = 600 costs 6.5 digits, leaving ~9 in double precision.
Convergence of phi on the ray is e^{-c n sin(delta)}, so n_max ~ 42/(c sin delta).

The v-integral is done on a uniform grid (spacing h) with Euler-Maclaurin endpoint corrections
through h^6 at v=0 (the v=V end is dead by double-exponential decay).  The oscillation e^{i t v}
is then a pure geometric progression in j, so a two-level factorization evaluates the whole
70k-point sum in ~70k flops: H(t) costs ~0.1 ms.

THREE SPECIMENS, ONE ENGINE, MATCHED GAMMA FACTOR AND CONDUCTOR (hence matched zero density):
   F     = sum a_1(n) n^{-s}   principal class     NOT an Euler product   pc = 1/2
   zeta_K= sum d_K(n) n^{-s}   Dedekind of Q(V-23) IS  an Euler product   pc = 3/2
   L_f   = sum b(n)   n^{-s}   weight-1 newform    IS  an Euler product   pc = 0
with a_1 = r_{Q0}/2, a_C = r_{Q1}/2, d_K = a_1 + 2 a_C, b = a_1 - a_C, and
F = (1/3)(zeta_K + 2 L_f).
"""
import numpy as np, math, os, sys
from math import pi, log, sqrt

D = 23
C = 2*pi/sqrt(D)                      # the self-dual scale
LOGQ = log(sqrt(D)/(2*pi))            # theta_Q(t) = t*LOGQ + Im logGamma(1/2+it)


# ------------------------------------------------------------------ coefficients
def rep_counts(a, b, c, N):
    """r_Q(n) = #{(x,y) in Z^2 : a x^2 + b xy + c y^2 = n}, n = 1..N."""
    r = np.zeros(N+1, dtype=np.int64)
    disc = b*b - 4*a*c                      # < 0
    ymax = int(math.isqrt(int(4*a*N//(-disc)))) + 2
    for y in range(-ymax, ymax+1):
        # a x^2 + b y x + (c y^2 - n) = 0  ->  x in [(-by - sqrt(b^2y^2-4a(cy^2-N)))/2a, ...]
        dd = b*b*y*y - 4*a*(c*y*y - N)
        if dd < 0:
            continue
        sd = math.isqrt(dd) + 1
        x0 = (-b*y - sd)//(2*a) - 1
        x1 = (-b*y + sd)//(2*a) + 1
        xs = np.arange(x0, x1+1)
        v = a*xs*xs + b*xs*y + c*y*y
        m = (v >= 1) & (v <= N)
        np.add.at(r, v[m], 1)
    return r


def coefficients(N):
    r0 = rep_counts(1, 1, 6, N)        # principal class
    r1 = rep_counts(2, 1, 3, N)        # one of the two non-principal classes
    assert r0[1] == 2 and r0[2] == 0 and r0[3] == 0 and r0[4] == 2 and r0[6] == 4
    a1 = r0/2.0
    aC = r1/2.0
    dK = a1 + 2*aC
    b = a1 - aC
    return a1, aC, dK, b


def chi23(n):
    """chi_{-23}(n) = Legendre(n|23); -23 = 1 mod 4 so the Kronecker symbol reduces to it."""
    n %= 23
    if n == 0:
        return 0
    return 1 if pow(n, 11, 23) == 1 else -1


def vonmangoldt_like(coef, NL):
    """Lam(n) from  coef(n) log n = sum_{d|n} Lam(d) coef(n/d),  coef(1) = 1."""
    assert abs(coef[1] - 1.0) < 1e-12
    L = np.zeros(NL+1)
    for n in range(2, NL+1):
        s = coef[n]*math.log(n)
        for d in range(2, n):
            if n % d == 0:
                s -= L[d]*coef[n//d]
        L[n] = s
    return L


# ------------------------------------------------------------------ the engine
class Engine:
    """Lambda(1/2+it) for a self-dual theta specimen, via the rotated Mellin ray."""

    def __init__(self, coef, polecoef, delta=0.025, h=1e-4, guard=42.0, name=""):
        self.name = name
        self.delta = delta
        self.alpha = pi/2 - delta
        self.h = h
        self.pc = polecoef
        sd = math.sin(delta)
        self.nmax = int(math.ceil(guard/(C*sd)))
        self.V = math.log(guard/(C*sd))          # c e^V sin delta = guard
        M = int(math.ceil(self.V/h)) + 1
        # pad to a nice factorization for the two-level phase sum
        K2 = int(math.isqrt(M)) + 1
        K1 = (M + K2 - 1)//K2
        self.K1, self.K2 = K1, K2
        self.M = K1*K2
        v = np.arange(self.M)*h
        self.v = v
        y0 = np.exp(1j*self.alpha)
        self.y0 = y0
        yv = y0*np.exp(v)                        # y(v) on the ray

        # NB: b_f(n) takes NEGATIVE values -- must select on != 0, not > 0.
        nz = np.nonzero(coef[:self.nmax+1] != 0)[0]
        nz = nz[nz >= 1]
        self.nz = nz
        # phi(y(v)) = sum_n coef(n) exp(-c n y(v))
        phi = np.zeros(self.M, dtype=complex)
        E = -C*yv
        for n in nz:
            phi += coef[n]*np.exp(n*E)
        g = phi*np.exp(v/2)
        g[int(math.ceil(self.V/h)):] = 0.0       # beyond V: dead
        g[0] *= 0.5                              # trapezoid endpoint
        self.G = g.reshape(K1, K2)

        # Euler-Maclaurin endpoint data at v=0:  f^(k)(0) = [(s+D)^k phi](y0), D = y d/dy.
        # D^k e^{u} = B_k(u) e^u with u = -c n y ; B_k = Stirling-2 polynomials.
        u = -C*y0*nz.astype(float)
        w = coef[nz]*np.exp(u)
        B = [np.ones_like(u),
             u,
             u + u**2,
             u + 3*u**2 + u**3,
             u + 7*u**2 + 6*u**3 + u**4,
             u + 15*u**2 + 25*u**3 + 10*u**4 + u**5]
        self.Dphi = np.array([np.sum(w*Bk) for Bk in B])   # D^k phi (y0), k=0..5

    def _Pk(self, s, k):
        """[(s+D)^k phi](y0) = sum_j C(k,j) s^{k-j} D^j phi."""
        tot = 0j
        for j in range(k+1):
            tot += math.comb(k, j)*s**(k-j)*self.Dphi[j]
        return tot

    def lam_scaled(self, t):
        """2 Re[e^{i alpha s}(I - pc/s)] * e^{pi t/2}  -- sign- and scale-faithful, O(1)."""
        h, K1, K2 = self.h, self.K1, self.K2
        s = 0.5 + 1j*t
        A = np.exp(1j*t*h*K2*np.arange(K1))
        Bv = np.exp(1j*t*h*np.arange(K2))
        S = A @ (self.G @ Bv)
        I = h*S
        I += (h**2/12)*self._Pk(s, 1)
        I -= (h**4/720)*self._Pk(s, 3)
        I += (h**6/30240)*self._Pk(s, 5)
        z = (I - self.pc/s)*np.exp(1j*self.alpha/2)
        return 2*math.exp(self.delta*t)*z.real

    def hardy(self, t):
        """Lambda(1/2+it) / [(sqrt23/2pi)^{1/2} |Gamma(1/2+it)|]  = the Hardy function."""
        pref = (sqrt(D)/(2*pi))**0.5 * math.sqrt(2*pi/(1 + math.exp(-2*pi*t)))
        return self.lam_scaled(t)/pref

    def hardy_vec(self, ts):
        return np.array([self.hardy(float(t)) for t in ts])


def theta_Q(t):
    from scipy.special import loggamma
    t = np.asarray(t, float)
    return t*LOGQ + np.imag(loggamma(0.5 + 1j*t))


# ------------------------------------------------------------------ zero census
def find_zeros(fn, T0, T1, step, verbose=True):
    from scipy.optimize import brentq
    ts = np.arange(T0, T1 + step, step)
    vals = np.array([fn(t) for t in ts])
    idx = np.nonzero(np.signbit(vals[:-1]) != np.signbit(vals[1:]))[0]
    if verbose:
        print(f"    grid {len(ts)} pts, {len(idx)} sign changes", flush=True)
    Z = np.array([brentq(fn, ts[i], ts[i+1], xtol=1e-9, rtol=1e-13) for i in idx])
    return Z, ts, vals
