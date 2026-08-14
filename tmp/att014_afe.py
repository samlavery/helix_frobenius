"""ATTEMPT 014 -- module: fast vectorised zeta, zeta', zeta'' in the critical strip via the
Hardy-Littlewood approximate functional equation, plus the exact Dirichlet expansion of
-zeta''/zeta' (the "Lambda-analogue" for the zeros of zeta').

AFE:  zeta(s) = sum_{n<=N} n^-s + chi(s) sum_{m<=N} m^{s-1} + O(t^{-sigma/2}),  N = floor(sqrt(t/2pi)).
      chi(s) = pi^{s-1/2} Gamma((1-s)/2)/Gamma(s/2),   P := chi'/chi = log pi - psi((1-s)/2)/2 - psi(s/2)/2.
Differentiating termwise:
      zeta'  = -sum L_n n^-s + chi*( P*T0 + T1 )
      zeta'' =  sum L_n^2 n^-s + chi*( (P^2+P')*T0 + 2P*T1 + T2 )
with T0=sum m^{s-1}, T1=sum L_m m^{s-1}, T2=sum L_m^2 m^{s-1}, P' = (psi'((1-s)/2)-psi'(s/2))/4.

DERIVATION OF THE PREDICTION (the DC-first step, done exactly, not estimated).
  -zeta'(s) = sum_{n>=2} (log n) n^-s = (log 2) 2^{-s} * (1 + X(s)),  X = sum_{n>=3} (log n/log 2)(n/2)^{-s}
   zeta''(s) = sum_{n>=2} (log n)^2 n^-s = (log 2)^2 2^{-s} * (1 + Y(s)), Y = sum_{n>=3}(log n/log 2)^2 (n/2)^{-s}
  =>  -zeta''/zeta'(s) = log2 * (1+Y)/(1+X) = sum_lambda a_lambda e^{-s lambda},
      lambda running over log(n_1...n_k / 2^k), n_i >= 3.
  This is the exact analogue of -zeta'/zeta = sum Lambda(n) n^{-s}.  Two consequences:
   (i) DC:  a_0 = log 2  =>  density of zeta' zeros = (1/2pi)[log(t/2pi) - log 2] = (1/2pi)log(t/4pi).
       The Berndt/Levinson-Montgomery density shift IS the constant term of the same series.
   (ii) LINES: by Landau/Gonek transported to the theta-tape exactly as in attempt 010,
       K(tau_lambda) = U^2 * a_lambda^2 * e^{-lambda} / (L^2 * n_zeros),  tau_lambda = lambda/L.
       (for zeta: a = Lambda(n), lambda = log n, e^{-lambda} = 1/n  -> U Lambda^2/(L^2 n).  Same law.)
"""
import numpy as np, math
from fractions import Fraction

TWOPI = 2*math.pi

# ---------- Stirling asymptotics (|z| >> 1; we only use them at |z| ~ t/2 >= 500) ----------
_B = [1/6, -1/30, 1/42, -1/30, 5/66, -691/2730]
def lgamma_a(z):
    z = np.asarray(z, dtype=complex)
    r = (z-0.5)*np.log(z) - z + 0.5*math.log(TWOPI)
    zi = 1.0/z; z2 = zi*zi; p = zi
    for k in range(1, 7):
        r = r + _B[k-1]/(2*k*(2*k-1))*p
        p = p*z2
    return r
def digamma_a(z):
    z = np.asarray(z, dtype=complex)
    r = np.log(z) - 0.5/z; zi = 1.0/z; z2 = zi*zi; p = z2
    for k in range(1, 7):
        r = r - _B[k-1]/(2*k)*p
        p = p*z2
    return r
def trigamma_a(z):
    z = np.asarray(z, dtype=complex)
    zi = 1.0/z
    r = zi + 0.5*zi**2; z2 = zi*zi; p = zi*z2
    for k in range(1, 7):
        r = r + _B[k-1]*p
        p = p*z2
    return r

def chi_pack(s):
    """chi(s), P = chi'/chi, P' ."""
    s = np.asarray(s, dtype=complex)
    lc = (s-0.5)*math.log(math.pi) + lgamma_a((1-s)/2) - lgamma_a(s/2)
    chi = np.exp(lc)
    P = math.log(math.pi) - 0.5*digamma_a((1-s)/2) - 0.5*digamma_a(s/2)
    Pp = 0.25*(trigamma_a((1-s)/2) - trigamma_a(s/2))
    return chi, P, Pp

# ---------- AFE ----------
def zeta_afe(s, chunk=4000):
    """returns zeta, zeta', zeta'' (arrays).  Requires Im s > 30."""
    s = np.atleast_1d(np.asarray(s, dtype=complex))
    out = [np.empty(s.shape, complex) for _ in range(3)]
    for i0 in range(0, s.size, chunk):
        ss = s[i0:i0+chunk]
        t = ss.imag
        N = np.floor(np.sqrt(t/TWOPI)).astype(np.int64)
        Nx = int(N.max())
        n = np.arange(1, Nx+1, dtype=float); ln = np.log(n)
        msk = (n[None, :] <= N[:, None])
        E = np.exp(-np.outer(ss, ln)) * msk           # n^{-s}
        G = np.exp(np.outer(ss-1.0, ln)) * msk        # m^{s-1}
        S0 = E.sum(1); S1 = -(E*ln).sum(1); S2 = (E*ln*ln).sum(1)
        T0 = G.sum(1); T1 = (G*ln).sum(1); T2 = (G*ln*ln).sum(1)
        chi, P, Pp = chi_pack(ss)
        out[0][i0:i0+chunk] = S0 + chi*T0
        out[1][i0:i0+chunk] = S1 + chi*(P*T0 + T1)
        out[2][i0:i0+chunk] = S2 + chi*((P*P+Pp)*T0 + 2*P*T1 + T2)
    return out[0], out[1], out[2]

def theta(t):
    t = np.asarray(t, float)
    return t/2*np.log(t/TWOPI) - t/2 - math.pi/8 + 1/(48*t) + 7/(5760*t**3)

# ---------- exact Dirichlet coefficients of -zeta''/zeta' ----------
def zprime_coeffs(lam_max=2.2):
    """dict {Fraction r : a}  with  -zeta''/zeta'(s) = sum_r a_r r^{-s},  r = n1..nk/2^k, n_i>=3.
    Built from log2*(1+Y)*(1 - X + X^2 - X^3 + ...) truncated at lambda <= lam_max."""
    R = math.exp(lam_max)
    l2 = math.log(2)
    nmax = int(2*R) + 1
    base = {}                                   # X coefficients
    baseY = {}
    for n in range(3, nmax+1):
        r = Fraction(n, 2)
        if float(r) > R + 1e-12: continue
        base[r] = math.log(n)/l2
        baseY[r] = (math.log(n)/l2)**2
    # powers of X
    powers = [{Fraction(1,1): 1.0}]             # X^0
    cur = {Fraction(1,1): 1.0}
    for k in range(1, 8):
        nxt = {}
        for r1, c1 in cur.items():
            for r2, c2 in base.items():
                r = r1*r2
                if float(r) > R + 1e-12: continue
                nxt[r] = nxt.get(r, 0.0) + c1*c2
        if not nxt: break
        powers.append(nxt); cur = nxt
    inv = {}                                    # 1/(1+X) = sum (-1)^k X^k
    for k, pk in enumerate(powers):
        for r, c in pk.items():
            inv[r] = inv.get(r, 0.0) + ((-1)**k)*c
    res = {}
    for r1, c1 in inv.items():
        res[r1] = res.get(r1, 0.0) + c1*l2
    for r1, c1 in inv.items():
        for r2, c2 in baseY.items():
            r = r1*r2
            if float(r) > R + 1e-12: continue
            res[r] = res.get(r, 0.0) + c1*c2*l2
    return res

def zeta_coeffs(lam_max=2.2):
    """{n : Lambda(n)} for log n <= lam_max -- the same object for zeta (a_lambda = Lambda)."""
    R = int(math.exp(lam_max)) + 1
    d = {}
    for p in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        k = 1
        while p**k <= R:
            d[p**k] = math.log(p); k += 1
    return d

if __name__ == "__main__":
    import mpmath as mp, sys, time
    def P_(*a): print(*a); sys.stdout.flush()
    mp.mp.dps = 30
    P_("GATE 1 -- AFE vs mpmath for zeta, zeta', zeta''")
    P_(f"  {'sigma':>6}{'t':>10}{'|zeta|':>11}{'err z':>11}{'|zp|':>11}{'err zp':>11}{'|zpp|':>11}{'err zpp':>11}")
    worst = {}
    for t in (1e4, 1e5, 1e6, 1e7):
        for sig in (0.30, 0.50, 0.55, 0.70, 1.20, 2.00, 3.50):
            s = complex(sig, t)
            z, z1, z2 = [x[0] for x in zeta_afe(np.array([s]))]
            mz  = complex(mp.zeta(mp.mpc(sig, t)))
            mz1 = complex(mp.zeta(mp.mpc(sig, t), derivative=1))
            mz2 = complex(mp.zeta(mp.mpc(sig, t), derivative=2))
            e0, e1, e2 = abs(z-mz), abs(z1-mz1), abs(z2-mz2)
            worst[sig] = max(worst.get(sig, 0.0), e1)
            P_(f"  {sig:>6.2f}{t:>10.0e}{abs(mz):>11.3f}{e0:>11.2e}{abs(mz1):>11.3f}{e1:>11.2e}{abs(mz2):>11.3f}{e2:>11.2e}")
    P_("  worst absolute zeta' error by sigma: " + "  ".join(f"{k}:{v:.1e}" for k,v in sorted(worst.items())))
    P_("")
    P_("GATE 2 -- exact Dirichlet coefficients a_lambda of -zeta''/zeta' (numeric check)")
    C = zprime_coeffs(2.2)
    for sig in (4.0, 6.0):
        for t in (0.0, 3.0):
            s = mp.mpc(sig, t)
            lhs = -mp.zeta(s, derivative=2)/mp.zeta(s, derivative=1)
            rhs = sum(a*mp.mpf(float(r))**(-s) for r, a in C.items())
            P_(f"   s={sig}+{t}i   -zeta''/zeta' = {complex(lhs):.10f}   series = {complex(rhs):.10f}   "
               f"diff {abs(complex(lhs-rhs)):.2e}")
    P_("")
    P_(f"GATE 3 -- DC term a_0 must be exactly log 2 = {math.log(2):.12f}: "
       f"a(r=1) = {C[Fraction(1,1)]:.12f}   [this IS the log(T/4pi) density shift]")
    P_("")
    P_("PREDICTED TAPE LINES  (amplitude^2 = a_lambda^2 e^{-lambda}); zeta shown for comparison")
    Z = zeta_coeffs(2.2)
    rows = []
    for r, a in C.items():
        lam = math.log(float(r))
        if lam <= 1e-12 or lam > 2.2: continue
        rows.append((lam, str(r), a, a*a*math.exp(-lam)))
    rows.sort()
    P_(f"  {'lambda':>9}{'r':>8}{'a_lambda':>12}{'a^2 e^-lam':>12}   | zeta: {'n':>4}{'Lam^2/n':>10}")
    zrows = sorted((math.log(n), n, L*L/n) for n, L in Z.items())
    for lam, rs, a, amp in rows[:26]:
        m = [zr for zr in zrows if abs(zr[0]-lam) < 1e-12]
        zz = f"{m[0][1]:>4}{m[0][2]:>10.4f}" if m else f"{'-':>4}{'-':>10}"
        P_(f"  {lam:>9.5f}{rs:>8}{a:>12.5f}{amp:>12.5f}   |       {zz}")
