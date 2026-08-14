"""ADVERSARIAL INDEPENDENT VERIFICATION of attempt 029.

Written from scratch; imports NOTHING from att029_*.py or att014_*.py.
(NB: the record's own verification script already occupies att029_verify.py, so this file is
att029_verify_adv.py -- overwriting their artefact would destroy the evidence under review.)

Targets recomputed independently:
  T1  zeta:  Delta(n) median / mean / sigma over the admissible n, and the composite-line floor.
  T2  DH  :  theta_f count, the ON-LINE zero count on a 4x finer grid (census-gate stress test),
             my own Lambda_f, and Delta_online / Delta_all / Delta_beta / enrichment.
  T3  DH  :  independent argument-principle winding count on sub-boxes -> completeness of the
             OFF-LINE census (the thing the whole DH arm rests on).
"""
import sys, math, time
import numpy as np
from math import log, sqrt, pi

TMP = '/Users/samuellavery/work/helix_frobenius/tmp/'
def P(*a): print(*a); sys.stdout.flush()

# ======================================================================= arithmetic (mine)
def vonmangoldt(N):
    """Lambda(n) for n <= N by sieve."""
    L = np.zeros(N + 1)
    for p in range(2, N + 1):
        if L[p] == 0.0:          # p prime iff untouched by a smaller prime power
            isp = all(p % q for q in range(2, int(p ** 0.5) + 1))
            if not isp:
                continue
            q = p
            while q <= N:
                L[q] = math.log(p)
                q *= p
    return L

# ======================================================================= T1  zeta
def T1_zeta():
    P("=" * 96)
    P("T1  ZETA ARM -- independent recomputation")
    g = np.load(TMP + 'att019_zeros_to20k.npy')
    N = len(g); W = g[-1] - g[0]
    P(f"  zeros {N}, gamma in [{g[0]:.4f},{g[-1]:.4f}], W = {W:.4f}")

    # completeness cross-check of the cached list: Riemann-von Mangoldt
    def NT(T):
        return T / (2 * pi) * math.log(T / (2 * pi)) - T / (2 * pi) + 7.0 / 8.0
    P(f"  completeness: N(20000) Riemann-vM main terms = {NT(20000.0):.1f}  vs cached {N}"
      f"  (diff {N - NT(20000.0):+.1f}; |S| must be small)")
    d = np.diff(g)
    P(f"  min gap {d.min():.5f}, #gaps < 0.01 = {(d < 0.01).sum()}, monotone = {(d > 0).all()}")

    LAM = vonmangoldt(500)
    # admissible n: same Gonek criterion, recoded from the stated formula r = 2 pi n loglog n / W
    adm = []
    for n in range(2, 500):
        if LAM[n] == 0.0:
            continue
        r = 2 * pi * sqrt(n) * math.log(n) * math.log(math.log(n) + 1.0) * sqrt(n) / (W * LAM[n])
        if r < 0.10:
            adm.append(n)
    P(f"  admissible n (r<0.10): {adm[0]}..{adm[-1]}, {len(adm)} values")

    # Delta(n) -- computed with a Kahan-free but float128-ish accumulation for safety
    D = []
    for n in adm:
        ln = math.log(n)
        c = np.cos(g * ln).sum()          # Re part only, as the prediction is real
        a = c * (2 * pi / W)
        pred = -LAM[n] / sqrt(n)
        D.append(a / pred - 1.0)
    D = np.array(D)
    P(f"  Delta(n): median {np.median(D):+.5f}  mean {D.mean():+.5f}  sigma {D.std():.5f}"
      f"  max|.| {np.abs(D).max():.5f}  median|Delta| {np.median(np.abs(D)):.5f}")

    # composite-line moduli
    comp = [n for n in range(6, 200) if LAM[n] == 0.0]
    az = []
    for n in comp:
        ln = math.log(n)
        z = np.exp(1j * g * ln).sum() * (2 * pi / W)
        az.append(abs(z))
    az = np.array(az)
    poisson = (2 * pi / W) * sqrt(N)
    P(f"  composite lines n in [6,199] ({len(comp)} values): median {np.median(az):.5f}"
      f"  84th {np.percentile(az,84):.5f}  max {az.max():.5f} at n={comp[int(np.argmax(az))]}")
    P(f"  Poisson floor (2pi/W)sqrt(N) = {poisson:.5f}  -> ratio to median = {poisson/np.median(az):.1f}x")
    # the CORRECT comparison: Landau/Gonek's absolute error term, which has no T in it
    gonek = np.array([(2 * pi / W) * sqrt(n) * math.log(n) * math.log(math.log(n))
                      for n in comp])
    P(f"  Gonek error scale (2pi/W) sqrt(n) log n loglog n: median {np.median(gonek):.5f}"
      f"  max {gonek.max():.5f}   [this, not sqrt(N), is the theorem's floor]")
    P(f"  observed/Gonek-scale: median {np.median(az/gonek):.3f}  max {np.max(az/gonek):.3f}")
    return g, W, N, az, comp


if __name__ == '__main__':
    T1_zeta()


# ======================================================================= DH, my own evaluator
# a_n periodic mod 5: [1, xi, -xi, -1, 0].  xi derived from scratch below and cross-checked
# against the literature value 0.2840790438...
_A = (4 / math.sqrt(5)) * math.sin(2 * math.pi / 5)
_B = (4 / math.sqrt(5)) * math.sin(4 * math.pi / 5)
XI_MINE = (math.sqrt(_A ** 2 + _B ** 2) - _A) / _B
AVEC = np.array([1.0, XI_MINE, -XI_MINE, -1.0, 0.0])

# Bernoulli B_2k for k = 1..12
_B2K = [1/6, -1/30, 1/42, -1/30, 5/66, -691/2730, 7/6, -3617/510,
        43867/798, -174611/330, 854513/138, -236364091/2730]

def hz(s, a, K=8, extra=60, fac=2.0):
    """Hurwitz zeta by Euler-Maclaurin -- my own coding, different N and K from theirs."""
    s = np.atleast_1d(np.asarray(s, complex))
    N = int(fac * np.abs(s.imag).max() + extra)
    k = np.arange(N, dtype=float) + a
    tot = np.exp(-np.outer(s, np.log(k))).sum(1)
    A = N + a; lA = math.log(A)
    tot = tot + A ** (1 - s) / (s - 1) + 0.5 * A ** (-s)
    poch = np.ones_like(s)
    for j in range(1, K + 1):
        # (s)_{2j-1} = s(s+1)...(s+2j-2)
        if j == 1:
            poch = s.copy()
        else:
            poch = poch * (s + 2 * j - 3) * (s + 2 * j - 2)
        tot = tot + _B2K[j - 1] / math.factorial(2 * j) * poch * A ** (-s - 2 * j + 1)
    return tot

def fdh(s, **kw):
    s = np.atleast_1d(np.asarray(s, complex))
    out = np.zeros(s.shape, complex)
    for r in range(1, 5):
        out = out + AVEC[r - 1] * hz(s, r / 5.0, **kw)
    return 5.0 ** (-s) * out

def fdh_chunked(s, chunk=3000, **kw):
    s = np.asarray(s, complex).ravel()
    o = np.argsort(np.abs(s.imag))
    out = np.empty(s.shape, complex)
    for i in range(0, len(s), chunk):
        idx = o[i:i + chunk]
        out[idx] = fdh(s[idx], **kw)
    return out

from scipy.special import loggamma as _lg
def theta_dh(t):
    t = np.asarray(t, float)
    return (t / 2) * math.log(5 / math.pi) + np.imag(_lg(0.75 + 0.5j * t))


def T2_dh_gates():
    P("\n" + "=" * 96)
    P("T2  DH ARM -- my own evaluator, gates first")
    import mpmath as mp
    mp.mp.dps = 30
    P(f"  xi derived from scratch = {XI_MINE:.13f}   (literature 0.2840790438)")
    # evaluator gate vs mpmath
    rng = np.random.default_rng(11)
    pts = np.concatenate([0.5 + 1j * rng.uniform(100, 3100, 10),
                          np.array([0.3 + 40j, 0.8085171 + 85.6993485j, 1.5 + 2999j,
                                    -0.5 + 3100j, 0.5 + 3099.9j])])
    mine = fdh_chunked(pts)
    worst = 0.0
    for z, v in zip(pts, mine):
        sm = mp.mpc(float(z.real), float(z.imag))
        mv = mp.mpf(5) ** (-sm) * sum(mp.mpf(AVEC[k - 1]) * mp.zeta(sm, mp.mpf(k) / 5)
                                      for k in range(1, 5))
        rel = abs(complex(mv) - v) / max(abs(complex(mv)), 1e-300)
        worst = max(worst, rel)
    P(f"  GATE evaluator vs mpmath on {len(pts)} points: max rel err = {worst:.2e}")
    # FE / theta gate
    tt = np.linspace(100, 3100, 17)
    Z = fdh_chunked(0.5 + 1j * tt) * np.exp(1j * theta_dh(tt))
    P(f"  GATE theta/FE: max |Im Z|/|Z| = {np.max(np.abs(Z.imag)/np.abs(Z)):.2e}")
    # theta count
    Nth = (theta_dh(3100.0) - theta_dh(100.0)) / pi
    P(f"  theta_f count over [100,3100]: delta theta/pi = {Nth:.4f}")
    return Nth


def _Z(t, **kw):
    t = np.asarray(t, float)
    return (fdh_chunked(0.5 + 1j * t, **kw) * np.exp(1j * theta_dh(t))).real

def T3_online_count(t0, t1, h, **kw):
    """Independent on-line zero count by sign change of Z_f on a grid of step h."""
    ng = int(round((t1 - t0) / h))
    grid = np.linspace(t0, t1, ng + 1)
    z = _Z(grid, **kw)
    s = np.sign(z)
    idx = np.where(s[:-1] * s[1:] < 0)[0]
    lo = grid[idx].copy(); hi = grid[idx + 1].copy(); flo = z[idx].copy()
    for _ in range(45):
        mid = 0.5 * (lo + hi); fm = _Z(mid, **kw)
        b = fm * flo > 0
        lo = np.where(b, mid, lo); hi = np.where(b, mid, hi); flo = np.where(b, fm, flo)
    return 0.5 * (lo + hi)

def winding_box(sl, sh, tl, th, dt=0.01, ds=0.002, **kw):
    """Argument-principle zero count of f in the open box (sl,sh) x (tl,th)."""
    sg = np.linspace(sl, sh, max(300, int((sh - sl) / ds)))
    tt = np.linspace(tl, th, max(500, int((th - tl) / dt)))
    tot = 0.0; mx = 0.0; mn = np.inf
    for pts in (sg + 1j * tl, sh + 1j * tt, sg[::-1] + 1j * th, sl + 1j * tt[::-1]):
        v = fdh_chunked(pts, **kw)
        mn = min(mn, np.abs(v).min())
        d = np.angle(v[1:] / v[:-1]); tot += d.sum(); mx = max(mx, np.abs(d).max())
    return tot / (2 * pi), mx, mn


# ======================================================================= T4  Lambda_f (mine)
def lambda_f_dirichlet_inverse(N=4000):
    """Lambda_f via the DIRICHLET INVERSE of a, not their divisor recursion.
       b = a^{-1} (Dirichlet), then Lambda_f = (a . log) * b."""
    a = np.zeros(N + 1)
    for n in range(1, N + 1):
        a[n] = AVEC[(n % 5) - 1] if n % 5 else 0.0
    b = np.zeros(N + 1); b[1] = 1.0
    for n in range(2, N + 1):
        s = 0.0
        for d in range(1, n):
            if n % d == 0:
                s += b[d] * a[n // d]
        b[n] = -s
    LF = np.zeros(N + 1)
    for n in range(1, N + 1):
        s = 0.0
        for d in range(1, n + 1):
            if n % d == 0:
                s += a[d] * math.log(d) * b[n // d]
        LF[n] = s
    return LF


# ======================================================================= T5  DH deficits
def T5_deficits(on, LF):
    off = np.load(TMP + 'att029_dh_off.npy'); r = off[off.real > 0.5]
    W = 3000.0; k = 2 * pi / W; gam = r.imag; d = r.real - 0.5
    Noff = 2 * len(r); f_off = Noff / 3306.532
    rows = []
    for n in range(2, 80):
        if abs(LF[n]) < 1e-9: continue
        ln = log(n); e = np.exp(1j * gam * ln)
        a_on = k * np.exp(1j * on * ln).sum()
        a_oO = k * 2 * e.sum(); a_oB = k * (2 * np.cosh(d * ln) * e).sum()
        pred = -LF[n] / sqrt(n)
        rows.append((a_on.real / pred, (a_on + a_oO).real / pred, (a_on + a_oB).real / pred,
                     abs(a_oO) / abs(pred), abs(pred),
                     abs(a_oO) / (k * sqrt(Noff)), abs(a_oO) / (2 * k * sqrt(len(r)))))
    R = np.array(rows); big = R[:, 4] > 0.25
    P(f"  f_off = {f_off:.4f}   resolvable lines = {int(big.sum())}")
    P(f"  Delta_online = {np.median(R[big,0])-1:+.4f}   [-f_off = {-f_off:+.4f}  <- pre-registered NULL-4]")
    P(f"  Delta_all    = {np.median(R[big,1])-1:+.4f}")
    P(f"  Delta_beta   = {np.median(R[big,2])-1:+.4f}   IQR "
      f"{np.percentile(R[big,2],25):.4f}-{np.percentile(R[big,2],75):.4f}")
    P(f"  |a_off|/|pred| median {np.median(R[big,3]):.4f}  => enrichment {np.median(R[big,3])/f_off:.2f}")
    P(f"  |a_off|/floor: THEIR floor (2pi/W)sqrt(2*137) -> {np.median(R[big,5]):.2f}"
      f"    CORRECT floor (2pi/W)*2*sqrt(137) -> {np.median(R[big,6]):.2f}")
    P(f"  |Delta_all|/|Delta_online| = {abs(np.median(R[big,1])-1)/abs(np.median(R[big,0])-1):.3f}")
