"""ADVERSARIAL VERIFICATION of attempt 030.  Written from scratch; shares no code with
tmp/att030_*.py.  Different integrand (xi-total and A-arch computed separately, arith by
subtraction), different radius, different N, own FFT, own Laguerre, own detrend.

Targets, in order of how much the verdict rests on them:
  V1  lambda_n^arith for zeta, independent contour.  Anchors: lambda_1^arith = gamma_E,
      lambda_1 = lambda_1^arch + lambda_1^arith = 1 + gamma/2 - log(4 pi)/2 (closed form).
  V2  the dyadic R^2 table at M=32 (015's -1124.7 / -65.75 / -30.89 / -3.776 / +0.9501)
      and 030's extension (0.8340 on [320,640] ...).
  V3  n* vs window ratio -- INCLUDING the edge-vs-centre relabelling the campaign has
      already been burned by once.  n* is reported at the window START by 030.
  V4  the lowest-zero cosine identification R^2 on [20,40].
  V5  gamma_1 for chi_-3 / chi_5 / chi_8 by an independent Hardy-Z sign scan.
  V6  lambda_n^arith for chi_-3 by my own contour, and n_half, to test the exponent p.
"""
import sys, os, math, time
import numpy as np
from mpmath import mp, mpf, mpc

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = []
def P(*a):
    s = " ".join(str(x) for x in a)
    print(s); sys.stdout.flush(); OUT.append(s)

# --------------------------------------------------------------------------- my own FFT
def _fft(a):
    """iterative radix-2 DIT, mpmath complex, in-place style.  N a power of two."""
    n = len(a)
    x = list(a)
    # bit reversal
    nb = n.bit_length() - 1
    for i in range(n):
        j = int('{:0{w}b}'.format(i, w=nb)[::-1], 2)
        if j > i:
            x[i], x[j] = x[j], x[i]
    m = 2
    while m <= n:
        th = -2 * mp.pi / m
        wm = mpc(mp.cos(th), mp.sin(th))
        h = m // 2
        pw = [mpc(1)]
        for _ in range(h - 1):
            pw.append(pw[-1] * wm)
        for st in range(0, n, m):
            for k in range(h):
                t = pw[k] * x[st + k + h]
                u = x[st + k]
                x[st + k] = u + t
                x[st + k + h] = u - t
        m *= 2
    return x

def coeffs_on_circle(f, r, N, nkeep, dps, sym=True, tag=""):
    """Taylor coefficients c_k = (1/N r^k) sum_j f(r w^j) w^{-jk}, w = e^{2 pi i/N}."""
    mp.dps = dps
    r = mpf(r)
    vals = [None] * N
    t0 = time.time()
    top = N // 2 if sym else N - 1
    for j in range(top + 1):
        ang = 2 * mp.pi * j / N
        vals[j] = f(r * mpc(mp.cos(ang), mp.sin(ang)))
        if j and j % 500 == 0:
            P(f"      {tag} {j}/{top}  [{time.time()-t0:.0f}s]")
    if sym:
        for j in range(N // 2 + 1, N):
            vals[j] = mp.conj(vals[N - j])
    A = _fft(vals)
    return [A[k] / (N * r ** k) for k in range(nkeep)]

# --------------------------------------------------------------------------- integrands
def s_of(z):
    return 1 / (1 - z)

def g_total_zeta(z):
    """(xi'/xi)(s) s^2, xi = (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s)."""
    s = s_of(z)
    v = 1 / s + 1 / (s - 1) - mp.log(mp.pi) / 2 + mp.digamma(s / 2) / 2 \
        + mp.zeta(s, 1, 1) / mp.zeta(s)
    return v * s * s

def g_arch_zeta(z):
    """(A'/A)(s) s^2, A = (1/2) s pi^{-s/2} Gamma(s/2)."""
    s = s_of(z)
    return (1 / s - mp.log(mp.pi) / 2 + mp.digamma(s / 2) / 2) * s * s

# --------------------------------------------------------------------------- Laguerre
def lag1_matrixfree(x, amp, nmax):
    """S_n = sum_i amp_i L_{n-1}^{(1)}(x_i) for n=1..nmax.  L_k^{(1)} by (k+1)L_{k+1}^{(1)}
    = (2k+2-x) L_k^{(1)} - (k+1) L_{k-1}^{(1)}."""
    x = np.asarray(x, float); amp = np.asarray(amp, float)
    S = np.empty(nmax)
    a = np.ones_like(x)      # L_0^{(1)} = 1
    b = np.zeros_like(x)     # L_{-1}^{(1)} = 0
    for k in range(nmax):
        S[k] = float(np.dot(a, amp))
        c = ((2 * k + 2 - x) * a - (k + 1) * b) / (k + 1)
        b, a = a, c
    return S

def lag0_seq(x, nmax):
    """L_n^{(0)}(x), n = 0..nmax."""
    o = np.empty(nmax + 1); o[0] = 1.0
    a, b = 1.0, 0.0
    for k in range(nmax):
        c = ((2 * k + 1 - x) * a - k * b) / (k + 1)
        b, a = a, c
        o[k + 1] = c
    return o

def vonmangoldt(M):
    M = int(M)
    isp = np.ones(M + 1, bool); isp[:2] = False
    for p in range(2, int(M ** .5) + 1):
        if isp[p]:
            isp[p * p::p] = False
    ms, lg = [], []
    for p in np.flatnonzero(isp):
        p = int(p); q = p
        while q <= M:
            ms.append(q); lg.append(math.log(p)); q *= p
    o = np.argsort(ms)
    return np.array(ms, float)[o], np.array(lg, float)[o]

def BL_trunc(nmax, M, chi=None, q=1):
    """O_n(M) = 1 - L_n(log M) - sum_{m<=M} Lambda(m) chi(m)/m L_{n-1}^{(1)}(log m)."""
    ms, lg = vonmangoldt(M)
    w = lg / ms
    if chi is not None:
        cv = np.array([chi(int(m) % q) for m in ms], float)
        w = w * cv
        head = 0.0            # no pole => no PNT main term for the tail
    else:
        head = 1.0
    S = lag1_matrixfree(np.log(ms), w, nmax)
    if chi is None:
        return head - lag0_seq(math.log(M), nmax)[1:nmax + 1] - S
    return -S

# --------------------------------------------------------------------------- statistic
def detr(n, y, basis='orig'):
    n = np.asarray(n, float)
    if basis == 'orig':
        X = np.stack([np.ones_like(n), np.log(n), np.sqrt(n), n], 1)
    elif basis == 'lin':
        X = np.stack([np.ones_like(n), n], 1)
    elif basis == 'p3':
        v = np.sqrt(n); X = np.stack([v ** k for k in range(4)], 1)
    elif basis == 'p6':
        v = np.sqrt(n); X = np.stack([v ** k for k in range(7)], 1)
    Q, _ = np.linalg.qr(X)
    return y - Q @ (Q.T @ y)

def R2(n, y, o, basis='orig'):
    yd, od = detr(n, y, basis), detr(n, o, basis)
    return 1 - np.sum((yd - od) ** 2) / np.sum(yd ** 2)

# =========================================================================== main
if __name__ == "__main__":
    t0 = time.time()
    stage = sys.argv[1] if len(sys.argv) > 1 else 'all'
    NMAX = 2000
    CA = os.path.join(HERE, 'ver030_tot.npy')
    CB = os.path.join(HERE, 'ver030_arch.npy')

    # ---------------- V1
    if stage in ('all', 'v1'):
        P("=" * 100)
        P("V1  independent contour: r = 0.985, N = 4096, dps = 45, nmax = 2000")
        P("    radius validity: 1/(1-r^2) = %.3f ; every nontrivial zero has beta^2+gamma^2"
          " >= 14.1347^2 = 199.79, so NO zero image is inside |z| < r.  Unconditional."
          % (1 / (1 - 0.985 ** 2)))
        if not (os.path.exists(CA) and os.path.exists(CB)):
            ct = coeffs_on_circle(g_total_zeta, '0.985', 4096, NMAX, 45, tag='tot')
            np.save(CA, np.array([float(c.real) for c in ct]))
            P("    max |Im| of total coeffs: %.3e"
              % max(float(abs(c.imag)) for c in ct[:NMAX]))
            ca = coeffs_on_circle(g_arch_zeta, '0.985', 4096, NMAX, 45, tag='arch')
            np.save(CB, np.array([float(c.real) for c in ca]))
        TOT = np.load(CA); ARCH = np.load(CB)
        ARI = TOT - ARCH
        gam = float(mp.euler)
        P("    lambda_1^arith (mine)  = %.12f   gamma_E = %.12f   diff %.2e"
          % (ARI[0], gam, abs(ARI[0] - gam)))
        lam1_closed = 1 + gam / 2 - math.log(4 * math.pi) / 2
        P("    lambda_1 (mine)        = %.16f   closed form 1+g/2-log(4pi)/2 = %.16f"
          % (TOT[0], lam1_closed))
        P("    lambda_1^arch (mine)   = %.12f   closed 1-log(pi)/2+psi(1/2)/2 = %.12f"
          % (ARCH[0], 1 - math.log(math.pi) / 2 + float(mp.digamma(mpf(1) / 2)) / 2))
        # cross-check against THEIR cached arrays
        TY = np.load(os.path.join(HERE, 'att030_Yzeta_r997.npy'))[:NMAX]
        TA = np.load(os.path.join(HERE, 'att030_arch.npy'))[:NMAX]
        P("    vs THEIR arith array : max abs %.3e   max rel %.3e"
          % (np.abs(ARI - TY).max(), (np.abs(ARI - TY) / np.maximum(np.abs(TY), 1)).max()))
        P("    vs THEIR arch  array : max rel %.3e"
          % (np.abs(ARCH - TA) / np.abs(TA)).max())
        P("    min lambda_n over n<=2000 = %.8f at n=%d  (Li positivity)"
          % (TOT.min(), int(TOT.argmin()) + 1))
        w = np.arange(200, 3001)
        w = w[w <= NMAX]
        P("    max |arith|/arch on [200,%d] = %.4e" % (w[-1], (np.abs(ARI[199:]) / ARCH[199:]).max()))
        np.save(os.path.join(HERE, 'ver030_arith.npy'), ARI)

    # ---------------- V2/V3/V4
    if stage in ('all', 'v2'):
        ARI = np.load(os.path.join(HERE, 'ver030_arith.npy'))
        P("=" * 100)
        P("V2  the dyadic R^2 table, M = 32, basis {1, log n, sqrt n, n}, MY lambda array")
        # sanity of my Laguerre against mpmath
        mp.dps = 25
        chk = max(abs(float(mp.laguerre(k, 1, mpf('0.6931471805599453')))
                      - lag1_matrixfree([math.log(2.0)], [1.0], k + 1)[k]) for k in (0, 5, 40, 300))
        P("    Laguerre L_k^(1)(log 2) vs mpmath, k in {0,5,40,300}: max diff %.3e" % chk)
        O32 = BL_trunc(len(ARI), 32)
        wins = [(10, 20), (20, 40), (40, 80), (80, 160), (160, 320), (320, 640),
                (640, 1280), (1000, 2000)]
        P("    %-14s %12s   %s" % ("window", "R^2 (mine)", "030 reported"))
        rep = {(10, 20): -1124.7345, (20, 40): -65.7463, (40, 80): -30.8928,
               (80, 160): -3.7757, (160, 320): 0.9501, (320, 640): 0.8340,
               (640, 1280): 0.8158}
        for lo, hi in wins:
            n = np.arange(lo, hi + 1, dtype=float)
            v = R2(n, ARI[lo - 1:hi], O32[lo - 1:hi])
            P("    [%5d,%5d] %12.4f   %s" % (lo, hi, v, rep.get((lo, hi), '-')))
        P("")
        P("    M-sensitivity (030's N3): R^2 at M = 2, 32, 1000, 10^5")
        Os = {M: BL_trunc(len(ARI), M) for M in (2, 32, 1000, 100000)}
        P("    %-14s" % "window" + "".join("%12s" % ("M=%d" % M) for M in (2, 32, 1000, 100000)))
        for lo, hi in wins:
            n = np.arange(lo, hi + 1, dtype=float)
            P("    [%5d,%5d]" % (lo, hi) +
              "".join("%12.4f" % R2(n, ARI[lo - 1:hi], Os[M][lo - 1:hi])
                      for M in (2, 32, 1000, 100000)))

        P("")
        P("V3  crossing point n* (R^2 first reaches 0.5 and stays) vs window ratio")
        P("    reported at the window START (030's convention), at the GEOMETRIC centre,")
        P("    and at the ARITHMETIC centre -- edge-vs-centre is a known campaign failure.")
        grid = np.unique(np.round(np.exp(np.linspace(math.log(12), math.log(900), 200))).astype(int))
        res = {}
        for basis in ('orig', 'lin', 'p3', 'p6'):
            row = "    basis %-5s:" % basis
            for ratio in (1.5, 2.0, 3.0, 4.0):
                cross = None
                for n0 in grid:
                    n1 = int(n0 * ratio)
                    if n1 > len(ARI) or n1 - n0 < 8:
                        continue
                    n = np.arange(n0, n1 + 1, dtype=float)
                    if R2(n, ARI[n0 - 1:n1], O32[n0 - 1:n1], basis) >= 0.5:
                        ok = True
                        for mm in (1.3, 1.8, 2.6):
                            a2 = int(n0 * mm); b2 = int(a2 * ratio)
                            if b2 > len(ARI):
                                continue
                            n2 = np.arange(a2, b2 + 1, dtype=float)
                            if R2(n2, ARI[a2 - 1:b2], O32[a2 - 1:b2], basis) < 0.5:
                                ok = False; break
                        if ok:
                            cross = n0; break
                res[(basis, ratio)] = cross
                row += "  r%.1f: n*=%s" % (ratio, cross)
            P(row)
        st = [res[('orig', r)] for r in (1.5, 2.0, 3.0, 4.0)]
        if all(s is not None for s in st):
            gc = [s * math.sqrt(r) for s, r in zip(st, (1.5, 2.0, 3.0, 4.0))]
            ac = [s * (1 + r) / 2 for s, r in zip(st, (1.5, 2.0, 3.0, 4.0))]
            P("    orig basis: START  %s  spread %.2fx" % (st, max(st) / min(st)))
            P("                GEOM-C %s  spread %.2fx"
              % ([round(x) for x in gc], max(gc) / min(gc)))
            P("                ARITH-C %s  spread %.2fx"
              % ([round(x) for x in ac], max(ac) / min(ac)))
        allv = [v for v in res.values() if v is not None]
        P("    full range over bases x ratios (START label): %d ... %d  = %.1fx"
          % (min(allv), max(allv), max(allv) / min(allv)))

    if stage in ('all', 'v4'):
        ARI = np.load(os.path.join(HERE, 'ver030_arith.npy'))
        O32 = BL_trunc(len(ARI), 32)
        P("=" * 100)
        P("V4  the lowest-zero cosine.  lambda_n = sum_gamma [2 - 2 cos(2 n arctan(1/(2gamma)))]")
        P("    (RH form, valid for the low zeros which are certified on the line).")
        g = [14.134725141734693, 21.022039638771555, 25.010857580145688,
             30.424876125859513, 32.935061587739190]
        n = np.arange(1, len(ARI) + 1, dtype=float)
        for K in (1, 2, 5):
            zm = sum(2 - 2 * np.cos(2 * n * math.atan(1 / (2 * gg))) for gg in g[:K])
            row = "    K=%d:" % K
            for lo, hi in ((20, 40), (40, 80), (80, 160), (160, 320), (320, 640)):
                nn = np.arange(lo, hi + 1, dtype=float)
                row += "  [%d,%d] %+.4f" % (lo, hi, R2(nn, ARI[lo - 1:hi], zm[lo - 1:hi]))
            P(row)
        row = "    prime M=32:"
        for lo, hi in ((20, 40), (40, 80), (80, 160), (160, 320), (320, 640)):
            nn = np.arange(lo, hi + 1, dtype=float)
            row += "  [%d,%d] %+.4f" % (lo, hi, R2(nn, ARI[lo - 1:hi], O32[lo - 1:hi]))
        P(row)

    P("\n[%.0fs] verification stage '%s' done" % (time.time() - t0, stage))
    with open(os.path.join(HERE, 'att030_verify_%s.out' % stage), 'w') as fh:
        fh.write("\n".join(OUT) + "\n")

# =========================================================================== V5/V6/V7
# appended: Dirichlet specimens, independent of att030_dirichlet.py

CH = {  # name: (q, parity a, chi as a dict on residues)
    'chi_-3': (3, 1, {1: 1, 2: -1}),
    'chi_5':  (5, 0, {1: 1, 2: -1, 3: -1, 4: 1}),
    'chi_8':  (8, 0, {1: 1, 3: -1, 5: -1, 7: 1}),
}

def chival(name, n):
    q, a, tab = CH[name]
    return tab.get(int(n) % q, 0)

def Lval(s, name, d=0):
    """L^{(d)}(s,chi) via Hurwitz: L = q^{-s} sum_a chi(a) zeta(s,a/q)."""
    q, a, tab = CH[name]
    if d == 0:
        return mp.power(q, -s) * mp.fsum(tab[r] * mp.zeta(s, mpf(r) / q) for r in tab)
    S0 = mp.fsum(tab[r] * mp.zeta(s, mpf(r) / q) for r in tab)
    S1 = mp.fsum(tab[r] * mp.zeta(s, mpf(r) / q, 1) for r in tab)
    return mp.power(q, -s) * (S1 - mp.log(q) * S0)

def Zhardy(t, name):
    q, a, tab = CH[name]
    s = mpc(mpf(1) / 2, t)
    th = (t / 2) * mp.log(mpf(q) / mp.pi) + mp.im(mp.loggamma((mpf(1) / 2 + a + mpc(0, t)) / 2))
    return mp.re(mp.expj(th) * Lval(s, name))

def g_arith_chi(z, name):
    s = s_of(z)
    return (Lval(s, name, 1) / Lval(s, name)) * s * s

def amp_curve(Y, nmax, ratio=2.0, npts=260):
    grid = np.unique(np.round(np.exp(np.linspace(math.log(10), math.log(nmax / ratio),
                                                 npts))).astype(int))
    ns, As = [], []
    for n0 in grid:
        n1 = int(n0 * ratio)
        if n1 > nmax or n1 - n0 < 8:
            continue
        nv = np.arange(n0, n1 + 1, dtype=float)
        ns.append(float(n0)); As.append(detr(nv, Y[n0 - 1:n1]).std() / (0.5 * (n0 + n1)) ** 0.25)
    return np.array(ns), np.array(As)

def n_half_of(ns, As, frac=0.3, plateau_from=700):
    m = ns >= plateau_from
    pl = np.median(As[m]) if m.any() else As[-5:].mean()
    thr = frac * pl
    for i in range(len(ns)):
        if As[i] >= thr and np.all(As[i:] >= 0.55 * thr):
            return ns[i], pl
    return float('nan'), pl

if __name__ == "__main__" and stage in ('v5', 'v6', 'v7'):
    if stage == 'v5':
        P("=" * 100)
        P("V5  gamma_1 by my own Hardy-Z sign scan, plus closed-form anchors for L(1,chi)")
        mp.dps = 30
        anchors = {'chi_-3': 2 * mp.pi / (6 * mp.sqrt(3)),
                   'chi_5': 2 * mp.log((1 + mp.sqrt(5)) / 2) / mp.sqrt(5),
                   'chi_8': 2 * mp.log(1 + mp.sqrt(2)) / mp.sqrt(8)}
        for nm in CH:
            v = Lval(mpf(1), nm); an = anchors[nm]
            P("    %-7s L(1,chi) = %s   class-number formula %s   diff %.2e"
              % (nm, mp.nstr(v, 15), mp.nstr(an, 15), float(abs(v - an))))
            lp = Lval(mpf(1), nm, 1) / v
            lp2 = mp.diff(lambda x: mp.log(Lval(x, nm)), mpf(1))
            P("        lambda_1^arith = L'/L(1,chi) = %s   (by mp.diff of log L: %s)"
              % (mp.nstr(lp, 15), mp.nstr(lp2, 15)))
            # real-axis zero scan on (0,1): a Siegel zero would invalidate the contour
            sg = [mp.sign(Lval(mpf(k) / 40, nm)) for k in range(1, 40)]
            P("        L(sigma,chi) sign changes on (0,1): %d" % sum(
                1 for i in range(len(sg) - 1) if sg[i] * sg[i + 1] < 0))
            prev = Zhardy(mpf('0.05'), nm); found = []
            t = 0.05
            while t < 25 and len(found) < 3:
                t += 0.05
                cur = Zhardy(mpf(t), nm)
                if prev * cur < 0:
                    found.append(float(mp.findroot(lambda u: Zhardy(u, nm),
                                                   (mpf(t - 0.05), mpf(t)), solver='bisect',
                                                   tol=mpf(10) ** -20)))
                prev = cur
            P("        first ordinates: %s" % ["%.6f" % g for g in found])

    if stage == 'v6':
        P("=" * 100)
        P("V6  lambda_n^arith for chi_-3 by MY contour (r=0.985, N=4096, dps=45)")
        c = os.path.join(HERE, 'ver030_chi-3.npy')
        if not os.path.exists(c):
            cc = coeffs_on_circle(lambda z: g_arith_chi(z, 'chi_-3'), '0.985', 4096, 2500, 45,
                                  tag='chi-3')
            np.save(c, np.array([float(x.real) for x in cc]))
        Y = np.load(c)
        T = np.load(os.path.join(HERE, 'att030_Y_chi_-3.npy'))
        P("    lambda_1^arith = %.12f   (030 reports 0.368281615970)" % Y[0])
        P("    vs THEIR chi_-3 array (n<=%d): max abs %.3e" % (len(T), np.abs(Y[:len(T)] - T).max()))

    if stage == 'v7':
        P("=" * 100)
        P("V7  is n_half a measurement, or an artefact of the statistic's own design?")
        ARI = np.load(os.path.join(HERE, 'ver030_arith.npy'))
        Ys = {'zeta': ARI}
        for nm in CH:
            f = os.path.join(HERE, 'ver030_%s.npy' % nm)
            if os.path.exists(f):
                Ys[nm] = np.load(f)
            else:
                Ys[nm] = np.load(os.path.join(HERE, 'att030_Y_%s.npy' % nm))
        g1 = {'zeta': 14.134725141734693, 'chi_-3': 8.039737155681467,
              'chi_5': 6.648453344727715, 'chi_8': 4.899973997007036}
        NM = 2000
        P("    (a) n_half on the REAL lambda arrays (their statistic, my code), f=0.3, ratio 2")
        nh = {}
        for k in Ys:
            ns, As = amp_curve(Ys[k][:NM], NM, 2.0)
            nh[k], pl = n_half_of(ns, As, 0.3)
            P("        %-7s gamma_1=%7.4f  n_half=%6.0f  plateau=%.4f  n_h/g=%.2f  n_h/g^2=%.3f"
              % (k, g1[k], nh[k], pl, nh[k] / g1[k], nh[k] / g1[k] ** 2))
        x = np.log([g1[k] for k in ['zeta', 'chi_-3', 'chi_5', 'chi_8']])
        y = np.log([nh[k] for k in ['zeta', 'chi_-3', 'chi_5', 'chi_8']])
        p_, c_ = np.polyfit(x, y, 1)
        P("        exponent p = %+.3f   r = %+.4f   (030 reports p = +0.982, r = +0.9987)"
          % (p_, np.corrcoef(x, y)[0, 1]))

        P("    (b) SYNTHETIC control: PURE lowest-zero cosine, NO primes, NO arithmetic at all.")
        P("        y_n = 2 - 2 cos(2 n arctan(1/(2 gamma))) for a grid of gamma.")
        gs = np.array([4.9, 6.65, 8.04, 11.0, 14.13, 20.0, 28.0])
        nhs = []
        for gg in gs:
            n = np.arange(1, NM + 1, dtype=float)
            ysyn = 2 - 2 * np.cos(2 * n * math.atan(1 / (2 * gg)))
            ns, As = amp_curve(ysyn, NM, 2.0)
            v, pl = n_half_of(ns, As, 0.3)
            nhs.append(v)
            P("        gamma=%6.2f  n_half=%6.0f   n_h/gamma = %.2f" % (gg, v, v / gg))
        nhs = np.array(nhs, float)
        ok = np.isfinite(nhs)
        p2, _ = np.polyfit(np.log(gs[ok]), np.log(nhs[ok]), 1)
        P("        SYNTHETIC exponent p = %+.3f  (a pure single cosine, zero arithmetic content)"
          % p2)
        P("    (c) same synthetic control at f = 0.5 and window ratio 3")
        for f, rat in ((0.5, 2.0), (0.3, 3.0)):
            vv = []
            for gg in gs:
                n = np.arange(1, NM + 1, dtype=float)
                ysyn = 2 - 2 * np.cos(2 * n * math.atan(1 / (2 * gg)))
                ns, As = amp_curve(ysyn, NM, rat)
                vv.append(n_half_of(ns, As, f)[0])
            vv = np.array(vv, float); ok = np.isfinite(vv)
            P("        f=%.1f ratio=%.1f: p = %+.3f   n_h/gamma = %s"
              % (f, rat, np.polyfit(np.log(gs[ok]), np.log(vv[ok]), 1)[0],
                 ["%.2f" % (a / b) for a, b in zip(vv[ok], gs[ok])]))
    with open(os.path.join(HERE, 'att030_verify_%s.out' % stage), 'w') as fh:
        fh.write("\n".join(OUT) + "\n")
