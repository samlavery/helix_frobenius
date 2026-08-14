"""ADVERSARIAL VERIFICATION of attempt 011.  Written from scratch.

Independence choices (deliberately different from att011_*.py):
  * theta via scipy.special.loggamma  (NOT their 5-term Stirling asymptotic)
  * Lambda_f via the LOG-SERIES  log f = sum_k (-1)^{k+1} g^{*k}/k  with Dirichlet
    convolution powers (NOT their  a_n log n = sum_{d|n} Lambda(d) a_{n/d}  recursion)
  * a NEW window T = 3e5, W = 1500 that they never ran, plus their T=1e6/W=3000
  * my own zero finder, different grid, refinement by 60 bisections
  * DH's OWN noise floor reported (the record quotes only zeta's and chi-3's)
  * NEW TEST: DH census deficit as a function of HEIGHT (T = 1e3 .. 1e6) at matched
    tape length.  If the deficit is off-line zeros with density ~ c per unit t, the
    FRACTION must fall like 1/log(5T/2pi).  If it is flat, it is not off-line zeros.
"""
import numpy as np, math, sys, time, os
from scipy.special import loggamma
import mpmath as mp
mp.mp.dps = 25
def P(*a): print(*a); sys.stdout.flush()
TMP = '/Users/samuellavery/work/helix_frobenius/tmp/'

# ---------------------------------------------------------------- specimens
A_ = (4/np.sqrt(5))*np.sin(2*np.pi/5); B_ = (4/np.sqrt(5))*np.sin(4*np.pi/5)
XI = (np.sqrt(A_**2+B_**2)-A_)/B_
SPEC = {'zeta':  dict(q=1, a=0, c=np.array([1.0])),
        'chi-3': dict(q=3, a=1, c=np.array([0.0, 1.0, -1.0])),
        'DH':    dict(q=5, a=1, c=np.array([0.0, 1.0, XI, -XI, -1.0]))}

def theta(t, q, a):
    """theta_f(t) = Im logGamma((1/2+a+it)/2) + (t/2) log(q/pi).  scipy loggamma."""
    t = np.asarray(t, float)
    return np.imag(loggamma((0.5+a+1j*t)/2)) + (t/2)*math.log(q/math.pi)

def coeffs(name, N):
    s = SPEC[name]; q = s['q']
    n = np.arange(1, N+1)
    return s['c'][n % q] if q > 1 else np.ones(N)

def Zmain(t, name, cs=None):
    s = SPEC[name]; q, a = s['q'], s['a']
    t = np.atleast_1d(np.asarray(t, float))
    Nn = np.floor(np.sqrt(q*t/(2*math.pi))).astype(np.int64)
    Nmax = int(Nn.max())
    if cs is None or len(cs) < Nmax: cs = coeffs(name, Nmax)
    th = theta(t, q, a); out = np.zeros_like(t)
    for n in range(1, Nmax+1):
        c = cs[n-1]
        if c == 0.0: continue
        m = Nn >= n
        out[m] += c*np.cos(th[m] - t[m]*math.log(n))/math.sqrt(n)
    return 2*out

# ================================================================ S0 identity
P("="*92)
P("S0  XI and the Davenport-Heilbronn decomposition (independent algebra)")
P(f"    XI = {XI:.15f}   (Titchmarsh/DH literature value 0.28407904384...)")
CHI = np.array([0, 1, 1j, -1j, -1])          # quartic chi mod 5, chi(2)=i
Ac  = (1 - 1j*XI)/2
aDH = SPEC['DH']['c']
e1 = max(abs(aDH[r] - 2*np.real(Ac*CHI[r])) for r in range(5))
tau = sum(CHI[r]*np.exp(2j*np.pi*r/5) for r in range(1, 5))
eps = tau/(1j*math.sqrt(5))
P(f"    max_r |a_r - 2 Re(A chi(r))|            = {e1:.3e}")
P(f"    |eps_chi| = {abs(eps):.15f} ;  arg(A) + arg(eps)/2 = {np.angle(Ac)+np.angle(eps)/2:.3e}")
P("    => f_DH = A L(s,chi) + conj(A) L(s,chibar) EXACTLY (this is the DH definition).")

# ================================================================ S1 Lambda_f
P("\n" + "="*92)
P("S1  Lambda_f by an INDEPENDENT route: log f = sum_k (-1)^(k+1) g^{*k}/k")
def dconv(x, y, N):
    out = np.zeros(N+1)
    nz = np.nonzero(x[:N+1])[0]
    for d in nz:
        if d == 0: continue
        m = N//d
        if m == 0: break
        out[d::d][:m] += x[d]*y[1:m+1]
    return out
def lamf_log(name, N):
    a = np.zeros(N+1); a[1:] = coeffs(name, N)
    assert a[1] == 1.0
    g = a.copy(); g[1] = 0.0
    b = np.zeros(N+1); pw = g.copy(); k = 1
    while True:
        b += ((-1)**(k+1)/k)*pw
        if 2**(k+1) > N: break
        pw = dconv(pw, g, N); k += 1
    n = np.arange(N+1)
    return b*np.log(np.maximum(n, 1))
N = 20000
LAM = {}
for nm in ('zeta', 'chi-3', 'DH'):
    t0 = time.time(); L = lamf_log(nm, N); LAM[nm] = L
    ref = np.load(TMP+f'att011_lamfull_{nm}.npy')
    run = np.maximum.accumulate(np.abs(L))
    x = np.log(np.arange(200, N+1))
    fits = []
    for lo, hi in ((200, 2000), (2000, N), (5000, N)):
        xx = np.log(np.arange(lo, hi+1)); yy = np.log(np.maximum(run[lo:hi+1], 1e-300))
        fits.append(np.polyfit(xx, yy, 1)[0])
    P(f"    {nm:>6}  max_{{n<=20000}}|Lambda_f| = {run[N]:10.4f}   "
      f"max|mine - theirs| = {np.abs(L-ref).max():.2e}   "
      f"exponents [200,2e3]/[2e3,2e4]/[5e3,2e4] = {fits[0]:.4f}/{fits[1]:.4f}/{fits[2]:.4f}"
      f"   ({time.time()-t0:.0f}s)")
P(f"    log(19993) = {math.log(19993):.4f}")
# independent gate: sum Lambda_f(n) n^-3  vs  -f'/f(3) by high precision mpmath
for nm in ('zeta', 'chi-3', 'DH'):
    lhs = float((LAM[nm][2:N+1]*np.arange(2, N+1)**(-3.0)).sum())
    q = SPEC[nm]['q']; cc = SPEC[nm]['c']
    def fser(s):
        tot = mp.mpf(0)
        for r in range(1, q+1):
            v = cc[r % q]
            if v == 0: continue
            vv = mp.mpf(str(XI)) if abs(abs(v)-XI) < 1e-12 else mp.mpf(1)
            if v < 0: vv = -vv
            tot += vv*mp.zeta(s, mp.mpf(r)/q)
        return mp.power(q, -s)*tot
    d = mp.diff(fser, mp.mpf(3))
    rhs = float(-d/fser(mp.mpf(3)))
    P(f"    {nm:>6}  sum Lambda_f n^-3 = {lhs:.12f}   -f'/f(3) [mpmath] = {rhs:.12f}   "
      f"diff {abs(lhs-rhs):.2e}")

# ================================================================ S2 gates
P("\n" + "="*92)
P("S2  GATE: AFE main sum vs mpmath, my theta (scipy loggamma) vs their Stirling")
def Zex(t, name):
    s = SPEC[name]; q, a = s['q'], s['a']
    tm = mp.mpf(float(t)); ss = mp.mpf(0.5)+1j*tm
    th = mp.im(mp.loggamma((mp.mpf(0.5)+a+1j*tm)/2)) + (tm/2)*mp.log(mp.mpf(q)/mp.pi)
    tot = mp.mpc(0)
    q_, cc = s['q'], s['c']
    for r in range(1, q_+1):
        v = cc[r % q_]
        if v == 0: continue
        vv = mp.mpf(str(XI)) if abs(abs(v)-XI) < 1e-12 else mp.mpf(1)
        if v < 0: vv = -vv
        tot += vv*mp.zeta(ss, mp.mpf(r)/q_)
    return mp.exp(1j*th)*mp.power(q_, -ss)*tot
rng = np.random.default_rng(2026)
# theta: scipy loggamma vs mpmath loggamma (exactness of MY theta at the working heights)
for nm in ('zeta', 'chi-3', 'DH'):
    q, a = SPEC[nm]['q'], SPEC[nm]['a']
    w = 0.0
    for t in (3e5, 1e6, 1e6+2999.0):
        ref = float(mp.im(mp.loggamma((mp.mpf(0.5)+a+1j*mp.mpf(t))/2)) + (mp.mpf(t)/2)*mp.log(mp.mpf(q)/mp.pi))
        w = max(w, abs(float(theta(t, q, a))-ref))
    P(f"    {nm:>6}  max |theta_scipy - theta_mpmath| at t=3e5,1e6 = {w:.2e} rad")
# AFE main sum vs mpmath at moderate t (Hurwitz zeta is tractable there)
for nm in ('zeta', 'chi-3', 'DH'):
    for T0 in (2000.0, 20000.0):
        ts = rng.uniform(T0, T0+50, 8)
        ex = np.array([float(mp.re(Zex(float(t), nm))) for t in ts])
        im = max(abs(float(mp.im(Zex(float(t), nm)))/abs(float(mp.re(Zex(float(t), nm))))) for t in ts[:2])
        ap = Zmain(ts, nm)
        P(f"    {nm:>6} T={T0:.0e}  max|dZ| = {np.abs(ap-ex).max():.4f}   rms|Z| = {ex.std():.3f}"
          f"   |Im Z|/|Re Z| = {im:.1e}   (t^-1/4 = {T0**-0.25:.3f})")

# ================================================================ zero finder
def zeros(name, T, W, h, nb=60):
    s = SPEC[name]; q = s['q']
    Nmax = int(math.floor(math.sqrt(q*(T+W)/(2*math.pi))))
    cs = coeffs(name, Nmax)
    g = np.arange(T, T+W, h)
    sb = np.empty(len(g), bool)
    for i in range(0, len(g), 300000):
        sb[i:i+300000] = np.signbit(Zmain(g[i:i+300000], name, cs))
    k = np.nonzero(sb[:-1] != sb[1:])[0]
    lo, hi = g[k].copy(), g[k+1].copy()
    for _ in range(nb):
        m = 0.5*(lo+hi)
        f = np.signbit(Zmain(lo, name, cs)) != np.signbit(Zmain(m, name, cs))
        hi = np.where(f, m, hi); lo = np.where(f, lo, m)
    return 0.5*(lo+hi)

def isPP(n):
    for p in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59):
        m = n
        while m % p == 0: m //= p
        if m == 1: return p
    return 0

def tape_run(name, T, W, h):
    g = zeros(name, T, W, h)
    g2 = zeros(name, T, W, h/2)
    gate = 'PASS' if len(g) == len(g2) else f'FAIL {len(g)} vs {len(g2)}'
    if len(g2) != len(g): g = g2
    q, a = SPEC[name]['q'], SPEC[name]['a']
    u = theta(g, q, a)/math.pi; u -= u[0]; U = u[-1]
    tc = 0.5*(g[0]+g[-1]); L = theta(tc+1.0, q, a) - theta(tc-1.0, q, a)
    return dict(name=name, T=T, W=W, g=g, u=u, U=U, L=L, nz=len(g), gate=gate)

def K_at(r, taus):
    return np.abs(np.exp(2j*np.pi*np.outer(np.asarray(taus, float), r['u'])).sum(axis=1))**2/r['U']

def floor_of(r, ntau=800, seed=17):
    U, L = r['U'], r['L']
    bad = np.array([math.log(n)/L for n in range(2, 400)])
    rg = np.random.default_rng(seed); out = []
    while len(out) < ntau:
        t = rg.uniform(0.02, 0.40)
        if np.abs(t-bad).min() > 4.0/U: out.append(t)
    A = K_at(r, out)
    return np.median(A), np.percentile(A, 90), np.percentile(A, 99), A.mean()

def report(r, LAMf):
    U, L = r['U'], r['L']
    P(f"\n  {r['name']:>6} T={r['T']:.0e} W={r['W']:.0f}  zeros={r['nz']}  U={U:.1f}  L={L:.4f}"
      f"  deficit U-nz = {U-r['nz']:+.1f}  ({100*(U-r['nz'])/U:.2f}%)  refine-gate {r['gate']}")
    ns = list(range(2, 33))
    A = K_at(r, [math.log(n)/L for n in ns])
    P(f"     {'n':>3}{'Lam_f':>10}{'predK':>9}{'obsK':>9}{'o/p':>9}{'fullK':>8}{'o/full':>8}  kind")
    rows = []
    for i, n in enumerate(ns):
        pred = U*LAMf[n]**2/(L*L*n)
        p = isPP(n)
        full = U*math.log(p)**2/(L*L*n) if p else 0.0
        rat = A[i]/pred if pred > 1e-9 else float('nan')
        rf = A[i]/full if full > 1e-9 else float('nan')
        P(f"     {n:>3}{LAMf[n]:>10.4f}{pred:>9.3f}{A[i]:>9.3f}"
          f"{('%9.3f' % rat) if pred > 1e-9 else '        -'}{full:>8.2f}"
          f"{('%8.3f' % rf) if full > 1e-9 else '       -'}  {'PP' if p else 'comp'}")
        rows.append((n, pred, A[i], p))
    m, p90, p99, mean = floor_of(r)
    P(f"     NOISE FLOOR (800 off-line taus): median {m:.4f}  90th {p90:.4f}  99th {p99:.4f}  mean {mean:.4f}")
    return rows, (m, p90, p99, mean)

# ================================================================ S3 new window
if __name__ == '__main__':
    stage = sys.argv[1] if len(sys.argv) > 1 else 'all'

    if stage in ('all', 's3'):
        P("\n" + "="*92)
        P("S3  TAPE at a NEW window T = 3e5, W = 1500  (never run by the record)")
        RES = {}
        for nm in ('zeta', 'chi-3', 'DH'):
            t0 = time.time(); r = tape_run(nm, 3e5, 1500.0, 0.02); RES[nm] = r
            rows, fl = report(r, LAM[nm])
            RES[nm]['rows'] = rows; RES[nm]['floor'] = fl
            P(f"     ({time.time()-t0:.0f}s)")
        P("\n  SUMMARY at T=3e5:")
        for nm in ('zeta', 'chi-3', 'DH'):
            r = RES[nm]; rows = r['rows']; fl = r['floor']
            pp = [(n, o/p) for n, p, o, k in rows if k and p > 1e-9]
            cm = [(n, o) for n, p, o, k in rows if not k]
            P(f"    {nm:>6}: prime-power obs/pred median {np.median([v for _, v in pp]):.3f} "
              f"[{min(v for _,v in pp):.3f},{max(v for _,v in pp):.3f}] over {len(pp)} lines;"
              f"  max composite K = {max(v for _, v in cm):.3f} at n={max(cm, key=lambda z: z[1])[0]}"
              f"  (floor 99th {fl[2]:.3f})")
        r = RES['chi-3']
        for n in (3, 9, 27):
            k = K_at(r, [math.log(n)/r['L']])[0]
            zs = r['U']*math.log(3)**2/(r['L']**2*n)
            P(f"    chi-3  K({n}) = {k:.4f}   if-present zeta-strength = {zs:.3f}   ratio {k/zs:.2e}")
        r = RES['DH']
        for n in (6, 14, 21, 26):
            k = K_at(r, [math.log(n)/r['L']])[0]
            pr = r['U']*LAM['DH'][n]**2/(r['L']**2*n)
            P(f"    DH     K({n}) = {k:.4f}   Lambda_f pred = {pr:.3f}   obs/pred {k/pr:.4f}"
              f"   floor(median {r['floor'][0]:.3f}, 99th {r['floor'][2]:.3f})"
              f"   R = {r['U']*math.log(n)*math.log(1+r['W']/r['T'])/r['L']**2:.2f}")

    if stage in ('all', 's4'):
        P("\n" + "="*92)
        P("S4  DH CENSUS DEFICIT vs HEIGHT at MATCHED tape length (~2000 zeros).")
        P("    If the deficit is off-line zeros of density ~c per unit t (the classical")
        P("    ~cT count), the FRACTION must scale like 1/L, L = log(5T/2pi).")
        base = None
        for T in (1e3, 1e4, 1e5, 1e6):
            L0 = math.log(5*T/(2*math.pi))
            W = 2000*2*math.pi/L0
            h = min(0.02, 2*math.pi/L0/25)
            r = tape_run('DH', T, W, h)
            frac = 100*(r['U']-r['nz'])/r['U']
            if base is None: base = (frac, r['L'])
            P(f"    T={T:.0e}  W={W:7.1f}  h={h:.4f}  U={r['U']:7.1f}  zeros={r['nz']:5d}"
              f"  deficit {frac:6.2f}%   1/L-scaled from T=1e3: {base[0]*base[1]/r['L']:6.2f}%"
              f"   gate {r['gate']}")
        P("    zeta control (finder loss only):")
        for T in (1e3, 1e5, 1e6):
            L0 = math.log(T/(2*math.pi)); W = 2000*2*math.pi/L0
            h = min(0.02, 2*math.pi/L0/25)
            r = tape_run('zeta', T, W, h)
            P(f"    T={T:.0e}  U={r['U']:7.1f}  zeros={r['nz']:5d}  deficit "
              f"{100*(r['U']-r['nz'])/r['U']:6.2f}%   gate {r['gate']}")

    if stage in ('all', 's6'):
        P("\n" + "="*92)
        P("S6  RESIDUE-CLASS SPLIT (H_avg) at the NEW window T=3e5, W=1500, and the")
        P("    quartic-character control, with COMPLEX coefficients.")
        PSI = np.angle(eps)/2
        def Zc(t, cf, q, a, psi):
            t = np.atleast_1d(np.asarray(t, float))
            Nn = np.floor(np.sqrt(q*t/(2*math.pi))).astype(np.int64); Nmax = int(Nn.max())
            th = theta(t, q, a) - psi; out = np.zeros_like(t)
            for n in range(1, Nmax+1):
                c = cf[n % q]
                if c == 0: continue
                m = Nn >= n; ph = th[m] - t[m]*math.log(n)
                out[m] += (c.real*np.cos(ph) - c.imag*np.sin(ph))/math.sqrt(n)
            return 2*out
        def zeros_c(cf, q, a, psi, T, W, h, nb=60):
            g = np.arange(T, T+W, h); sb = np.empty(len(g), bool)
            for i in range(0, len(g), 300000):
                sb[i:i+300000] = np.signbit(Zc(g[i:i+300000], cf, q, a, psi))
            k = np.nonzero(sb[:-1] != sb[1:])[0]
            lo, hi = g[k].copy(), g[k+1].copy()
            for _ in range(nb):
                m = 0.5*(lo+hi)
                fl = np.signbit(Zc(lo, cf, q, a, psi)) != np.signbit(Zc(m, cf, q, a, psi))
                hi = np.where(fl, m, hi); lo = np.where(fl, lo, m)
            return 0.5*(lo+hi)
        T, W, h = 3e5, 1500.0, 0.02
        out = {}
        for nm, cf, psi in (('chi5q', CHI.astype(complex), PSI),
                            ('DH', SPEC['DH']['c'].astype(complex), 0.0)):
            g = zeros_c(cf, 5, 1, psi, T, W, h)
            u = theta(g, 5, 1)/math.pi; u -= u[0]; U = u[-1]
            tc = 0.5*(g[0]+g[-1]); L = theta(tc+1.0, 5, 1)-theta(tc-1.0, 5, 1)
            out[nm] = dict(u=u, U=U, L=L, nz=len(g))
            P(f"    {nm:>6}: zeros={len(g)}  U={U:.1f}  L={L:.4f}  deficit {100*(U-len(g))/U:.2f}%")
        rows = []
        for n in range(2, 61):
            p = isPP(n)
            if p == 0 or n % 5 == 0: continue
            v = []
            for nm in ('chi5q', 'DH'):
                r = out[nm]
                k = np.abs(np.exp(2j*np.pi*(math.log(n)/r['L'])*r['u']).sum())**2/r['U']
                full = r['U']*math.log(p)**2/(r['L']**2*n)
                v.append(k/full)
            rows.append((n, n % 5, v[0], v[1]))
        rows = np.array(rows)
        for lbl, msk in (('+-1 mod 5', (rows[:,1]==1)|(rows[:,1]==4)),
                         ('+-2 mod 5', (rows[:,1]==2)|(rows[:,1]==3))):
            P(f"    ALL n<=60, {lbl}:  chi5q obs/full median {np.median(rows[msk,2]):.3f} "
              f"[{rows[msk,2].min():.3f},{rows[msk,2].max():.3f}]  |  "
              f"DH obs/full median {np.median(rows[msk,3]):.3f} "
              f"[{rows[msk,3].min():.3f},{rows[msk,3].max():.3f}]  (n={int(msk.sum())})")
        oos = rows[rows[:,0] > 32]
        for lbl, msk in (('+-1 mod 5', (oos[:,1]==1)|(oos[:,1]==4)),
                         ('+-2 mod 5', (oos[:,1]==2)|(oos[:,1]==3))):
            P(f"    n>32      {lbl}:  chi5q median {np.median(oos[msk,2]):.3f}  "
              f"DH median {np.median(oos[msk,3]):.3f}   n={oos[msk,0].astype(int).tolist()}")
        P("    per-n detail (n, n%5, chi5q obs/full, DH obs/full):")
        for n, m5, a1, a2 in rows:
            P(f"      {int(n):>3} {int(m5)}   {a1:8.3f}   {a2:8.3f}")

    if stage in ('all', 's5'):
        P("\n" + "="*92)
        P("S5  REPRODUCE the record's headline window T=1e6, W=3000, with my code")
        for nm in ('zeta', 'chi-3', 'DH'):
            t0 = time.time(); r = tape_run(nm, 1e6, 3000.0, 0.015)
            rows, fl = report(r, LAM[nm])
            pp = [o/p for n, p, o, k in rows if k and p > 1e-9]
            cm = [o for n, p, o, k in rows if not k]
            P(f"     prime-power obs/pred median {np.median(pp):.3f}; max composite K {max(cm):.3f}"
              f"   ({time.time()-t0:.0f}s)")
