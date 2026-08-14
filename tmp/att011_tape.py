"""ATTEMPT 011 -- the Euler product as a SPECTRAL signature on the theta-tape.

HOUSE     : the theta-tape line amplitude  K(tau_n) = U Lambda_f(n)^2 / (L^2 n),
            plus divisor-class coherence (the Euler/non-Euler discriminator).
CLASSICAL : Landau (1911) / Gonek (1993) explicit formula for sums over zeros,
            extended to Dirichlet L-functions.

MECHANISM.  On the tape u = theta_f(t)/pi the density is 1 + dS_f/du, and
    S_f(t) = (1/pi) arg f(1/2+it) = -(1/pi) sum_{n>=2} Lambda_f(n) sin(t log n)/(sqrt n log n),
with Lambda_f(n) the Dirichlet coefficient of -f'/f.  Hence the tape spectrum has a line
at tau_n = log n / L of height U Lambda_f(n)^2/(L^2 n).  For an EULER function Lambda_f is
supported on prime powers; for an FE-only function it is not.  So the Euler product is an
ABSENCE of lines at composite non-prime-power n.

===========================  PRE-REGISTERED NULLS  ===========================
The noise floor of K is Exp(1):  median 0.693, 90th pct 2.303, 99th pct 4.605.
"Absent" means "indistinguishable from Exp(1)".  "Present" means K ~= predicted >> floor.

(a) L(chi_-3), q=3, chi(3)=0.
      PREDICT : lines at n = 2,4,5,7,8,11,... at FULL strength U Lambda(n)^2/(L^2 n);
                lines at n = 3,9,27 EXACTLY ABSENT (chi(3)=0).
      NULL    : K(3), K(9) are at the zeta-strength value U Lambda(n)^2/(L^2 n),
                i.e. K(3) ~ 7-9 in the T=1e5 window -- the tape does not see the character.
(b) Davenport-Heilbronn, FE but no Euler product.
      PREDICT : lines PRESENT at composite non-prime-powers n = 6,14,21,26 (and 12,18,24,28)
                at K = U Lambda_f(n)^2/(L^2 n), which is 6-14 in the T=1e5 window.
      NULL    : K(6), K(14), K(21), K(26) sit on the Exp(1) floor (<= 4.6) -- the
                instrument cannot separate Euler from non-Euler and the idea is dead.
(c) zeta, control on (b).
      PREDICT : K at the SAME composite n is on the Exp(1) floor.
      NULL    : zeta also shows composite lines -- then (b) is an artifact of the pipeline.

VALIDITY CRITERION, reported for every line:  R(n) = U log n log(1+W/T)/L^2 must be << 1.
=============================================================================
"""
import numpy as np, math, os, sys, time
mp = None
def P(*a): print(*a); sys.stdout.flush()

TMP = '/Users/samuellavery/work/helix_frobenius/tmp/'
A_DH = (4/np.sqrt(5))*np.sin(2*np.pi/5); B_DH = (4/np.sqrt(5))*np.sin(4*np.pi/5)
XI   = (np.sqrt(A_DH**2+B_DH**2)-A_DH)/B_DH
SPEC = {'zeta':  dict(q=1, a=0, coef=[1.0]),
        'chi-3': dict(q=3, a=1, coef=[0.0, 1.0, -1.0]),
        'DH':    dict(q=5, a=1, coef=[0.0, 1.0, XI, -XI, -1.0])}

_B = [1/6, -1/30, 1/42, -1/30, 5/66]
def logGamma_asym(z):
    z = np.asarray(z, complex); out = (z-0.5)*np.log(z) - z + 0.5*np.log(2*np.pi); zp = z.copy()
    for k in range(1, 6):
        out += _B[k-1]/(2*k*(2*k-1)*zp); zp = zp*z*z
    return out
def theta_f(t, q, a):
    t = np.asarray(t, float)
    return np.imag(logGamma_asym((0.5+a+1j*t)/2)) + (t/2)*math.log(q/np.pi)

def cvec(name, nmax):
    s = SPEC[name]; q = s['q']; c = np.array(s['coef'], float); n = np.arange(1, nmax+1)
    return c[n % q] if q > 1 else np.ones(nmax)

def Zmain(t, name, cs, Nmax):
    """AFE main sum, sharp cutoff N=floor(sqrt(q t/2pi)).  Gated in att011_gate.py:
    max|dZ| vs mpmath at t~1e5 = 0.054 (zeta), 0.025 (chi-3), 0.0045 (DH)."""
    sp = SPEC[name]; q, a = sp['q'], sp['a']
    t = np.asarray(t, float)
    Nn = np.floor(np.sqrt(q*t/(2*np.pi))).astype(np.int64)
    th = theta_f(t, q, a); s = np.zeros_like(t)
    for n in range(1, Nmax+1):
        c = cs[n-1]
        if c == 0.0: continue
        m = Nn >= n
        s[m] += c*np.cos(th[m] - t[m]*math.log(n))/math.sqrt(n)
    return 2*s

def zeros_of(name, T, W, h, nbis=45):
    sp = SPEC[name]; q = sp['q']
    Nmax = int(math.floor(math.sqrt(q*(T+W)/(2*np.pi)))); cs = cvec(name, Nmax)
    out = []
    CH = 400000
    g = np.arange(T, T+W, h)
    sb = np.empty(len(g), bool)
    for i in range(0, len(g), CH):
        sb[i:i+CH] = np.signbit(Zmain(g[i:i+CH], name, cs, Nmax))
    idx = np.nonzero(sb[:-1] != sb[1:])[0]
    a_, b_ = g[idx].copy(), g[idx+1].copy()
    for _ in range(nbis):
        m = (a_+b_)/2
        left = np.signbit(Zmain(a_, name, cs, Nmax)) != np.signbit(Zmain(m, name, cs, Nmax))
        b_ = np.where(left, m, b_); a_ = np.where(left, a_, m)
    return (a_+b_)/2

def tape(g, name):
    sp = SPEC[name]; q, a = sp['q'], sp['a']
    u = theta_f(g, q, a)/np.pi; u = u - u[0]
    return u, u[-1]

def spec_at(u, taus):
    F = np.exp(2j*np.pi*np.outer(np.asarray(taus, float), u)).sum(axis=1)
    return np.abs(F)**2

LAMS = np.load(TMP+'att011_lamf.npy')          # rows: zeta, chi-3, DH ; index = n
ROW = {'zeta': 0, 'chi-3': 1, 'DH': 2}
NS = list(range(2, 33))

def run(name, T, W, h, tag, cache=True):
    fn = TMP + f'att011_z_{name}_{T:.0e}_{int(W)}.npy'
    if cache and os.path.exists(fn):
        g = np.load(fn); gated = 'cached'
    else:
        t0 = time.time(); g = zeros_of(name, T, W, h)
        g2 = zeros_of(name, T, W, h/2)
        gated = 'PASS' if len(g2) == len(g) else f'FAIL h:{len(g)} h/2:{len(g2)}'
        if len(g2) != len(g): g = g2
        if cache: np.save(fn, g)
        P(f"    [{name} T={T:.0e} W={W:.0f} h={h}]  {len(g)} zeros, refine-gate {gated}, {time.time()-t0:.0f}s")
    u, U = tape(g, name)
    tc = (g[0]+g[-1])/2; q, a = SPEC[name]['q'], SPEC[name]['a']
    L = theta_f(tc+1.0, q, a) - theta_f(tc-1.0, q, a)          # = 2 theta'(tc)
    Udens = (theta_f(g[-1], q, a) - theta_f(g[0], q, a))/np.pi  # tape length (= U)
    lam = LAMS[ROW[name]]
    taus = [math.log(n)/L for n in NS]
    A = spec_at(u, taus)
    return dict(name=name, T=T, W=W, g=g, u=u, U=U, L=L, nz=len(g), lam=lam,
                A=A, taus=taus, tag=tag, tc=tc)

def report(r, ns=NS):
    U, L, lam, nz = r['U'], r['L'], r['lam'], r['nz']
    P(f"\n  {r['name']}  T={r['T']:.0e}  W={r['W']:.0f}  zeros={nz}  tape U={U:.1f}  "
      f"L={L:.4f}  census deficit U-nz = {U-nz:+.1f}")
    P(f"    {'n':>3}{'Lam_f':>10}{'pred K':>9}{'obs K':>9}{'obs/pred':>10}{'R(n)':>7}  kind")
    rows = []
    sel = [(n, r['A'][NS.index(n)]) for n in ns]     # index by n, never by position
    for n, a in sel:
        K = a/U
        pred = U*lam[n]**2/(L*L*n)
        R = U*math.log(n)*math.log(1+r['W']/r['T'])/(L*L)
        kind = 'PP' if _isprimepower(n) else 'comp'
        rat = (K/pred) if pred > 1e-9 else float('nan')
        P(f"    {n:>3}{lam[n]:>10.4f}{pred:>9.3f}{K:>9.3f}"
          f"{('%10.3f'%rat) if pred>1e-9 else '         -'}{R:>7.2f}  {kind}")
        rows.append((n, lam[n], pred, K, R, kind))
    return rows

def _isprimepower(n):
    for p in (2,3,5,7,11,13,17,19,23,29,31):
        m = n
        while m % p == 0: m //= p
        if m == 1: return True
    return False

def noisefloor(r, ntau=800, seed=3):
    """Empirical Exp(1) floor: K at tau away from every log n / L with Lam_f(n) != 0."""
    U, L, lam = r['U'], r['L'], r['lam']
    bad = [math.log(n)/L for n in range(2, 400) if n < len(lam) and abs(lam[n]) > 1e-9]
    bad += [math.log(n)/L for n in range(2, 400)]      # be strict: avoid ALL log n / L
    rng = np.random.default_rng(seed); taus = []
    while len(taus) < ntau:
        t = rng.uniform(0.02, 0.40)
        if min(abs(t-b) for b in bad) > 4.0/U: taus.append(t)
    A = spec_at(r['u'], taus)/U
    return np.median(A), np.percentile(A, 90), np.percentile(A, 99), A.mean()

if __name__ == '__main__':
    P(__doc__)
    P("="*100)
    P("GATE G4 -- pipeline positive control: main-sum-only zero finder vs the CACHED EXACT")
    P("zeta zeros (att010, RS with the Psi correction, gated 4.9e-7 vs mpmath.zetazero).")
    cz = np.load(TMP+'att010_zeros_1e+05.npy')
    T, W, h = 1e5, 1200.0, 0.020
    gmine = run('zeta', T, W, h, 'G4')['g']
    sel = cz[(cz >= gmine[0]-1e-6) & (cz <= gmine[-1]+1e-6)]
    P(f"   cached exact in [{gmine[0]:.4f},{gmine[-1]:.4f}]: {len(sel)}   main-sum-only: {len(gmine)}")
    if len(sel) == len(gmine):
        P(f"   max |gamma_mine - gamma_cached| = {np.abs(gmine-sel).max():.3e}   "
          f"(mean spacing {(gmine[-1]-gmine[0])/len(gmine):.3f})")
    P("="*100)

    RES = {}
    P("\n### MAIN RUN  T = 1e5,  W = 1200  (three specimens, matched window)")
    for nm in ('zeta','chi-3','DH'):
        RES[(nm,1e5)] = run(nm, 1e5, 1200.0, 0.020, 'main')
    for nm in ('zeta','chi-3','DH'):
        report(RES[(nm,1e5)])
        m, p90, p99, mean = noisefloor(RES[(nm,1e5)])
        P(f"    empirical K noise floor (800 off-line taus): median {m:.3f} (Exp(1): 0.693), "
          f"90th {p90:.3f} (2.303), 99th {p99:.3f} (4.605), mean {mean:.3f} (1.000)")

    P("\n### CONTROL -- aim at the WRONG L.  Lines must COLLAPSE (structure missing, not cancelled).")
    P(f"    {'spec':>6}{'c=0.85':>9}{'0.95':>9}{'1.00':>9}{'1.05':>9}{'1.15':>9}   "
      f"(mean K over the prime powers n<=32 with Lam_f != 0)")
    for nm in ('zeta','chi-3'):
        r = RES[(nm,1e5)]; row = f"    {nm:>6}"
        good = [n for n in NS if abs(r['lam'][n]) > 1e-9]
        for c in (0.85, 0.95, 1.00, 1.05, 1.15):
            A = spec_at(r['u'], [math.log(n)/(c*r['L']) for n in good])/r['U']
            row += f"{A.mean():>9.3f}"
        P(row)

    P("\n\n### NOISE AUDIT 1 -- window sweep at T=1e5 (drives R up and down)")
    for W in (500.0, 800.0, 1800.0):
        for nm in ('chi-3','DH'):
            r = run(nm, 1e5, W, 0.020, 'sweep')
            report(r, ns=[2,3,4,5,6,7,9,14,21,26])

    P("\n\n### NOISE AUDIT 2 -- height sweep, T = 1e6, W = 3000")
    for nm in ('zeta','chi-3','DH'):
        r = run(nm, 1e6, 3000.0, 0.015, 'height')
        report(r)
        m, p90, p99, mean = noisefloor(r)
        P(f"    empirical K noise floor: median {m:.3f}, 90th {p90:.3f}, 99th {p99:.3f}, mean {mean:.3f}")
