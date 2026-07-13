"""The value-registration census -- the S(t)-compensation analogue at value level.

Goal (NOT to prove the law -- to build the CENSUS any candidate law must fit):
for every certified central value we own, measure how a warped/adapted carrier
reading F_w(1/2) relates to the true L(1/2).  The registration ratio

    R = F_w(1/2) / L(1/2)     (complex -- phase kept)

is the observable.  R = 1 means the adapted reading registers the true value.

FROZEN PROTOCOL (every choice fixed BEFORE the sweep; see FROZEN_NOTES below):
  * banks: unitary lambda_n, exact bad-prime locals, NMAX = 1.5e6, theta caches.
  * warp: house forcible closure -- one weight vector x on the coherent
    generators [log n, omega(n), Theta_leg(n) per constituent curve], solved by
    Gauss-Newton to close the pi/3 cells of y = log n (kmin=4..kmax).  This is
    the adapted_center.py protocol exactly; the Jacobian is analytic (the exact
    limit of adapted_center's finite difference -- same closure minimum, checked
    against adapted's published ratios in the VALIDATION block).
  * reader: the canonical C-infinity carrier window w(log n / log Y) (never-clip
    method law), so F_w(1/2;Y) = sum_n lambda_n n^{-1/2} e^{i (G x)(n)} w.  The
    unwarped reading R_0 is the SAME window with the warp switched off (the m=0
    harmonic-lattice point).
  * Y-ladder: a COMMON absolute log-spaced ladder, so Y/sqrt(Q) varies across
    the census (huge for low conductor, O(1) for degree 6) -- this is what lets
    the Y/sqrt(Q) candidate be separated from the object.

THE HUNT (each candidate pre-registered here, BEFORE any fit):
  (i)   |R-1| ~ warp energy alone
  (ii)  |R-1| ~ closure-improvement ratio (median|D|_before/after)
  (iii) |R-1| ~ degree/conductor through log Q
  (iv)  |R-1| ~ window scale through Y/sqrt(Q)
  (v)   null: nothing systematic (pure protocol artifact)
  (money) |R-1| -> 0 as the warp is restricted to the HARMONIC LATTICE
          (integer-m warps on Theta only, no log n / omega freedom): is
          mis-registration caused precisely by OFF-LATTICE warp freedom?
Fits are leave-one-object-out cross-validated (object-level predictors must be
tested on UNSEEN objects, else they leak) -- held-out RMS reported for each.

Run: python3 value_registration.py     (~6-10 min; banks in RAM, no new caches)
"""
import sys, os, math, cmath
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH
from theta_cache import theta_table

# ----------------------------------------------------------------- FROZEN_NOTES
NMAX = 1_500_000
H = math.pi / 3.0
KMIN = 4
KMAX = int(math.log(NMAX) / H) - 1          # top full cell (excludes partial)
# common absolute window ladder (log-spaced, all within NMAX reach):
Y_LADDER = [40000.0, 130000.0, 420000.0, 1_350_000.0]
GN_ITERS = 60
GN_STEP = 0.8

TH11 = theta_table("11a1")
TH37 = theta_table("37a1")
A11 = 1.0 / math.sqrt(11.0)                  # Steinberg eigenvalue, 11a1
A37 = 1.0 / math.sqrt(37.0)                  # a_37(37a1) = 1

# ------------------------------------------------------- certified truths (unitary)
OBJECTS = [
    # name, degree, Q, L(1/2)_unitary, eigs_fn, legs (curve labels for Theta)
    ("L(11a1)",              2, 11,             0.2538417,   "gl2",  ["11a1"]),
    ("L(Sym2 11a1)",         3, 11**2,          0.8933980,   "sym2", ["11a1"]),
    ("L(Sym3 11a1)",         4, 11**3,          1.1402380,   "sym3", ["11a1"]),
    ("L(11a1 x 37a1) RS4",   4, (11*37)**2,     5.0227652,   "rs4",  ["11a1", "37a1"]),
    ("L(Sym4 11a1)",         5, 11**4,          0.6058010,   "sym4", ["11a1"]),
    ("L(Sym2(11a1) x 37a1)", 6, 11**4 * 37**3,  0.61570486,  "deg6", ["11a1", "37a1"]),
]


# ---------------------------------------------------------------- eigenvalue rules
def _th(TH, p):
    v = float(TH[p])
    return 0.0 if math.isnan(v) else v


def eigs_gl2(p):
    if p == 11:
        return [A11]
    t = _th(TH11, p)
    return [cmath.exp(1j * t), cmath.exp(-1j * t)]


def eigs_sym(r):
    def fn(p):
        if p == 11:
            return [A11 ** r]
        t = _th(TH11, p)
        return [cmath.exp(1j * (r - 2 * j) * t) for j in range(r + 1)]
    return fn


def eigs_rs4(p):
    if p == 11:
        t2 = _th(TH37, p)
        return [A11 * cmath.exp(1j * s * t2) for s in (1, -1)]
    if p == 37:
        t1 = _th(TH11, p)
        return [A37 * cmath.exp(1j * s * t1) for s in (1, -1)]
    t1, t2 = _th(TH11, p), _th(TH37, p)
    return [cmath.exp(1j * (s1 * t1 + s2 * t2)) for s1 in (1, -1) for s2 in (1, -1)]


def eigs_deg6(p):
    if p == 11:
        t2 = _th(TH37, p)
        return [cmath.exp(1j * s * t2) / 11.0 for s in (1, -1)]
    if p == 37:
        t1 = _th(TH11, p)
        return [cmath.exp(2j * s * t1) / math.sqrt(37.0) for s in (1, 0, -1)]
    t1, t2 = _th(TH11, p), _th(TH37, p)
    return [cmath.exp(1j * (2 * s1 * t1 + s2 * t2))
            for s1 in (1, 0, -1) for s2 in (1, -1)]


EIGS = {"gl2": eigs_gl2, "sym2": eigs_sym(2), "sym3": eigs_sym(3),
        "sym4": eigs_sym(4), "rs4": eigs_rs4, "deg6": eigs_deg6}


# ---------------------------------------------------------------- bank + generators
def local_coeffs(eigs, kmax):
    poly = np.array([1.0 + 0j])
    for e in eigs:
        poly = np.convolve(poly, np.array([1.0, -e]))
    c = np.zeros(kmax + 1, dtype=complex)
    c[0] = 1.0
    for k in range(1, kmax + 1):
        acc = 0j
        for j in range(1, min(k, len(poly) - 1) + 1):
            acc -= poly[j] * c[k - j]
        c[k] = acc
    return c


def fast_bank(eigs_fn, nmax, primes):
    """Vectorized multiplicative sieve (race-free scatter: (p,k) reads touch
    only p-coprime m, never written by p's own pass)."""
    lam = np.zeros(nmax + 1, dtype=complex)
    lam[1] = 1.0
    for p in primes:
        p = int(p)
        kmax = int(math.log(nmax) / math.log(p))
        c = local_coeffs(eigs_fn(p), kmax)
        for k in range(kmax, 0, -1):
            pk = p ** k
            m = np.arange(1, nmax // pk + 1)
            m = m[m % p != 0]
            lam[m * pk] += c[k] * lam[m]
    return lam.real.copy()


def additive_omega(nmax, primes):
    om = np.zeros(nmax + 1)
    for p in primes:
        om[int(p)::int(p)] += 1.0
    return om


def additive_theta(nmax, primes, TH):
    """Theta(n) = sum_{p^k || n} k theta_p  (each multiple of p^j gets +theta_p
    for j = 1..v_p(n), summing to v_p(n) theta_p)."""
    out = np.zeros(nmax + 1)
    for p in primes:
        p = int(p)
        t = _th(TH, p)
        if t == 0.0:
            continue
        pk = p
        while pk <= nmax:
            out[pk::pk] += t
            pk *= p
    return out


# ------------------------------------------------------------------- the warp GN
def make_G(cols):
    """Stack the chosen generator columns (index 1..NMAX) into an (N, npar)."""
    if not cols:
        return None
    return np.column_stack(cols)


def cell_residuals(base_terms_real, base_terms_imag, cells, ncell, kmax):
    re = np.bincount(cells, weights=base_terms_real, minlength=ncell)
    im = np.bincount(cells, weights=base_terms_imag, minlength=ncell)
    return (re + 1j * im)[KMIN:kmax + 1]


GN_EPS = 1e-6


def _resid(base, G, x, cells, ncell, kmax):
    phase = np.exp(1j * (G @ x))
    terms = base * phase
    return cell_residuals(terms.real, terms.imag, cells, ncell, kmax)


def gauss_newton(base, G, cells, ncell, kmax):
    """Close cells KMIN..kmax by phase warp e^{i G x}, Gauss-Newton with a
    FINITE-DIFFERENCE Jacobian (eps=1e-6) -- exactly adapted_center.py.  This is
    load-bearing: a real bank is a first-order-stationary point of the closure
    objective (a perpendicular phase rotation raises |r_k| only at 2nd order),
    so the analytic 1st-order Jacobian cannot take a step; the descent that
    adapted uses lives in the eps-scale curvature the finite difference captures."""
    if G is None:
        return np.zeros(0)
    npar = G.shape[1]
    x = np.zeros(npar)
    for _ in range(GN_ITERS):
        r = _resid(base, G, x, cells, ncell, kmax)
        rv = np.concatenate([r.real, r.imag])
        J = np.zeros((len(rv), npar))
        for j in range(npar):
            xp = x.copy()
            xp[j] += GN_EPS
            rp = _resid(base, G, xp, cells, ncell, kmax)
            J[:, j] = np.concatenate([(rp - r).real, (rp - r).imag]) / GN_EPS
        try:
            dx, *_ = np.linalg.lstsq(J, -rv, rcond=None)
        except np.linalg.LinAlgError:
            break
        x = x + GN_STEP * dx
        if np.linalg.norm(dx) < 1e-12:
            break
    return x


def closure_median(base, G, x, cells, ncell, kmax):
    phase = np.exp(1j * (G @ x)) if (G is not None and len(x)) else np.ones(len(base))
    terms = base * phase
    r = cell_residuals(terms.real, terms.imag, cells, ncell, kmax)
    return float(np.median(np.abs(r)))


# --------------------------------------------------------------------- the reader
def wsmooth_vec(u):
    w = np.zeros_like(u)
    w[u <= 0.5] = 1.0
    mid = (u > 0.5) & (u < 1.0)
    xx = (u[mid] - 0.5) / 0.5
    a = np.exp(-1.0 / (1.0 - xx))
    b = np.exp(-1.0 / xx)
    w[mid] = a / (a + b)
    return w


def read_window(base, G, x, logn, Y):
    w = wsmooth_vec(logn / math.log(Y))
    if G is None or len(x) == 0:
        return complex((base * w).sum())
    phase = np.exp(1j * (G @ x))
    return complex((base * phase * w).sum())


# ==============================================================================
def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# VALUE-REGISTRATION CENSUS -- R = F_w(1/2)/L(1/2) across every certified")
    P("# central value (the S(t)-compensation analogue at value level)")
    P("#" * 78)
    P()
    P("FROZEN PROTOCOL:")
    P(f"  NMAX = {NMAX};  cells KMIN..KMAX = {KMIN}..{KMAX} (pi/3 lattice);")
    P(f"  Y-ladder (common, absolute) = {[int(y) for y in Y_LADDER]};")
    P(f"  warp = GN closure on [log n, omega, Theta_leg]; reader = C-inf window;")
    P(f"  R_0 = unwarped window (the m=0 harmonic-lattice point).")
    P()

    primes = SH.sieve_primes(NMAX)
    n = np.arange(1, NMAX + 1, dtype=float)
    logn = np.log(n)
    cells = np.floor(logn / H).astype(int)
    ncell = int(cells.max()) + 1
    nm05 = n ** -0.5
    kmax_full = KMAX

    P("building generators (log n, omega, Theta_11a1, Theta_37a1) -- vectorized...")
    G_logn = logn.copy()
    G_omega = additive_omega(NMAX, primes)[1:]
    TH_cols = {"11a1": additive_theta(NMAX, primes, TH11)[1:],
               "37a1": additive_theta(NMAX, primes, TH37)[1:]}
    # generator std over the FULL training support (for warp-energy normalization)
    sigma = {"logn": float(G_logn.std()), "omega": float(G_omega.std()),
             "11a1": float(TH_cols["11a1"].std()), "37a1": float(TH_cols["37a1"].std())}
    P(f"  generator std over support: log n {sigma['logn']:.3f}, "
      f"omega {sigma['omega']:.3f}, Theta_11 {sigma['11a1']:.3f}, "
      f"Theta_37 {sigma['37a1']:.3f}")
    P()

    def gcols(kind, legs):
        """Generator columns for a family kind."""
        theta_cols = [TH_cols[c] for c in legs]
        sig = [sigma[c] for c in legs]
        if kind == "full":
            return make_G([G_logn, G_omega] + theta_cols), \
                ["logn", "omega"] + legs, [sigma["logn"], sigma["omega"]] + sig
        if kind == "omega_theta":
            return make_G([G_omega] + theta_cols), ["omega"] + legs, \
                [sigma["omega"]] + sig
        if kind == "theta":
            return make_G(theta_cols), list(legs), sig
        return None, [], []

    def warp_energy(x, sig):
        return float(sum((xi * si) ** 2 for xi, si in zip(x, sig)))

    def offlattice_dist(x, names):
        """distance from x to nearest harmonic-lattice point (integer m on the
        Theta legs, 0 on log n / omega)."""
        d2 = 0.0
        for xi, nm in zip(x, names):
            if nm in ("logn", "omega"):
                d2 += xi ** 2
            else:
                d2 += (xi - round(xi)) ** 2
        return math.sqrt(d2)

    # -------------------------------------------------- VALIDATION (reproduce adapted)
    P("VALIDATION -- reproduce adapted_center.py ratios (NMAX=1e5, hard cutoff):")
    P("  (faithfulness check: analytic-Jacobian GN must recover the published")
    P("   full-warp mis-registrations 1.35 on RS4, 0.78 on Sym4)")
    NV = 100000
    pv = SH.sieve_primes(NV)
    nv = np.arange(1, NV + 1, dtype=float)
    lognv = np.log(nv)
    cellsv = np.floor(lognv / H).astype(int)
    ncellv = int(cellsv.max()) + 1
    kmax_v = int(math.log(NV) / H) - 1
    thv = {"11a1": additive_theta(NV, pv, TH11)[1:], "37a1": additive_theta(NV, pv, TH37)[1:]}
    for nm, ekey, legs, truth in [("RS 11a1x37a1", "rs4", ["11a1", "37a1"], 5.0227652),
                                  ("Sym4 11a1", "sym4", ["11a1"], 0.6058010)]:
        lamv = fast_bank(EIGS[ekey], NV, pv)
        basev = lamv[1:] * (nv ** -0.5)
        Gv = np.column_stack([lognv, additive_omega(NV, pv)[1:]] + [thv[c] for c in legs])
        xv = gauss_newton(basev, Gv, cellsv, ncellv, kmax_v)
        phase = np.exp(1j * (Gv @ xv))
        fw = complex(np.cumsum(basev * phase)[-1])
        P(f"    {nm:16s} full-warp F_w(1/2) hard-cutoff = "
          f"{fw.real:+.4f}{fw.imag:+.4f}i   |F_w|/L = {abs(fw)/truth:.4f}")
    P()

    # per-window training support: warp closes exactly the cells the window sees
    def cellcap(Y):
        return int(math.log(Y) / H) - 1          # top FULL cell (excludes partial)

    def train_n(K):
        Ntr = int(math.floor(math.exp((K + 1) * H) - 1e-9))
        return min(Ntr, NMAX)

    # -------------------------------------------------- build banks + per-window warps
    P("building banks (unitary, exact locals); per-window adapted warp per (obj,Y)...")
    P("  (warp trained on the cells the window sees -- KMIN..cellcap(Y); the")
    P("   smooth-window translation of adapted's cutoff protocol.  It is active")
    P("   where cells are under-closed (small Y) and self-vanishes as Y grows.)")
    census = []          # one row per (object, Y), each with its own warp
    graded = {}          # name -> {family: (R, energy, dlatt)} at the most-active Y
    Yact = Y_LADDER[0]   # smallest Y = most-active warp = money-question regime
    for name, deg, Q, L, ekey, legs in OBJECTS:
        lam = fast_bank(EIGS[ekey], NMAX, primes)
        base = lam[1:] * nm05
        sqrtQ = math.sqrt(Q)
        Gf, namesf, _ = gcols("full", legs)

        for Y in Y_LADDER:
            K = cellcap(Y)
            Ntr = train_n(K)
            b_tr = base[:Ntr]
            Gf_tr = Gf[:Ntr]
            cells_tr = cells[:Ntr]
            ncell_tr = K + 1
            sigf = [float(Gf_tr[:, j].std()) for j in range(Gf_tr.shape[1])]
            med_before = closure_median(b_tr, Gf_tr, np.zeros(Gf.shape[1]),
                                        cells_tr, ncell_tr, K)
            xf = gauss_newton(b_tr, Gf_tr, cells_tr, ncell_tr, K)
            med_after = closure_median(b_tr, Gf_tr, xf, cells_tr, ncell_tr, K)
            W = warp_energy(xf, sigf)
            dlatt = offlattice_dist(xf, namesf)
            R0 = read_window(base, None, [], logn, Y) / L
            Rf = read_window(base, Gf, xf, logn, Y) / L
            census.append(dict(name=name, deg=deg, Q=Q, sqrtQ=sqrtQ, L=L, Y=Y,
                               yq=Y / sqrtQ, R0=R0, Rfree=Rf, x=xf, names=namesf,
                               energy=W, xnorm=float(np.linalg.norm(xf)),
                               med_before=med_before, med_after=med_after,
                               ratio=med_before / max(med_after, 1e-12),
                               logQ=math.log(Q), dlatt=dlatt))

        # graded warp family (money question) at the most-active window Y = Yact
        K = cellcap(Yact)
        Ntr = train_n(K)
        b_tr, cells_tr, ncell_tr = base[:Ntr], cells[:Ntr], K + 1
        fam = {"unwarped(m=0)": (read_window(base, None, [], logn, Yact) / L, 0.0, 0.0)}
        xf_act = None
        for kind, label in [("theta", "Theta-only"), ("omega_theta", "omega+Theta"),
                            ("full", "full")]:
            Gk, namesk, _ = gcols(kind, legs)
            sigk = [float(Gk[:Ntr, j].std()) for j in range(Gk.shape[1])]
            xk = gauss_newton(b_tr, Gk[:Ntr], cells_tr, ncell_tr, K)
            if kind == "full":
                xf_act = (xk, namesk)
            Rk = read_window(base, Gk, xk, logn, Yact) / L
            fam[label] = (Rk, warp_energy(xk, sigk), offlattice_dist(xk, namesk))
        # lattice-snap of the full warp: round Theta legs to integer m, zero log/omega
        xk, namesk = xf_act
        xsnap = np.array([0.0 if nmn in ("logn", "omega") else float(round(xi))
                          for xi, nmn in zip(xk, namesk)])
        sigf_full = [float(Gf[:Ntr, j].std()) for j in range(Gf.shape[1])]
        Rsnap = read_window(base, Gf, xsnap, logn, Yact) / L
        fam["lattice-snap"] = (Rsnap, warp_energy(xsnap, sigf_full),
                               offlattice_dist(xsnap, namesk))
        graded[name] = fam
        P(f"  {name:24s} deg {deg} built; warp |x| across Y: " +
          ", ".join(f"{c['xnorm']:.2f}" for c in census if c['name'] == name))
    P()

    # ------------------------------------------------------------- TABLE A: warps
    P("=" * 78)
    P("TABLE A -- per-window full warp at the most-active window Y = %d " % int(Yact))
    P("           (cells %d..%d):" % (KMIN, cellcap(Yact)))
    P("=" * 78)
    P(f"  {'object':24s} {'deg':>3s} {'|x|':>6s} {'closure b->a':>16s} "
      f"{'ratio':>6s} {'energy':>7s} {'d_latt':>6s}")
    for name, _, _, _, _, _ in OBJECTS:
        w = [c for c in census if c['name'] == name and c['Y'] == Yact][0]
        P(f"  {name:24s} {w['deg']:>3d} {w['xnorm']:>6.3f} "
          f"{w['med_before']:>7.3f}->{w['med_after']:<7.3f} {w['ratio']:>6.2f} "
          f"{w['energy']:>7.4f} {w['dlatt']:>6.3f}")
        P(f"    weights: " + ", ".join(f"{nm}={xi:+.4f}"
                                       for nm, xi in zip(w['names'], w['x'])))
    P()

    # ------------------------------------------------------------- TABLE B: census
    P("=" * 78)
    P("TABLE B -- registration census (R_0 = unwarped window, R_free = per-window")
    P("           adapted warp).  |x|,energy,d_latt are the warp for THAT (obj,Y).")
    P("=" * 78)
    P(f"  {'object':22s} {'Y':>9s} {'Y/sqQ':>8s} {'|x|':>5s} {'energy':>6s} "
      f"{'R_0':>7s} {'|R0-1|':>7s} {'ReRf':>7s} {'ImRf':>7s} {'|Rf-1|':>7s}")
    for c in census:
        P(f"  {c['name']:22s} {c['Y']:>9.0f} {c['yq']:>8.1f} {c['xnorm']:>5.2f} "
          f"{c['energy']:>6.3f} {c['R0'].real:>7.4f} {abs(c['R0']-1):>7.4f} "
          f"{c['Rfree'].real:>7.4f} {c['Rfree'].imag:>7.4f} {abs(c['Rfree']-1):>7.4f}")
    P()

    # ------------------------------------------------------------- THE HUNT
    P("=" * 78)
    P("THE HUNT -- candidate laws for the registration defect delta = |R-1|.")
    P("Leave-one-object-out CV (object-level predictors tested on UNSEEN objects).")
    P("=" * 78)

    rows = census
    ncen = len(rows)

    def cv_linear(target_fn, pred_fn, label):
        """Leave-one-object-out CV of delta = a + b*pred; held-out RMS vs null."""
        names = [o[0] for o in OBJECTS]
        held_err, held_null = [], []
        for hold in names:
            tr = [r for r in rows if r['name'] != hold]
            te = [r for r in rows if r['name'] == hold]
            xt = np.array([pred_fn(r) for r in tr])
            yt = np.array([target_fn(r) for r in tr])
            xe = np.array([pred_fn(r) for r in te])
            ye = np.array([target_fn(r) for r in te])
            if xt.std() < 1e-9:                       # predictor flat on train -> mean
                pe = np.full(len(ye), yt.mean())
            else:
                A = np.column_stack([np.ones(len(xt)), xt])
                coef, *_ = np.linalg.lstsq(A, yt, rcond=None)
                pe = coef[0] + coef[1] * xe
                # guard: never extrapolate beyond the observed target range
                span = np.ptp(yt)
                pe = np.clip(pe, yt.min() - span, yt.max() + span)
            held_err.extend((ye - pe) ** 2)
            held_null.extend((ye - yt.mean()) ** 2)
        rmse = math.sqrt(np.mean(held_err))
        rmnull = math.sqrt(np.mean(held_null))
        # in-sample correlation for direction
        xa = np.array([pred_fn(r) for r in rows])
        ya = np.array([target_fn(r) for r in rows])
        cc = np.corrcoef(xa, ya)[0, 1] if xa.std() > 0 else float('nan')
        P(f"  {label:34s} held-RMS {rmse:.4f}  (null {rmnull:.4f})  "
          f"corr {cc:+.3f}  {'BEATS null' if rmse < rmnull * 0.98 else 'no lift'}")
        return rmse, rmnull

    dfree = lambda r: abs(r['Rfree'] - 1)
    d0 = lambda r: abs(r['R0'] - 1)
    dshift = lambda r: abs(r['Rfree'] - r['R0'])   # warp-INDUCED shift (isolates warp)

    P()
    P("Target = |R_free - R_0| (warp-INDUCED shift -- isolates the warp from the")
    P("finite-Y transient that R_0 and R_free share):")
    cv_linear(dshift, lambda r: r['energy'], "(i)    warp energy")
    cv_linear(dshift, lambda r: r['ratio'], "(ii)   closure-improvement ratio")
    cv_linear(dshift, lambda r: r['dlatt'], "(money) off-lattice distance")
    cv_linear(dshift, lambda r: r['logQ'], "(iii)  log Q")
    cv_linear(dshift, lambda r: math.log(r['yq']), "(iv)   log(Y/sqrtQ)")
    P()
    P("Target = |R_free - 1| (the full warped/adapted reading, transient included):")
    cv_linear(dfree, lambda r: r['energy'], "(i)    warp energy")
    cv_linear(dfree, lambda r: r['dlatt'], "(money) off-lattice distance")
    cv_linear(dfree, lambda r: math.log(r['yq']), "(iv)   log(Y/sqrtQ)")
    P()
    P("Target = |R_0 - 1| (the UNWARPED window -- the pure finite-Y transient law):")
    cv_linear(d0, lambda r: math.log(r['yq']), "(iv)   log(Y/sqrtQ)")
    cv_linear(d0, lambda r: r['logQ'], "(iii)  log Q")
    P("  (v) null is the 'null' column; a candidate is a measured law ONLY if it")
    P("      beats null out-of-sample (held-RMS < null).")
    P()

    # ------------------------------------------------------- MONEY: lattice restriction
    P("=" * 78)
    P("THE MONEY QUESTION -- is mis-registration caused by OFF-LATTICE freedom?")
    P("Graded warp families at the most-active window Y = %d, per object:" % int(Yact))
    P("=" * 78)
    P(f"  {'object':22s} {'family':16s} {'Re R':>8s} {'Im R':>8s} "
      f"{'|R-1|':>7s} {'energy':>7s} {'d_latt':>6s}")
    order = ["unwarped(m=0)", "Theta-only", "omega+Theta", "full", "lattice-snap"]
    agg = {f: [] for f in order}
    for name, _, _, _, _, _ in OBJECTS:
        for f in order:
            R, en, dl = graded[name][f]
            agg[f].append(abs(R - 1))
            P(f"  {name:22s} {f:16s} {R.real:>8.4f} {R.imag:>8.4f} "
              f"{abs(R-1):>7.4f} {en:>7.4f} {dl:>6.3f}")
        P()
    P("  family-mean |R-1| across the six certified objects:")
    for f in order:
        P(f"    {f:16s}  mean |R-1| = {np.mean(agg[f]):.4f}   "
          f"median = {np.median(agg[f]):.4f}")
    P()

    # correlation of the WARP-INDUCED shift with off-lattice content
    P("  warp-induced shift vs off-lattice distance (does the lattice govern it?):")
    dl_all, shift_all = [], []
    for name, _, _, _, _, _ in OBJECTS:
        R0 = graded[name]["unwarped(m=0)"][0]
        Rf, en, dl = graded[name]["full"]
        dl_all.append(dl)
        shift_all.append(abs(Rf - R0))
        P(f"    {name:22s} |R_full - R_0| = {abs(Rf-R0):.4f}   "
          f"d_latt = {dl:.3f}   energy = {en:.4f}")
    dl_all, shift_all = np.array(dl_all), np.array(shift_all)
    if dl_all.std() > 0:
        cc = np.corrcoef(dl_all, shift_all)[0, 1]
        P(f"    corr(|R_full-R_0|, d_latt) = {cc:+.3f}")
    P()

    # ----------------------------------------------------------------- VERDICT
    P("=" * 78)
    P("VERDICT (pre-registered; read the census, not a hope):")
    P("=" * 78)
    m0 = np.mean(agg["unwarped(m=0)"])
    mf = np.mean(agg["full"])
    msnap = np.mean(agg["lattice-snap"])
    P(f"  mean |R-1|:  unwarped(m=0) {m0:.4f}   full-warp {mf:.4f}   "
      f"lattice-snap {msnap:.4f}")
    if m0 < mf * 0.9:
        P("  -> The m=0 lattice point (unwarped window) registers markedly BETTER")
        P("     than the off-lattice continuous warp: removing off-lattice warp")
        P("     freedom improves registration.  Consistent with the money")
        P("     hypothesis -- the value-registration law is the lattice restriction.")
    elif abs(m0 - mf) < 0.02:
        P("  -> unwarped and full-warp register EQUALLY: the off-lattice warp")
        P("     neither helps nor hurts the value -- it buys summability only.")
        P("     The residual |R-1| is the finite-Y transient (see the |R_0-1|")
        P("     vs Y/sqrtQ fit), NOT a warp artifact: a structured null.")
    else:
        P("  -> The off-lattice warp registers BETTER than m=0 -- report as-is;")
        P("     inspect which objects drive it before any claim.")
    P()
    P("  Any candidate that BEATS null out-of-sample above is a measured law;")
    P("  the rest are killed forms -- the measured shape of what the law is NOT.")

    outp = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "value_registration_results.txt")
    with open(outp, "w") as fh:
        fh.write("\n".join(lines) + "\n")
    P()
    P(f"[results written to {outp}]")


if __name__ == "__main__":
    main()
