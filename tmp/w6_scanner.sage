# W6: index-formula scanner for the two-fiber specimen.
# C: v^3 + p v + q = 0 over E0, coefficients p, q rational functions with
# poles in the {O, T, T'} fiber set, at least two fibers polar => the {1,v}
# single-fiber pencil (thetanull law) is broken.  Per candidate: branches at
# level-6 substitution with per-branch ramification detection, gates
# [4,3,3] (genus 4 + connected mu_3 tower), canonical quadric rank (want 4),
# then the RIGIDITY RANK (27 = generic rigidity certified).

p7 = 7
F = GF(p7)
R2.<X, Y> = PolynomialRing(F)
GE = Y^2 + 2*X*Y + Y - X^3
K6 = GF(p7^6, 'w')
ZETA = K6(F(2))
NTR = 30
S.<s> = LaurentSeriesRing(K6, default_prec=NTR)
P1.<z> = PolynomialRing(K6)
import random
random.seed(int(202607202))

# coefficient atoms: functions on E0 with fiber-set poles
# div(x) = T + T' - 2O ; div(y) = 3T - 3O ; div((y+1)/x) = poles T + O
ATOMS = {
    '1':    lambda xs, ys: xs^0,
    'x':    lambda xs, ys: xs,
    'y':    lambda xs, ys: ys,
    '1/x':  lambda xs, ys: 1/xs,
    'w':    lambda xs, ys: (ys+1)/xs,      # poles T + O
    'y/x':  lambda xs, ys: ys/xs,          # poles T' + O
}
ATOMPOLY = {
    '1': R2(1), 'x': X, 'y': Y, '1/x': None, 'w': None, 'y/x': None,
}


def e0_series(pl, prec):
    Sl.<ss> = LaurentSeriesRing(K6, default_prec=prec)
    if pl == 'O':
        xs = ss^-2
        for _ in range(prec + 4):
            xs = ss^-2 + 2*ss^-1 + 1/(xs*ss)
        return xs, xs/ss
    x0, y0 = pl
    xs = x0 + ss
    ys = y0 + 0*ss
    for _ in range(prec + 4):
        fy = ys^2 + 2*xs*ys + ys - xs^3
        ys = ys - fy/(2*ys + 2*xs + 1)
    return xs, ys


def eval_coeff(coeffs, xs, ys):
    v = 0*xs
    for (cf, at) in coeffs:
        v = v + K6(cf) * ATOMS[at](xs, ys)
    return v


def eval_coeff_pt(coeffs, x0, y0):
    v = K6(0)
    for (cf, at) in coeffs:
        if at == '1':
            v += K6(cf)
        elif at == 'x':
            v += K6(cf)*x0
        elif at == 'y':
            v += K6(cf)*y0
        elif at == '1/x':
            v += K6(cf)/x0
        elif at == 'w':
            v += K6(cf)*(y0+1)/x0
        elif at == 'y/x':
            v += K6(cf)*y0/x0
    return v


def cubic_roots_series(ps, qs, prec):
    """All Laurent-series roots of v^3 + ps*v + qs (level of ps/qs), via
    Newton slopes + Hensel; returns list of series."""
    roots = []
    vp = ps.valuation() if ps != 0 else 10**6
    vq = qs.valuation() if qs != 0 else 10**6
    cand_v = set()
    # slopes from Newton polygon of (3,0),(1,vp),(0,vq)
    for k in range(-12, 13):
        vals = [3*k, vp + k, vq]
        m = min(vals)
        if len([1 for t in vals if t == m]) >= 2:
            cand_v.add(k)
    for k in sorted(cand_v):
        Pz.<cc> = PolynomialRing(K6)
        poly = Pz(0)
        vals = [3*k, vp + k, vq]
        m = min(vals)
        if 3*k == m:
            poly += cc^3
        if ps != 0 and vp + k == m:
            poly += ps.coefficients()[0]*cc
        if qs != 0 and vq == m:
            poly += qs.coefficients()[0]
        for (c0, _) in poly.roots():
            if c0 == 0:
                continue
            u = c0 * s.parent()(ps.parent().gen())^k if False else c0 * ps.parent().gen()^k
            for _ in range(prec + 6):
                fu = u^3 + ps*u + qs
                if fu == 0:
                    break
                dfu = 3*u^2 + ps
                if dfu == 0:
                    break
                u = u - fu/dfu
            res = u^3 + ps*u + qs
            if res != 0 and res.valuation() < prec - 10:
                continue
            if any((u - r0) == 0 or (u - r0).valuation() >= prec - 12
                   for r0 in roots):
                continue
            roots.append(u)
    return roots


def branch_data(pcoef, qcoef, pl):
    """Level-6 branches over E0-place pl: returns list of
    (xs6, ys6, vbr, tbr, m) with m = 6/e the sigma-lattice, or None."""
    xs6, ys6 = e0_series(pl, NTR)
    xs6, ys6 = xs6.V(6), ys6.V(6)
    Sl = xs6.parent()
    ps = eval_coeff(pcoef, xs6, ys6)
    qs = eval_coeff(qcoef, xs6, ys6)
    vroots = cubic_roots_series(ps, qs, NTR*6 - 20)
    if len(vroots) != 3:
        return None
    # t: cube root of ys6 (one; others by zeta)
    yv = ys6.valuation()
    if yv % 3 != 0:
        return None
    tr = (z^3 - ys6.coefficients()[0]).roots()
    if not tr:
        return None
    t0 = tr[0][0] * Sl.gen()^(yv//3)
    for _ in range(40):
        t0 = t0 - (t0^3 - ys6)/(3*t0^2)
    out = []
    for vb in vroots:
        # detect lattice m = gcd of exponent support (with 6)
        expo = [e for e, c in enumerate([]) ] # placeholder
        supp = vb.exponents()
        m = 6
        for e in supp:
            m = gcd(m, e - supp[0]) if supp else 6
        m = gcd(m, 6)
        if m == 0:
            m = 6
        for kt in range(3):
            out.append((xs6, ys6, vb, ZETA^kt * t0, m))
    return out


GPOOL = [(a, b, i, j) for a in range(-2, 4) for b in (0, 1)
         for i in (0, 1, 2) for j in (0, 1, 2)]
G2POOL = [(a, b, i, j) for a in range(-4, 7) for b in (0, 1)
          for i in (0, 1, 2) for j in (0, 1, 2)]


def kernel_dims(BR, pcoef, pool, power):
    """Kernel of regularity for eta = (g t^j / F_v^power) * pi*omega0^power,
    per t-grade j; returns (dims, bases-over-pool)."""
    out_dims = []
    out_bases = []
    for j in range(3):
        sub = [mp for mp in pool if mp[3] == j]
        rows = []
        for pl, brs in BR.items():
            for (xs6, ys6, vb, tb, m) in brs:
                Fv = 3*vb^2 + eval_coeff(pcoef, xs6, ys6)
                w0 = xs6.derivative() / (2*ys6 + 2*xs6 + 1)
                pref = (tb^j) * w0^power / Fv^power
                sers = [xs6^a * ys6^b * vb^i * pref for (a, b, i, jj) in sub]
                minv = min(ss.valuation() for ss in sers)
                cutoff = power*(m - 1) - (m - 1) + (m - 1)  # = power*(m-1)
                for order in range(minv, power*(m-1)):
                    rows.append([ss[order] for ss in sers])
        M = matrix(K6, rows)
        Kb = M.right_kernel().basis_matrix()
        out_dims.append(Kb.nrows())
        out_bases.append((sub, Kb))
    return out_dims, out_bases


def run_candidate(pcoef, qcoef, verbose=False):
    BR = {}
    for pl in ('O', (F(0), F(0)), (F(0), F(6))):
        bd = branch_data(pcoef, qcoef, pl)
        if bd is None:
            return None
        BR[pl] = bd
    dims, bases = kernel_dims(BR, pcoef, GPOOL, 1)
    if verbose:
        print(f"    gates {dims}", flush=True)
    if dims != [4, 3, 3]:
        return ('gates', dims)
    # witnesses on C~
    WITS = []
    tries = 0
    while len(WITS) < 40 and tries < 4000:
        tries += 1
        x0 = K6.random_element()
        if x0 == 0:
            continue
        yr = (z^2 + (2*x0+1)*z - x0^3).roots()
        if not yr:
            continue
        y0 = yr[random.randrange(len(yr))][0]
        if y0 == 0:
            continue
        pv = eval_coeff_pt(pcoef, x0, y0)
        qv = eval_coeff_pt(qcoef, x0, y0)
        vr = (z^3 + pv*z + qv).roots()
        if not vr:
            continue
        v0 = vr[random.randrange(len(vr))][0]
        if 3*v0^2 + pv == 0:
            continue
        tr2 = (z^3 - y0).roots()
        if not tr2:
            continue
        WITS.append((x0, y0, v0, tr2[0][0]))
    if len(WITS) < 40:
        return ('wits', len(WITS))

    def evg(subKrow, sub, pt):
        x0, y0, v0, t0 = pt
        val = K6(0)
        for cc, (a, b, i, jj) in zip(subKrow, sub):
            if cc:
                val += cc * x0^a * y0^b * v0^i * t0^jj
        return val

    sub0, K0 = bases[0]
    qrows = []
    for pt in WITS[:25]:
        zc = [evg(K0.row(r), sub0, pt) for r in range(4)]
        qrows.append([zc[a]*zc[b] for a in range(4) for b in range(a, 4)])
    KQ = matrix(K6, qrows).right_kernel().basis_matrix()
    if KQ.nrows() != 1:
        return ('nquad', KQ.nrows())
    qv2 = KQ.row(0)
    Sm = matrix(K6, 4, 4)
    idx = 0
    for a in range(4):
        for b in range(a, 4):
            if a == b:
                Sm[a, a] = qv2[idx]
            else:
                Sm[a, b] += qv2[idx]/2
                Sm[b, a] += qv2[idx]/2
            idx += 1
    qr = Sm.rank()
    if qr != 4:
        return ('quadric', qr)
    # RIGIDITY
    dims2, _ = kernel_dims(BR, pcoef, G2POOL, 2)
    h0q = sum(dims2)
    rowsM = []
    for j1 in range(3):
        subA, KA = bases[j1]
        for j2 in (1, 2):
            subB, KB = bases[j2]
            for ra in range(KA.nrows()):
                for rb in range(KB.nrows()):
                    row = []
                    for pt in WITS:
                        x0, y0, v0, t0 = pt
                        pv = eval_coeff_pt(pcoef, x0, y0)
                        Fv = 3*v0^2 + pv
                        row.append(evg(KA.row(ra), subA, pt) *
                                   evg(KB.row(rb), subB, pt) / Fv^2)
                    rowsM.append(row)
    rk = matrix(K6, rowsM).rank()
    return ('HIT', qr, h0q, rk)


# --- candidate sweep: q with T'-structure (y+1)-vanishing kept, plus a
# two-fiber polar term in p or q
FAMS = []
for _ in range(60):
    pc = [(random.randrange(1, 7), 'x'),
          (random.randrange(7), '1'),
          (random.randrange(7), 'w')]
    qc = [(random.randrange(1, 7), 'y'), (random.randrange(1, 7), '1'),
          (random.randrange(7), 'x'), (random.randrange(7), '1/x')]
    FAMS.append((pc, qc))

hits = 0
diag = {}
nc = 0
for (pc, qc) in FAMS:
    nc += 1
    try:
        res = run_candidate(pc, qc)
    except (AssertionError, ZeroDivisionError, ValueError) as e:
        diag[type(e).__name__] = diag.get(type(e).__name__, 0) + 1
        continue
    if res is None:
        diag['branches'] = diag.get('branches', 0) + 1
        continue
    key = res[0] if res[0] != 'gates' else f"gates{res[1]}"
    diag[key] = diag.get(key, 0) + 1
    if nc <= 6:
        print(f"  cand {nc}: {res[:2]}", flush=True)
    if res[0] == 'HIT':
        print(f"p = {pc}", flush=True)
        print(f"q = {qc}", flush=True)
        print(f"  quadric rank 4; h^0(omega~^2) = {res[2]}; "
              f"RIGIDITY RANK = {res[3]} of 27", flush=True)
        if res[3] == 27:
            print("  *** SURJECTIVE — GENERIC RIGIDITY CERTIFIED ***",
                  flush=True)
            hits += 1
            break
    elif res[0] == 'gates' and res[1] != [4, 3, 3]:
        pass
print(f"sweep done; certified hits: {hits}; diagnostics: {diag}", flush=True)