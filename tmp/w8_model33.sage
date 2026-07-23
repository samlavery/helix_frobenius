# W8: the (3,3)-model specimen — tri-nodal bidegree-(3,3) curve in E0 x P^1
# with PRESCRIBED generic nodes (9 linear conditions on the 12 L(3O)-coeffs).
# Genus 7 - 3 = 4; omega = O(R) with R involving the generic node positions:
# NOT a fiber-class multiple => the master thetanull law cannot fire.
# Engine: monic depressed W-form (W-poles only over O, val -3); condition
# places = O/T/T' fibers + 3 real nodes + artifact nodes at a_3-zeros; the
# adjoint conditions arise automatically from 1/F_W's val at node branches.
# Chain: linear solve -> gates [4,3,3] -> quadric rank -> RIGIDITY RANK.

p7 = 7
F = GF(p7)
R2.<X, Y> = PolynomialRing(F)
GE = Y^2 + 2*X*Y + Y - X^3
K6 = GF(p7^6, 'w')
ZETA = K6(F(2))
NTR = 24
S.<s> = LaurentSeriesRing(K6, default_prec=NTR)
P1.<z> = PolynomialRing(K6)
RX.<xx> = PolynomialRing(F)
import random
random.seed(int(3372026))

Dx = 2*Y + 2*X + 1
Dy = 3*X^2 - 2*Y

# --- E0 rational points for node placement
E0RAT = [(F(x0), F(y0)) for x0 in F for y0 in F
         if x0 != 0 and y0 != 0 and (y0^2 + 2*x0*y0 + y0 - x0^3) == 0
         and y0 != -1]


def e0_series_at(x0, y0):
    xs = x0 + s
    ys = y0 + 0*s
    for _ in range(NTR + 4):
        fy = ys^2 + 2*xs*ys + ys - xs^3
        ys = ys - fy/(2*ys + 2*xs + 1)
    return xs, ys


def e0_series_O():
    xs = s^-2
    for _ in range(NTR + 4):
        xs = s^-2 + 2*s^-1 + 1/(xs*s)
    return xs, xs/s


def sqrt_series(f):
    v = f.valuation()
    if v % 2 != 0:
        return None
    rt = (z^2 - f.coefficients()[0]).roots()
    if not rt:
        return None
    g = rt[0][0] * s^(v//2)
    for _ in range(NTR + 6):
        g = g - (g^2 - f)/(2*g)
    return g


def cube_series(f):
    v = f.valuation()
    if v % 3 != 0:
        return None
    rt = (z^3 - f.coefficients()[0]).roots()
    if not rt:
        return None
    g = rt[0][0] * s^(v//3)
    for _ in range(NTR + 6):
        g = g - (g^3 - f)/(3*g^2)
    return g


def build_candidate():
    """Pick 3 nodes, solve the 9 linear conditions, return (a-coeffs, nodes)."""
    nodes = random.sample(E0RAT, 3)
    vvals = [F(random.randrange(1, 7)) for _ in range(3)]
    if len({pt[0] for pt in nodes}) < 3:
        return None
    rows = []
    # unknowns: (alpha_i, beta_i, gamma_i) for a_i = alpha + beta x + gamma y
    for ((x0, y0), v0) in zip(nodes, vvals):
        rF, rFv, rD = [], [], []
        dxv, dyv = Dx(x0, y0), Dy(x0, y0)
        for i in range(4):
            vi = v0^i
            vim = F(i)*v0^(i-1) if i >= 1 else F(0)
            rF += [vi, x0*vi, y0*vi]
            rFv += [vim, x0*vim, y0*vim]
            rD += [F(0), dxv*vi, dyv*vi]
        rows += [rF, rFv, rD]
    M = matrix(F, rows)
    Kb = M.right_kernel().basis_matrix()
    if Kb.nrows() < 1:
        return None
    coef = sum(F(random.randrange(7)) * Kb.row(r) for r in range(Kb.nrows()))
    A = [coef[3*i] + coef[3*i+1]*X + coef[3*i+2]*Y for i in range(4)]
    if A[3] == 0:
        return None
    return A, list(zip(nodes, vvals))


def PQ_of(A):
    a0, a1, a2, a3 = A
    P = a1*a3 - a2^2/F(3)
    Q = a0*a3^2 - a1*a2*a3/F(3) + 2*a2^3/F(27)
    return P, Q


def node_branches(Ppoly, Qpoly, x0, y0, W0):
    """Two branches of W^3 + P W + Q at a double root W0 over (x0,y0)."""
    xs, ys = e0_series_at(x0, y0)
    Ps, Qs = Ppoly(xs, ys), Qpoly(xs, ys)
    c1 = 3*W0^2 + Ps
    c0 = W0^3 + Ps*W0 + Qs
    if c0 == 0 or c1 == 0:
        return None
    if c0.valuation() < 2 or c1.valuation() < 1 or W0 == 0:
        return None
    outs = []
    for sgn in (1, -1):
        w = 0*s
        okb = False
        for _ in range(NTR + 8):
            disc = c1^2 - 12*W0*(c0 + w^3)
            r = sqrt_series(disc)
            if r is None:
                return None
            w2 = (-c1 + K6(sgn)*r)/(6*W0)
            if (w2 - w) == 0:
                okb = True
                w = w2
                break
            w = w2
        outs.append(W0 + w)
    if (outs[0] - outs[1]) == 0 or (outs[0]-outs[1]).valuation() > 2:
        return None
    return xs, ys, outs


def fiber_branches(Ppoly, Qpoly, pl):
    if pl == 'O':
        xs, ys = e0_series_O()
    else:
        xs, ys = e0_series_at(K6(pl[0]), K6(pl[1]))
    Ps, Qs = Ppoly(xs, ys), Qpoly(xs, ys)
    vq = Qs.valuation()
    branches = []
    if pl == 'O':
        if vq != -9:
            return None
        lead = z^3 + (Ps.coefficients()[0] if Ps.valuation() == -6 else 0)*z \
            + Qs.coefficients()[0]
        rts = lead.roots()
        if len(rts) != 3:
            return None
        for (c0, _) in rts:
            u = c0*s^-3
            for _ in range(NTR + 6):
                u = u - (u^3 + Ps*u + Qs)/(3*u^2 + Ps)
            branches.append(u)
    else:
        rts = (z^3 + Ps.coefficients()[0]*z + Qs.coefficients()[0]).roots() \
            if Ps.valuation() == 0 and vq == 0 else \
            (z^3 + (Ps[0])*z + (Qs[0])).roots()
        if len(rts) != 3:
            return None
        for (c0, _) in rts:
            u = c0 + 0*s
            for _ in range(NTR + 6):
                u = u - (u^3 + Ps*u + Qs)/(3*u^2 + Ps)
            branches.append(u)
    return xs, ys, branches


def all_places(A, NODES):
    Ppoly, Qpoly = PQ_of(A)
    a0, a1, a2, a3 = A
    PLACES = []
    for pl in ('O', (F(0), F(0)), (F(0), F(6))):
        fb = fiber_branches(Ppoly, Qpoly, pl)
        if fb is None:
            return None
        xs, ys, brs = fb
        ts = cube_series(ys)
        if ts is None:
            return None
        for vb in brs:
            for kt in range(3):
                PLACES.append((xs, ys, vb, ZETA^kt*ts))
    # real nodes
    for ((x0, y0), v0) in NODES:
        W0 = K6(a3(x0, y0))*K6(v0) + K6(a2(x0, y0))/3
        nb = node_branches(Ppoly, Qpoly, K6(x0), K6(y0), W0)
        if nb is None:
            return None
        xs, ys, outs = nb
        ts = cube_series(ys)
        if ts is None:
            return None
        for wb in outs:
            for kt in range(3):
                PLACES.append((xs, ys, wb, ZETA^kt*ts))
    # artifact nodes at a_3-zeros
    res = a3.resultant(GE, Y)
    resx = RX(res(xx, 0))
    if resx == 0:
        return None
    for (pf, _) in resx.factor():
        if pf.degree() == 0:
            continue
        d = pf.degree()
        if 6 % d != 0:
            return None
        Kd = GF(p7^d, 'a') if d > 1 else F
        x0r = pf.roots(Kd)[0][0]
        RY.<yy> = PolynomialRing(Kd)
        for (y0r, _) in RY(GE(x0r, yy)).roots():
            if a3(x0r, y0r) != 0:
                continue
            if d == 1:
                x0, y0 = K6(x0r), K6(y0r)
            else:
                emb = Kd.hom([Kd.gen().minimal_polynomial().roots(K6)[0][0]],
                             K6)
                x0, y0 = emb(x0r), emb(y0r)
            for _ in range(d):
                if x0 == 0 or y0 == 0:
                    return None
                W0 = K6(a2(x0, y0))/3
                if K6(a2(x0, y0)) == 0:
                    return None
                nb = node_branches(Ppoly, Qpoly, x0, y0, W0)
                if nb is None:
                    return None
                xs, ys, outs = nb
                ts = cube_series(ys)
                if ts is None:
                    return None
                for wb in outs:
                    for kt in range(3):
                        PLACES.append((xs, ys, wb, ZETA^kt*ts))
                x0, y0 = x0^7, y0^7
    return PLACES


GPOOL = [(a, b, i, j) for a in range(-2, 5) for b in (0, 1)
         for i in (0, 1, 2) for j in (0, 1, 2)]
G2POOL = [(a, b, i, j) for a in range(-4, 8) for b in (0, 1)
          for i in (0, 1, 2) for j in (0, 1, 2)]


def kernel_grades(PLACES, Ppoly, pool, power):
    dims, bases = [], []
    for j in range(3):
        sub = [mp for mp in pool if mp[3] == j]
        rows = []
        for (xs, ys, wb, tb) in PLACES:
            Fw = 3*wb^2 + Ppoly(xs, ys)
            w0 = xs.derivative() / (2*ys + 2*xs + 1)
            pref = (tb^j) * w0^power / Fw^power
            sers = [xs^a * ys^b * wb^i * pref for (a, b, i, jj) in sub]
            minv = min(ss.valuation() for ss in sers)
            for order in range(minv, 0):
                rows.append([ss[order] for ss in sers])
        Kb = matrix(K6, rows).right_kernel().basis_matrix()
        dims.append(Kb.nrows())
        bases.append((sub, Kb))
    return dims, bases


def evg(row, sub, pt):
    x0, y0, w0v, t0 = pt
    val = K6(0)
    for cc, (a, b, i, jj) in zip(row, sub):
        if cc:
            val += cc * x0^a * y0^b * w0v^i * t0^jj
    return val


found = 0
for trial in range(400):
    cand = build_candidate()
    if cand is None:
        continue
    A, NODES = cand
    Ppoly, Qpoly = PQ_of(A)
    PLACES = all_places(A, NODES)
    if PLACES is None:
        continue
    found += 1
    dims, bases = kernel_grades(PLACES, Ppoly, GPOOL, 1)
    if sum(dims) != 10:
        if found <= 6:
            print(f"cand {found}: gates {dims} Sigma {sum(dims)} — reject",
                  flush=True)
        continue
    if dims != [4, 3, 3]:
        print(f"cand {found}: gates {dims} — odd split", flush=True)
        continue
    print(f"cand {found}: gates [4,3,3] PASS  (nodes {NODES})", flush=True)
    # witnesses
    WITS = []
    tries = 0
    while len(WITS) < 40 and tries < 5000:
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
        Pv, Qv = Ppoly(x0, y0), Qpoly(x0, y0)
        wr = (z^3 + Pv*z + Qv).roots()
        if not wr:
            continue
        w0v = wr[random.randrange(len(wr))][0]
        if 3*w0v^2 + Pv == 0:
            continue
        tr2 = (z^3 - y0).roots()
        if not tr2:
            continue
        WITS.append((x0, y0, w0v, tr2[0][0]))
    if len(WITS) < 40:
        continue
    sub0, K0 = bases[0]
    qrows = []
    for pt in WITS[:25]:
        zc = [evg(K0.row(r), sub0, pt) for r in range(4)]
        qrows.append([zc[a]*zc[b] for a in range(4) for b in range(a, 4)])
    KQ = matrix(K6, qrows).right_kernel().basis_matrix()
    if KQ.nrows() != 1:
        print(f"  {KQ.nrows()} quadrics — skip", flush=True)
        continue
    qv = KQ.row(0)
    Sm = matrix(K6, 4, 4)
    idx = 0
    for a in range(4):
        for b in range(a, 4):
            if a == b:
                Sm[a, a] = qv[idx]
            else:
                Sm[a, b] += qv[idx]/2
                Sm[b, a] += qv[idx]/2
            idx += 1
    qr = Sm.rank()
    print(f"  quadric rank = {qr}", flush=True)
    if qr != 4:
        continue
    print(f"  *** NON-THETANULL (3,3)-SPECIMEN — running rigidity ***",
          flush=True)
    dims2, _ = kernel_grades(PLACES, Ppoly, G2POOL, 2)
    print(f"  h^0(omega~^2) grades {dims2} (Sigma {sum(dims2)}, expect 27)",
          flush=True)
    rowsM, labels = [], []
    for j1 in range(3):
        subA, KA = bases[j1]
        for j2 in (1, 2):
            subB, KB = bases[j2]
            for ra in range(KA.nrows()):
                for rb in range(KB.nrows()):
                    row = []
                    for pt in WITS:
                        x0, y0, w0v, t0 = pt
                        Fw = 3*w0v^2 + Ppoly(x0, y0)
                        row.append(evg(KA.row(ra), subA, pt) *
                                   evg(KB.row(rb), subB, pt) / Fw^2)
                    rowsM.append(row)
                    labels.append((j1 + j2) % 3)
    rk = matrix(K6, rowsM).rank()
    print(f"  RIGIDITY RANK = {rk} of 27  "
          f"({'*** SURJECTIVE — GENERIC RIGIDITY CERTIFIED ***' if rk == 27 else 'corank ' + str(27 - rk)})",
          flush=True)
    for gt in range(3):
        subr = [rowsM[i] for i in range(len(rowsM)) if labels[i] == gt]
        print(f"    sigma-grade {gt}: rank {matrix(K6, subr).rank()} of 9",
              flush=True)
    if rk == 27:
        break
print(f"done; viable candidates: {found}", flush=True)