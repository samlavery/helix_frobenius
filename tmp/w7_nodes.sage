# W7: the node-adjoint specimen family (eightfold tuned-pair playbook).
# C: (v - alpha)^2 (v + 2 alpha) + c^2 = 0  over E0, alpha in F7*,
# c = gamma*y + delta*x + eps in L(3O).  disc = -27 c^2 (4 alpha^3 + c^2):
# 3 NODES at {c = 0, v = alpha}, 6 simple branch points at {4a^3 + c^2 = 0}
# => R = 6, genus 4.  v has val -2 poles on the O-fiber only, but lies in
# L(2*O-fiber) = |omega|: the single-fiber pencil law does NOT fire.
# All fiber places unramified => level-1 engine; adjoint conditions at the
# node branches arise from the same regularity rows (F_v val 1 there).
# Chain: gates [4,3,3] (Sigma = 10 sanity) -> quadric rank 4 -> RIGIDITY.

p7 = 7
F = GF(p7)
R2.<X, Y> = PolynomialRing(F)
GE = Y^2 + 2*X*Y + Y - X^3
K6 = GF(p7^6, 'w')
ZETA = K6(F(2))
NTR = 26
S.<s> = LaurentSeriesRing(K6, default_prec=NTR)
P1.<z> = PolynomialRing(K6)
RX.<xx> = PolynomialRing(F)
import random
random.seed(int(72026))


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


def Dop(f):
    return (2*Y + 2*X + 1)*f.derivative(X) + (3*X^2 - 2*Y)*f.derivative(Y)


def hensel_cubic(pser, qser):
    """Roots of v^3 + pser v + qser with SIMPLE leading roots (level 1)."""
    roots = []
    vp = pser.valuation() if pser != 0 else 10**6
    vq = qser.valuation() if qser != 0 else 10**6
    for k in range(-6, 7):
        vals = [3*k, vp + k, vq]
        m = min(vals)
        if len([1 for t in vals if t == m]) < 2:
            continue
        Pz.<cc> = PolynomialRing(K6)
        poly = Pz(0)
        if 3*k == m:
            poly += cc^3
        if pser != 0 and vp + k == m:
            poly += pser.coefficients()[0]*cc
        if qser != 0 and vq == m:
            poly += qser.coefficients()[0]
        for (c0, mult) in poly.roots():
            if c0 == 0 or mult > 1:
                continue
            u = c0 * s^k
            for _ in range(NTR + 6):
                fu = u^3 + pser*u + qser
                if fu == 0:
                    break
                u = u - fu/(3*u^2 + pser)
            if any((u - r0) == 0 or (u - r0).valuation() >= NTR - 8
                   for r0 in roots):
                continue
            roots.append(u)
    return roots


def tower_places(alpha, cpoly):
    """All condition places of C~: fiber places (O/T/T') + node places.
    Returns list of (xs, ys, vbr, tbr) or None."""
    a3 = K6(alpha)^3
    out = []
    # fiber places
    for pl in ('O', (F(0), F(0)), (F(0), F(6))):
        if pl == 'O':
            xs, ys = e0_series_O()
        else:
            xs, ys = e0_series_at(K6(pl[0]), K6(pl[1]))
        cs = cpoly(xs, ys)
        pser = (-3*K6(alpha)^2) + 0*xs
        qser = 2*a3 + cs^2
        vr = hensel_cubic(pser, qser)
        if len(vr) != 3:
            return None
        yv = ys.valuation()
        if yv % 3 != 0:
            return None
        tr = (z^3 - ys.coefficients()[0]).roots()
        if not tr:
            return None
        t0 = tr[0][0] * s^(yv//3)
        for _ in range(NTR + 6):
            t0 = t0 - (t0^3 - ys)/(3*t0^2)
        for vb in vr:
            for kt in range(3):
                out.append((xs, ys, vb, ZETA^kt * t0))
    # node places: zeros of cpoly on E0, v-branches v = alpha + w, w = c*h
    res = cpoly.resultant(GE, Y)
    resx = RX(res(xx, 0))
    if resx == 0:
        return None
    ndeg = 0
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
            if cpoly(x0r, y0r) != 0:
                continue
            # embed into K6
            if d == 1:
                x0, y0 = K6(x0r), K6(y0r)
            else:
                emb = Kd.hom([Kd.gen().minimal_polynomial().roots(K6)[0][0]],
                             K6)
                x0, y0 = emb(x0r), emb(y0r)
            # all Frobenius conjugates are separate geometric node points
            for _ in range(d):
                xs, ys = e0_series_at(x0, y0)
                cs = cpoly(xs, ys)
                if cs.valuation() != 1:
                    return None      # non-simple c-zero: skip candidate
                # w^2 (w + 3 alpha) = -c^2 ; w = c*h, h^2 (c h + 3a) = -1
                sq = (z^2 + 1/(3*K6(alpha))).roots()
                if not sq:
                    return None
                for (h0, _) in sq:
                    h = h0 + 0*s
                    for _ in range(NTR + 6):
                        fh = h^2 * (cs*h + 3*K6(alpha)) + 1
                        dfh = 3*cs*h^2 + 6*K6(alpha)*h
                        h = h - fh/dfh
                    vb = K6(alpha) + cs*h
                    yv = ys.valuation()
                    tr = (z^3 - ys.coefficients()[0]).roots()
                    if not tr:
                        return None
                    t0 = tr[0][0] * s^(yv//3)
                    for _ in range(NTR + 6):
                        t0 = t0 - (t0^3 - ys)/(3*t0^2)
                    for kt in range(3):
                        out.append((xs, ys, vb, ZETA^kt * t0))
                ndeg += 1
                x0, y0 = x0^7, y0^7
    if ndeg != 3:
        return None
    return out


GPOOL = [(a, b, i, j) for a in range(-2, 5) for b in (0, 1)
         for i in (0, 1, 2) for j in (0, 1, 2)]
G2POOL = [(a, b, i, j) for a in range(-4, 8) for b in (0, 1)
          for i in (0, 1, 2) for j in (0, 1, 2)]


def kernel_grades(PLACES, alpha, pool, power):
    dims = []
    bases = []
    for j in range(3):
        sub = [mp for mp in pool if mp[3] == j]
        rows = []
        for (xs, ys, vb, tb) in PLACES:
            Fv = 3*vb^2 - 3*K6(alpha)^2
            w0 = xs.derivative() / (2*ys + 2*xs + 1)
            pref = (tb^j) * w0^power / Fv^power
            sers = [xs^a * ys^b * vb^i * pref for (a, b, i, jj) in sub]
            minv = min(ss.valuation() for ss in sers)
            for order in range(minv, 0):
                rows.append([ss[order] for ss in sers])
        Kb = matrix(K6, rows).right_kernel().basis_matrix()
        dims.append(Kb.nrows())
        bases.append((sub, Kb))
    return dims, bases


def evg(row, sub, pt):
    x0, y0, v0, t0 = pt
    val = K6(0)
    for cc, (a, b, i, jj) in zip(row, sub):
        if cc:
            val += cc * x0^a * y0^b * v0^i * t0^jj
    return val


tested = 0
for trial in range(200):
    alpha = F(random.randrange(1, 7))
    gam = F(random.randrange(1, 7))
    dlt = F(random.randrange(7))
    epsc = F(random.randrange(7))
    cpoly = gam*Y + dlt*X + epsc
    # basic exclusions: c nonzero at T, T'; 4a^3 + c^2 nonzero at fibers
    if cpoly(0, 0) == 0 or cpoly(0, -1) == 0:
        continue
    if 4*alpha^3 + cpoly(0, 0)^2 == 0 or 4*alpha^3 + cpoly(0, -1)^2 == 0:
        continue
    PLACES = tower_places(alpha, cpoly)
    if PLACES is None:
        continue
    tested += 1
    dims, bases = kernel_grades(PLACES, alpha, GPOOL, 1)
    if sum(dims) != 10:
        if tested <= 5:
            print(f"alpha={alpha} c={cpoly}: gates {dims} (Sigma "
                  f"{sum(dims)}) — reject", flush=True)
        continue
    if dims != [4, 3, 3]:
        print(f"alpha={alpha} c={cpoly}: gates {dims} — odd split", flush=True)
        continue
    print(f"alpha={alpha} c={cpoly}: gates [4,3,3] PASS", flush=True)
    # witnesses
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
        cv = cpoly(x0, y0)
        if cv == 0:
            continue
        vr = (z^3 - 3*K6(alpha)^2*z + 2*K6(alpha)^3 + cv^2).roots()
        if not vr:
            continue
        v0 = vr[random.randrange(len(vr))][0]
        if 3*v0^2 - 3*K6(alpha)^2 == 0:
            continue
        tr2 = (z^3 - y0).roots()
        if not tr2:
            continue
        WITS.append((x0, y0, v0, tr2[0][0]))
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
    print(f"  NON-THETANULL SPECIMEN FOUND — running rigidity", flush=True)
    dims2, _ = kernel_grades(PLACES, alpha, G2POOL, 2)
    print(f"  h^0(omega~^2) grades {dims2} (Sigma {sum(dims2)}, expect 27)",
          flush=True)
    rowsM = []
    labels = []
    for j1 in range(3):
        subA, KA = bases[j1]
        for j2 in (1, 2):
            subB, KB = bases[j2]
            for ra in range(KA.nrows()):
                for rb in range(KB.nrows()):
                    row = []
                    for pt in WITS:
                        x0, y0, v0, t0 = pt
                        Fv = 3*v0^2 - 3*K6(alpha)^2
                        row.append(evg(KA.row(ra), subA, pt) *
                                   evg(KB.row(rb), subB, pt) / Fv^2)
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
print(f"done; tested {tested}", flush=True)