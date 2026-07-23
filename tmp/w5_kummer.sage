# W5: the Kummer specimen — genus-4 (C, eps) breaking the structural
# obstructions (trinomial => thetanull; bielliptic => iota-corank).
# C: u^3 = f(x,y), f in L(3O) with x-dependence, 3 simple branch zeros off
# the fibers; C~: t^3 = y.  Loop over candidates until the canonical quadric
# has rank 4, then measure the RIGIDITY RANK (27 = surjective => generic
# rigidity of the AP-threefold, certified forever by semicontinuity).

p = 7
F = GF(p)
R2.<X, Y> = PolynomialRing(F)
G = Y^2 + 2*X*Y + Y - X^3
K6 = GF(p^6, 'w')
ZETA = K6(F(2))
NTRUNC = 18
S.<s> = LaurentSeriesRing(K6, default_prec=NTRUNC)
RX.<xx> = PolynomialRing(F)
P1.<z> = PolynomialRing(K6)
import random
random.seed(int(2026721))


def Dop(f):
    return (2*Y + 2*X + 1)*f.derivative(X) + (3*X^2 - 2*Y)*f.derivative(Y)


CANDIDATES = []
for _ in range(400):
    c0, c1, c2 = [F(random.randrange(p)) for _ in range(3)]
    if c2 == 0 or c1 == 0:
        continue
    fp = c0 + c1*X + c2*Y
    if fp(0, 0) == 0 or fp(0, -1) == 0 or fp in CANDIDATES:
        continue
    res = fp.resultant(G, Y)
    resx = RX(res(xx, 0))
    if resx == 0 or not resx.is_squarefree():
        continue
    dh = Dop(fp)
    ok = True
    nz = 0
    for (pf, _) in resx.factor():
        if pf.degree() == 0:
            continue
        d = pf.degree()
        Kd = GF(p^d, 'a') if d > 1 else F
        x0 = pf.roots(Kd)[0][0]
        RY.<yy> = PolynomialRing(Kd)
        for (y0, _) in RY(G(x0, yy)).roots():
            if fp(x0, y0) == 0:
                nz += d
                if x0 == 0 or dh(x0, y0) == 0:
                    ok = False
    if ok and nz == 3:
        CANDIDATES.append(fp)
print(f"candidates: {len(CANDIDATES)}", flush=True)


def e0_series(pl):
    if pl == 'O':
        xs = s^-2
        for _ in range(NTRUNC + 4):
            xs = s^-2 + 2*s^-1 + 1/(xs*s)
        return xs, xs/s
    x0, y0 = pl
    xs = x0 + s
    ys = y0 + 0*s
    for _ in range(NTRUNC + 4):
        fy = ys^2 + 2*xs*ys + ys - xs^3
        ys = ys - fy/(2*ys + 2*xs + 1)
    return xs, ys


def cover_places(fpoly, pl):
    xs, ys = e0_series(pl)
    fser = fpoly(xs, ys)
    fv = fser.valuation()
    assert fv % 3 == 0
    ur = (z^3 - fser.coefficients()[0]).roots()
    if not ur:
        return None
    u0 = ur[0][0] * s^(fv // 3)
    for _ in range(NTRUNC + 4):
        u0 = u0 - (u0^3 - fser)/(3*u0^2)
    yv = ys.valuation()
    tr = (z^3 - ys.coefficients()[0]).roots()
    if not tr:
        return None
    t0 = tr[0][0] * s^(yv // 3)
    for _ in range(NTRUNC + 4):
        t0 = t0 - (t0^3 - ys)/(3*t0^2)
    return [(xs, ys, ZETA^ku * u0, ZETA^kt * t0)
            for ku in range(3) for kt in range(3)]


POOL = [(pp, q, i, j) for pp in range(-2, 4) for q in (0, 1)
        for i in (0, 1, 2) for j in (0, 1, 2)]
QPOOL = [(pp, q, i, j) for pp in range(-4, 7) for q in (0, 1)
         for i in (0, 1, 2) for j in (0, 1, 2)]


def kernel_basis(PLACES, subpool, upow):
    rows = []
    for pl, places in PLACES.items():
        for (xs, ys, u, t) in places:
            sers = [xs^pp * ys^q * u^i * t^j / u^upow
                    for (pp, q, i, j) in subpool]
            minv = min(ss.valuation() for ss in sers)
            for order in range(minv, 0):
                rows.append([ss[order] for ss in sers])
    return matrix(K6, rows).right_kernel().basis_matrix()


def evalp(vec, pt):
    x0, y0, u0, t0 = pt
    v = K6(0)
    for cc, (pp, q, i, j) in zip(vec, POOL):
        if cc:
            v += cc * x0^pp * y0^q * u0^i * t0^j
    return v


for fpoly in CANDIDATES:
    PL = {}
    bad = False
    for pl in ('O', (F(0), F(0)), (F(0), F(6))):
        cp = cover_places(fpoly, pl)
        if cp is None:
            bad = True
            break
        PL[pl] = cp
    if bad:
        continue
    OMEGA = []
    dims = []
    for j in range(3):
        sub = [mp for mp in POOL if mp[3] == j]
        K = kernel_basis(PL, sub, 2)
        dims.append(K.nrows())
        idx = [POOL.index(mp) for mp in sub]
        for r in range(K.nrows()):
            v = [K6(0)] * len(POOL)
            for c, ii in enumerate(idx):
                v[ii] = K[r][c]
            OMEGA.append(v)
    if dims != [4, 3, 3]:
        print(f"f = {fpoly}: gates {dims} — skip", flush=True)
        continue
    WITS = []
    while len(WITS) < 40:
        x0 = K6.random_element()
        if x0 == 0:
            continue
        yr = (z^2 + (2*x0+1)*z - x0^3).roots()
        if not yr:
            continue
        y0 = yr[random.randrange(len(yr))][0]
        if y0 == 0 or fpoly(x0, y0) == 0:
            continue
        ur = (z^3 - fpoly(x0, y0)).roots()
        if not ur:
            continue
        tr = (z^3 - y0).roots()
        if not tr:
            continue
        WITS.append((x0, y0, ur[0][0], tr[0][0]))
    CAN = OMEGA[:4]
    qrows = []
    for pt in WITS[:25]:
        zc = [evalp(vb, pt) for vb in CAN]
        qrows.append([zc[a]*zc[b] for a in range(4) for b in range(a, 4)])
    KQ = matrix(K6, qrows).right_kernel().basis_matrix()
    if KQ.nrows() != 1:
        print(f"f = {fpoly}: {KQ.nrows()} quadrics — skip", flush=True)
        continue
    qv = KQ.row(0)
    Smat = matrix(K6, 4, 4)
    idx = 0
    for a in range(4):
        for b in range(a, 4):
            if a == b:
                Smat[a, a] = qv[idx]
            else:
                Smat[a, b] += qv[idx]/2
                Smat[b, a] += qv[idx]/2
            idx += 1
    qr = Smat.rank()
    print(f"f = {fpoly}: quadric rank {qr}", flush=True)
    if qr != 4:
        continue
    print(f"SPECIMEN ACCEPTED: u^3 = {fpoly} (non-thetanull certified)",
          flush=True)
    KQ2 = kernel_basis(PL, QPOOL, 4)
    print(f"GATE: h^0(omega~^2) = {KQ2.nrows()} (expect 27)", flush=True)
    ANTI = OMEGA[4:]
    SG = [0]*4 + [1]*3 + [2]*3
    rowsM = []
    labels = []
    for a in range(10):
        for b in range(6):
            row = []
            for pt in WITS:
                x0, y0, u0, t0 = pt
                row.append(evalp(OMEGA[a], pt) * evalp(ANTI[b], pt) / u0^4)
            rowsM.append(row)
            labels.append((SG[a] + SG[4 + b]) % 3)
    rk = matrix(K6, rowsM).rank()
    print(f"RIGIDITY MULTIPLICATION RANK = {rk} of 27  "
          f"({'SURJECTIVE — GENERIC RIGIDITY CERTIFIED' if rk == 27 else 'corank ' + str(27 - rk)})",
          flush=True)
    for gt in range(3):
        sub = [rowsM[i] for i in range(60) if labels[i] == gt]
        print(f"  sigma-grade {gt}: rank {matrix(K6, sub).rank()} of 9",
              flush=True)
    break