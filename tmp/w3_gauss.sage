# W3/J2 layer 0: generic depth-one base point + the s=1 trick.
# Find eta = (u + l)/u * omega0 with 6 distinct SPLIT closed points and a
# rational lift W~; compute M = {eta in H^0(omega_C~): div eta >= W~} by
# evaluation rows; check dim M = 4 and rank pr(M) = 3 (W1 at a GENERIC
# depth-one point).  This is the tau = 0 layer of the Gauss probe; the
# dual-number tau-layer stacks on the same rows.

load('w2_specimen.sage')   # hpoly, PLACES, POOL, K6, gates 4/3/3, ZETA, F

R2b.<X, Y> = PolynomialRing(F)
Gc = Y^2 + 2*X*Y + Y - X^3
hp2 = -2*X^3 + X^2 - X*Y + 3*X + 1
RXb.<xx> = PolynomialRing(F)


def Dop(f):
    return (2*Y + 2*X + 1)*f.derivative(X) + (3*X^2 - 2*Y)*f.derivative(Y)


# --- the 10-dim omega-basis from the gates (per t-grade j), coefficient
# vectors over the j-graded subpools; assemble one global basis over POOL.
def gate_kernel(j):
    sub = [mp for mp in POOL if mp[3] == j]
    rows = []
    for pl, places in PLACES.items():
        for (xs, ys, u, t) in places:
            sers = [(xs^pp * ys^q * u^i * t^jj) / u for (pp, q, i, jj) in sub]
            minv = min(ss.valuation() for ss in sers)
            for order in range(minv, 0):
                rows.append([ss[order] for ss in sers])
    K = matrix(K6, rows).right_kernel().basis_matrix()
    # embed into full-POOL coordinates
    idx = [POOL.index(mp) for mp in sub]
    out = []
    for r in range(K.nrows()):
        v = [K6(0)] * len(POOL)
        for c, ii in enumerate(idx):
            v[ii] = K[r][c]
        out.append(v)
    return out


OMEGA_BASIS = []
for j in range(3):
    OMEGA_BASIS += gate_kernel(j)
print(f"omega-basis assembled: {len(OMEGA_BASIS)} (expect 10)", flush=True)


def is_cube(v, K):
    return v == 0 or v^((K.order() - 1) // 3) == 1


# --- find a clean generic eta: F = l^2 - h with 6 distinct closed points,
# all t-split, all simple, none at branch/fiber loci
import random
random.seed(int(3719))
base = None
for _ in range(4000):
    c1, c2, c3 = [F(random.randrange(7)) for _ in range(3)]
    l = c1 + c2*X + c3*Y
    Fq = l^2 - hp2
    res = Fq.resultant(Gc, Y)
    resx = RXb(res(xx, 0))
    if resx == 0 or not resx.is_squarefree():
        continue
    pts = []
    ok = True
    for (pfac, mfac) in resx.factor():
        if pfac.degree() == 0:
            continue
        d = pfac.degree()
        Kd = GF(7^d, 'a') if d > 1 else F
        x0 = pfac.roots(Kd)[0][0]
        RY.<yy> = PolynomialRing(Kd)
        got = False
        for (y0, _) in RY(Gc(x0, yy)).roots():
            if Fq(x0, y0) != 0:
                continue
            got = True
            if x0 == 0 or y0 == 0 or hp2(x0, y0) == 0 or Dop(Fq)(x0, y0) == 0:
                ok = False
                break
            if not is_cube(y0, Kd):
                ok = False
                break
            pts.append((d, x0, y0, Kd))
        if not ok:
            break
        if not got:
            ok = False   # y in quadratic ext: skip for cleanliness
            break
    if ok and sum(d for (d, _, _, _) in pts) == 6:
        base = (c1, c2, c3, l, pts)
        break
assert base is not None, "no clean generic eta found"
c1, c2, c3, l, pts = base
print(f"base eta: l = {l}; closed points degrees {[d for (d,_,_,_) in pts]}",
      flush=True)

# --- rational lift W~: at each closed point choose the t-preimage with
# t-value in the SAME residue field (all three are, since split: pick one
# Frobenius-coherently: for each closed pt take t0 = any cube root of y0 in
# K_d — a rational closed point of C~ of degree d).
LIFT = []
for (d, x0, y0, Kd) in pts:
    RT.<zz> = PolynomialRing(Kd)
    t0 = RT(zz^3 - y0).roots()[0][0]
    u0 = -l(x0, y0)
    LIFT.append((d, x0, y0, u0, t0, Kd))

# --- M-space: evaluation rows of the omega-basis at the 6 lifted points,
# with restriction of scalars to F_7 for d > 1
def evalpool(vec, x0, y0, u0, t0):
    v = 0
    for cc, (pp, q, i, j) in zip(vec, POOL):
        if cc:
            v += cc * x0^pp * y0^q * u0^i * t0^j
    return v


rows = []
for (d, x0, y0, u0, t0, Kd) in LIFT:
    # a degree-d closed point = its d Frobenius-conjugate geometric points:
    # one evaluation row per conjugate (all inside K6 since d | 6)
    assert 6 % d == 0
    if d == 1:
        cx, cy, cu, ct = K6(x0), K6(y0), K6(u0), K6(t0)
    else:
        emb = Kd.hom([Kd.gen().minimal_polynomial().roots(K6)[0][0]], K6)
        cx, cy, cu, ct = emb(x0), emb(y0), emb(u0), emb(t0)
    for i in range(d):
        rows.append([evalpool(vb, cx, cy, cu, ct) for vb in OMEGA_BASIS])
        cx, cy, cu, ct = cx^7, cy^7, cu^7, ct^7
M0 = matrix(K6, rows)
KM = M0.right_kernel().basis_matrix()
print(f"dim M-space at generic depth-one point: {KM.nrows()} (expect 4)",
      flush=True)

# --- rank of pr(M): sigma-average subtraction at witness points
P1w.<z> = PolynomialRing(K6)
WITS = []
random.seed(int(99))
while len(WITS) < 10:
    x0 = K6.random_element()
    if x0 == 0:
        continue
    yr = (z^2 + (2*x0+1)*z - x0^3).roots()
    if not yr:
        continue
    y0 = yr[0][0]
    if y0 == 0:
        continue
    ur = (z^2 - hp2(x0, y0)).roots()
    if not ur or ur[0][0] == 0:
        continue
    tr = (z^3 - y0).roots()
    if not tr:
        continue
    WITS.append((x0, y0, ur[0][0], tr[0][0]))

prrows = []
for r in range(KM.nrows()):
    vec = [sum(KM[r][b] * OMEGA_BASIS[b][c] for b in range(10))
           for c in range(len(POOL))]
    row = []
    for (x0, y0, u0, t0) in WITS:
        vals = [evalpool(vec, x0, y0, u0, ZETA^k * t0) for k in range(3)]
        row.append(vals[0] - sum(vals)/3)
    prrows.append(row)
rk = matrix(K6, prrows).rank()
print(f"rank pr(M) = {rk} (expect 3: W1 verified at a GENERIC depth-one "
      f"point; kernel of pr = the trace line T_L)", flush=True)

# ================= tau-layer: the Gauss rank =================
# eta(tau) = (u + l + tau*l1)/u omega0; the divisor's primary geometric
# point moves tau-linearly: solve the 2x2 system (E0 tangency + F-motion);
# conjugates by Frobenius (l1 rational). Rows over dual numbers via
# logarithmic derivatives; kernel by perturbation M0 K1 = -M1 K0.

d6, x0r, y0r, u0r, t0r, Kd6 = LIFT[0]
if d6 > 1:
    emb6 = Kd6.hom([Kd6.gen().minimal_polynomial().roots(K6)[0][0]], K6)
    X0, Y0, U0, T0 = emb6(x0r), emb6(y0r), emb6(u0r), emb6(t0r)
else:
    X0, Y0, U0, T0 = K6(x0r), K6(y0r), K6(u0r), K6(t0r)
assert len(LIFT) == 1, "tau-layer written for the single-closed-point base"

F0poly = l^2 - hp2
Gx, Gy = Gc.derivative(X), Gc.derivative(Y)
F0x, F0y = F0poly.derivative(X), F0poly.derivative(Y)
lx, ly = l.derivative(X), l.derivative(Y)


def first_order(l1):
    A = matrix(K6, [[Gx(X0, Y0), Gy(X0, Y0)], [F0x(X0, Y0), F0y(X0, Y0)]])
    b = vector(K6, [0, -2*l(X0, Y0)*l1(X0, Y0)])
    x1, y1 = A.solve_right(b)
    u1 = -(lx(X0, Y0)*x1 + ly(X0, Y0)*y1 + l1(X0, Y0))
    t1 = y1 / (3*T0^2)
    return x1, y1, u1, t1


def dual_matrices(x1, y1, u1, t1):
    cx, cy, cu, ct = X0, Y0, U0, T0
    dx, dy, du, dt = x1, y1, u1, t1
    M0r, M1r = [], []
    for i in range(6):
        r0, r1 = [], []
        for vb in OMEGA_BASIS:
            v0 = K6(0); v1 = K6(0)
            for cc, (pp, q, ii, jj) in zip(vb, POOL):
                if cc:
                    m0 = cc * cx^pp * cy^q * cu^ii * ct^jj
                    v0 += m0
                    v1 += m0 * (pp*dx/cx + q*dy/cy + ii*du/cu + jj*dt/ct)
            r0.append(v0); r1.append(v1)
        M0r.append(r0); M1r.append(r1)
        cx, cy, cu, ct = cx^7, cy^7, cu^7, ct^7
        dx, dy, du, dt = dx^7, dy^7, du^7, dt^7
    return matrix(K6, M0r), matrix(K6, M1r)


def prvals(poolvec):
    row = []
    for (xw, yw, uw, tw) in WITS:
        vals = [evalpool(poolvec, xw, yw, uw, ZETA^k * tw) for k in range(3)]
        row.append(vals[0] - sum(vals)/3)
    return vector(K6, row)


def poolcomb(coeffs):
    return [sum(coeffs[b] * OMEGA_BASIS[b][c] for b in range(10))
            for c in range(len(POOL))]


# target 6-dim coordinates inside witness space
TBrows = []
for vb in OMEGA_BASIS:
    TBrows.append(prvals(vb))
TBmat = matrix(K6, TBrows)
TB = TBmat.row_space().basis_matrix()
assert TB.nrows() == 6, f"target coord rank {TB.nrows()} != 6"


def coords6(w):
    return TB.transpose().solve_right(w)


# frame at tau=0: pick 3 independent generators of pr(M)
V0 = [prvals(poolcomb(KM.row(a))) for a in range(4)]
C0 = [coords6(w) for w in V0]
M3 = matrix(K6, C0)
pick = M3.pivot_rows()
assert len(pick) == 3
F0c = matrix(K6, [C0[a] for a in pick])

# complement basis: extend F0c to rank 6 using TB-coordinate unit vectors
Qrows = list(F0c.rows())
for e in identity_matrix(K6, 6).rows():
    if matrix(K6, Qrows + [e]).rank() > len(Qrows):
        Qrows.append(e)
    if len(Qrows) == 6:
        break
QB = matrix(K6, Qrows)     # rows: 3 frame + 3 complement


def quotient_coords(w6):
    sol = QB.transpose().solve_right(w6)
    return vector(K6, [sol[3], sol[4], sol[5]])


Hvecs = []
M0chk = None
for l1 in (R2b(1), X, Y):
    x1, y1, u1, t1 = first_order(l1)
    M0d, M1d = dual_matrices(x1, y1, u1, t1)
    if M0chk is None:
        M0chk = M0d
        assert M0d.right_kernel().dimension() == 4, "tau0 kernel mismatch"
    # perturbation solve per chosen generator
    H = []
    for a in pick:
        k0 = vector(K6, KM.row(a))
        k1 = M0d.solve_right(-M1d * k0)
        v1 = prvals(poolcomb(list(k1)))
        H.append(quotient_coords(coords6(v1)))
    Hmat = matrix(K6, H)     # 3x3: the second-fundamental-form block
    Hvecs.append(vector(K6, Hmat.list()))
    print(f"direction l1 = {l1}: II-block rank = {Hmat.rank()}", flush=True)

GR = matrix(K6, Hvecs).rank()
print(f"GAUSS RANK (rank d-gamma) = {GR}  "
      f"({'nondegenerate, theta-like' if GR == 3 else 'DEGENERATE — structural news'})",
      flush=True)