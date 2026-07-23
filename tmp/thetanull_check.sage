# Lemma C reduced-case check for the tower's genus-4 base curve C:
# C: u^3 + x*u + (y+1) = 0 over E0: y^2+2xy+y = x^3.
# g=4 canonical model lies on a unique quadric in P^3; RANK 4 <=> no vanishing
# thetanull <=> h^0(omega - 2N) = 0 for the trigonal pencils <=> Lemma C
# (reduced case) HOLDS for this curve.  Rank 3 (cone) <=> omega = 2N and a
# failing (L, s) is constructible — either way Lemma A gets tested.

load('petri_t1.sage')   # F = GF(7^6), E0S/UB/TB/MONS + gate machinery

# --- rebuild the j=0 condition matrix and take its kernel (the canonical basis)
rows = []
for pl in ('T', 'Tp', 'O'):
    xs, ys = E0S[pl]
    w0 = omega0_val_and_series(pl)
    tb = TB[pl]
    for ub in UB[pl]:
        Fu = 3*ub^2 + xs
        pref = w0 / Fu
        series_list = []
        minv = 10**9
        for i in range(3):
            for (p, q) in MONS:
                ser = (xs^p) * (ys^q) * (ub^i) * pref
                series_list.append(ser)
                minv = min(minv, ser.valuation())
        for order in range(minv, 0):
            rows.append([ser[order] for ser in series_list])
M = matrix(F, rows)
K = M.right_kernel().basis_matrix()
print(f"canonical basis: dim = {K.nrows()} (expect 4)", flush=True)

# --- sample points of C over F_{7^6} and evaluate the 4 coordinate functions
import random
random.seed(int(20260719))
P.<z> = PolynomialRing(F)
pts = []
tried = 0
while len(pts) < 60 and tried < 4000:
    tried += 1
    x0 = F.random_element()
    if x0 == 0:
        continue
    yroots = (z^2 + (2*x0 + 1)*z - x0^3).roots()
    if not yroots:
        continue
    y0 = yroots[random.randrange(len(yroots))][0]
    uroots = (z^3 + x0*z + (y0 + 1)).roots()
    if not uroots:
        continue
    u0 = uroots[random.randrange(len(uroots))][0]
    if 3*u0^2 + x0 == 0:          # avoid ramification of C -> E0
        continue
    pts.append((x0, y0, u0))
print(f"sampled {len(pts)} points of C", flush=True)


def coord(k, pt):
    x0, y0, u0 = pt
    v = F(0)
    idx = 0
    for i in range(3):
        for (p, q) in MONS:
            v += K[k][idx] * x0^p * y0^q * u0^i
            idx += 1
    return v

# --- fit the quadric through the canonical image
qrows = []
for pt in pts:
    zc = [coord(k, pt) for k in range(4)]
    qrows.append([zc[a]*zc[b] for a in range(4) for b in range(a, 4)])
QM = matrix(F, qrows)
kerQ = QM.right_kernel().basis_matrix()
print(f"quadrics through canonical curve: {kerQ.nrows()} (expect 1)", flush=True)

qv = kerQ.row(0)
S = matrix(F, 4, 4)
idx = 0
for a in range(4):
    for b in range(a, 4):
        if a == b:
            S[a, a] = qv[idx]
        else:
            S[a, b] += qv[idx] / 2
            S[b, a] += qv[idx] / 2
        idx += 1
r = S.rank()
print(f"QUADRIC RANK = {r}  ({'rank 4: NO vanishing thetanull — Lemma C reduced case HOLDS for tower-C' if r == 4 else 'CONE: omega = 2N — failing (L,s) constructible, build it and watch ker jump'})", flush=True)

# --- THE FAILURE TEST.  Trigonal pencil = the u-map (u has 3 poles).
# Lemma A predicts: for W = (2 of 3 preimages) over each point of a u-fiber
# E0(c), the Petri kernel on the s-slice = h^0(omega_C - E0(c)) = h^0(N) = 2,
# i.e. the 3 canonical images of a u-fiber are COLLINEAR (rank 2 = cone
# ruling), while 3 random points of C give rank 3.  Kernel jump 1 -> 2 = the
# constructed mu_3-Prym-Petri failure; rank 3 on random triples = the generic
# no-failure control.

def cond_rank(triple):
    rows = [[coord(k, pt) for k in range(4)] for pt in triple]
    return matrix(F, rows).rank()

print("u-fiber triples (predict rank 2 => ker jumps to 2 = h^0(N)):", flush=True)
tested = 0
ci = 0
while tested < 5 and ci < 200:
    ci += 1
    c = F.random_element()
    if c == 0:
        continue
    # fiber {u = c}: y = -(c^3 + c*x + 1) substituted into E0 -> cubic in x
    Rx.<xx> = PolynomialRing(F)
    yy = -(c^3 + c*xx + 1)
    cub = yy^2 + 2*xx*yy + yy - xx^3
    rts = cub.roots()
    if len(rts) != 3:
        continue
    triple = []
    ok = True
    for (x0, _) in rts:
        y0 = -(c^3 + c*x0 + 1)
        u0 = c
        if x0 == 0 or 3*u0^2 + x0 == 0:
            ok = False
            break
        triple.append((x0, y0, u0))
    if not ok:
        continue
    print(f"  c={c}: rank = {cond_rank(triple)}  (ker dim = {4 - cond_rank(triple)})",
          flush=True)
    tested += 1

print("random non-fiber triples (predict rank 3 => ker stays 1 = T only):",
      flush=True)
for trial in range(5):
    triple = random.sample(pts, 3)
    if len({p[2] for p in triple}) < 3:
        continue
    print(f"  trial {trial}: rank = {cond_rank(triple)}  "
          f"(ker dim = {4 - cond_rank(triple)})", flush=True)