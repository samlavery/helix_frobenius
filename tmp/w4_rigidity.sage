# W4/J4 stage 1: the rigidity multiplication rank on the bielliptic specimen.
# Target: rank of  mult: H^0(omega~) (x) H^0(omega~)^{anti}  -->  H^0(omega~^2)
# (60 -> 27).  Rank 27 <=> ker(H^1(T_Z) -> H^1(O_Z) (x) W) = 0 <=> h^0(N) = 6
# (the AP-threefold rigid modulo translation) — the first number of the
# semiregularity pipeline on the Sym^3-resolution model.
# Method: products of the 10-dim omega-basis with the 6-dim anti-invariant
# part are functions A*B in the pool-squared space; their span inside the
# 27-dim H^0(omega~^2) = {G : div G >= -6*(O-places)} is measured by
# evaluation rank at witness points.  The 27-gate is computed independently.

load('w3_gauss.sage')   # OMEGA_BASIS (10, grades j=0:4, j=1:3, j=2:3), POOL,
                        # PLACES, K6, evalpool, WITS + the earlier pipeline

import random

# --- gate: h^0(omega~^2) = 3*g~ - 3 = 27 via the extended function pool
# quadratic differentials = (G/u^2) * omega0~^2 with div G >= -6*(O-places):
# pool for G: x^p y^q u^i t^j, wider p; conditions at all 18 fiber places
# (poles allowed only over O, up to 6).
QPOOL = [(pp, q, i, j) for pp in range(-4, 8) for q in (0, 1)
         for i in (0, 1) for j in (0, 1, 2)]

rows = []
for pl, places in PLACES.items():
    allow = 6 if pl == 'O' else 0
    for (xs, ys, u, t) in places:
        sers = [xs^pp * ys^q * u^i * t^j for (pp, q, i, j) in QPOOL]
        minv = min(ss.valuation() for ss in sers)
        for order in range(minv, -allow):
            rows.append([ss[order] for ss in sers])
Mq = matrix(K6, rows)
h0q = len(QPOOL) - Mq.rank()
print(f"GATE: h^0(omega~^2) = {h0q}  (expect 27 = 3g~-3)", flush=True)

# --- witness points (need >= 27 in general position; take 40)
random.seed(int(2026720))
P1w.<z> = PolynomialRing(K6)
WITS2 = []
while len(WITS2) < 40:
    x0 = K6.random_element()
    if x0 == 0:
        continue
    yr = (z^2 + (2*x0+1)*z - x0^3).roots()
    if not yr:
        continue
    y0 = yr[random.randrange(len(yr))][0]
    if y0 == 0:
        continue
    ur = (z^2 - hp2(x0, y0)).roots()
    if not ur or ur[0][0] == 0:
        continue
    tr = (z^3 - y0).roots()
    if not tr:
        continue
    WITS2.append((x0, y0, ur[0][0], tr[randrange := random.randrange(len(tr))][0]))

# sanity: the 27-dim space is separated by the 40 witnesses — check by
# evaluating a kernel basis of the QPOOL conditions
KQ = Mq.right_kernel().basis_matrix()


def evalq(vec, pt):
    x0, y0, u0, t0 = pt
    v = K6(0)
    for cc, (pp, q, i, j) in zip(vec, QPOOL):
        if cc:
            v += cc * x0^pp * y0^q * u0^i * t0^j
    return v


sep = matrix(K6, [[evalq(KQ.row(r), pt) for pt in WITS2]
                  for r in range(KQ.nrows())]).rank()
print(f"witness separation of H^0(omega~^2): rank {sep} of {KQ.nrows()}",
      flush=True)

# --- the multiplication matrix: (full 10-basis) x (anti-invariant 6) products,
# evaluated as functions A*B at the witnesses (common trivialization
# 1/u^2 * omega0~^2 cancels for rank purposes at fixed witnesses after
# multiplying by the SAME unit — include the 1/u^2 factor exactly anyway).
ANTI = OMEGA_BASIS[4:]          # grades j=1 (3) and j=2 (3)
rowsM = []
for a in range(10):
    for b in range(6):
        row = []
        for pt in WITS2:
            x0, y0, u0, t0 = pt
            va = evalpool(OMEGA_BASIS[a], x0, y0, u0, t0)
            vb = evalpool(ANTI[b], x0, y0, u0, t0)
            row.append(va * vb / u0^2)
        rowsM.append(row)
MM = matrix(K6, rowsM)
rk = MM.rank()
print(f"MULTIPLICATION RANK = {rk} of min(60, 27)  "
      f"({'SURJECTIVE: h^0(N) = 6, AP-threefold RIGID mod translation' if rk == h0q else 'NOT surjective: extra deformations — discovery'})",
      flush=True)
print(f"kernel dimension = {60 - rk}  (feeds the H^1(N) assembly)", flush=True)
# --- (sigma, iota~)-graded diagnosis of the corank: iota~ = (u -> -u) lifts
# (bielliptic involution); measure each basis vector's iota-sign, the
# per-cell product ranks, and the target cell dims (QPOOL gate + iota-sign).
def iota_sign(vec, pool, pt):
    x0, y0, u0, t0 = pt
    vp = sum(cc * x0^pp * y0^q * u0^i * t0^j
             for cc, (pp, q, i, j) in zip(vec, pool) if cc)
    vm = sum(cc * x0^pp * y0^q * (-u0)^i * t0^j
             for cc, (pp, q, i, j) in zip(vec, pool) if cc)
    if vp == vm:
        return +1
    if vp == -vm:
        return -1
    return 0   # mixed


pt0 = WITS2[0]
# sigma-grade of OMEGA_BASIS entries: construction order j=0 (4), j=1 (3), j=2 (3)
SGRADE = [0]*4 + [1]*3 + [2]*3
ISIGN = [iota_sign(OMEGA_BASIS[a], POOL, pt0) for a in range(10)]
# NOTE: sections are (A/u)omega0~: the 1/u flips the iota-sign of A
ISIGN = [-s for s in ISIGN]
print(f"omega-basis (sigma-grade, iota-sign): {list(zip(SGRADE, ISIGN))}",
      flush=True)

# per-(sigma-grade) product ranks
for gtar in range(3):
    rowsg = []
    for a in range(10):
        for b in range(6):
            if (SGRADE[a] + SGRADE[4 + b]) % 3 != gtar:
                continue
            row = []
            for pt in WITS2:
                x0, y0, u0, t0 = pt
                va = evalpool(OMEGA_BASIS[a], x0, y0, u0, t0)
                vb = evalpool(OMEGA_BASIS[4 + b], x0, y0, u0, t0)
                row.append(va * vb / u0^2)
            rowsg.append(row)
    rkg = matrix(K6, rowsg).rank()
    # target cell dim: QPOOL gate restricted to sigma-grade gtar
    sub = [mp for mp in QPOOL if mp[3] == gtar]
    rows = []
    for pl, places in PLACES.items():
        allow = 6 if pl == 'O' else 0
        for (xs, ys, u, t) in places:
            sers = [xs^pp * ys^q * u^i * t^j for (pp, q, i, j) in sub]
            minv = min(ss.valuation() for ss in sers)
            for order in range(minv, -allow):
                rows.append([ss[order] for ss in sers])
    dtar = len(sub) - matrix(K6, rows).rank()
    print(f"  sigma-grade {gtar}: product rank {rkg} of target dim {dtar} "
          f"({len(rowsg)} products)", flush=True)
