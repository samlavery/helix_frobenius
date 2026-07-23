# W1-final probe v2: rail occupancy of twisted limit canonicals on the mu_3 chain.
# Chain: R_0 - E_1 - R_1 - ... - E_g - R_g (tree; bridges = copies of E0,
# eps_i = [T - O] exact order 3; attachment points P_i, Q_i in E0(F_p) vary).
# omega_0|E_i = O(P_i + Q_i); twist j: O(P_i + Q_i + jT - jO); rationals untwisted.
# Sections: per-component + residue matching at nodes (dualizing sheaf, tree =>
# eps glues trivially).  v2 fix: L(D) pool = x^a y^b / ((x - xP)(x - xQ)) so
# sections HAVE poles at the attachment points; conditions at conjugates + T/T'/O.

p = 7
F = GF(p)
S.<s> = LaurentSeriesRing(F, default_prec=16)
Tpt, Tppt = (F(0), F(0)), (F(0), F(6))


def conj(pt):
    x0, y0 = pt
    return (x0, -y0 - 2*x0 - 1)


def series_at(pl):
    """(x(s), y(s)) at the place pl ('O' or affine point)."""
    if pl == 'O':
        xO = s^-2
        for _ in range(20):
            xO = s^-2 + 2*s^-1 + 1/(xO*s)
        return (xO, xO/s)
    x0, y0 = pl
    xs = x0 + s
    ys = y0 + 0*s
    for _ in range(20):
        fy = ys^2 + 2*xs*ys + ys - xs^3
        ys = ys - fy/(2*ys + 2*xs + 1)
    return (xs, ys)


POOL = [(a, b) for a in range(-2, 4) for b in range(0, 2)]


def LD(P, Q, j):
    """L(P + Q + jT - jO) on E0.  Returns (K, resP, resQ): kernel basis matrix
    over the 12-monomial pool /D(x), and residue vectors (of f*omega0) at P, Q."""
    xP, xQ = P[0], Q[0]
    allow = {P: 1, Q: 1}
    for pt in (conj(P), conj(Q), Tpt, Tppt):
        if pt not in allow:
            allow[pt] = 0
    allow[Tpt] = max(allow.get(Tpt, 0), 0) + j   # jT pole allowance
    allow['O'] = -j                              # forced vanishing order j at O
    rows, sers_at = [], {}
    for pl, a in allow.items():
        xs, ys = series_at(pl)
        den = (xs - xP) * (xs - xQ)
        sers = [xs^aa * ys^bb / den for (aa, bb) in POOL]
        sers_at[pl] = (xs, ys, sers)
        minv = min(t.valuation() for t in sers)
        for order in range(minv, -a):
            rows.append([t[order] for t in sers])
    M = matrix(F, rows)
    K = M.right_kernel().basis_matrix()
    res = {}
    for pl in (P, Q):
        xs, ys, sers = sers_at[pl]
        w = xs.derivative() / (2*ys + 2*xs + 1)
        res[pl] = [sum(c * t for c, t in zip(K.row(r), sers)) * w
                   for r in range(K.nrows())]
        res[pl] = [t[-1] for t in res[pl]]
    # T-valuation fingerprint per basis vector (rail occupancy datum)
    xs, ys, sers = sers_at[Tpt]
    vT = []
    for r in range(K.nrows()):
        f = sum(c * t for c, t in zip(K.row(r), sers))
        vT.append(f.valuation() if f != 0 else 'inf')
    return K, res[P], res[Q], vT


def chain_occupancy(g, att, j):
    bridge = []
    nvars = 0
    offs = []
    for (P, Q) in att:
        K, rP, rQ, vT = LD(P, Q, j)
        offs.append(nvars)
        bridge.append((K.nrows(), rP, rQ, vT))
        nvars += K.nrows()
    N = nvars + (g - 1)
    rows = []
    for i in range(g):
        nb, rP, rQ, vT = bridge[i]
        row = [F(0)] * N                       # node E_i|P_i <-> R_{i-1}
        for r in range(nb):
            row[offs[i] + r] = rP[r]
        if i >= 1:
            row[nvars + i - 1] += F(-1)
        rows.append(row)
        row = [F(0)] * N                       # node E_i|Q_i <-> R_i
        for r in range(nb):
            row[offs[i] + r] = rQ[r]
        if i <= g - 2:
            row[nvars + i] += F(1)
        rows.append(row)
    M = matrix(F, rows)
    Kg = M.right_kernel().basis_matrix()
    dims = [b[0] for b in bridge]
    support = []
    for r in range(Kg.nrows()):
        v = Kg.row(r)
        bs = [i for i in range(g)
              if any(v[offs[i] + t] for t in range(bridge[i][0]))]
        rs = [k for k in range(g - 1) if v[nvars + k]]
        support.append((bs, rs))
    return Kg.nrows(), dims, support, [b[3] for b in bridge]


E0pts = [(x0, y0) for x0 in F for y0 in F
         if (y0^2 + 2*x0*y0 + y0 - x0^3) == 0]
aff = [pt for pt in E0pts if pt[0] != 0]
print(f"E0(F_{p}) usable affine points (x != 0): {len(aff)}", flush=True)

import random
for g in (2, 3):
    print(f"=== chain g={g} ===", flush=True)
    for trial in range(4):
        random.seed(int(100*g + trial))
        att = [tuple(random.sample(aff, 2)) for _ in range(g)]
        for j in range(3):
            dim, dims, supp, vTs = chain_occupancy(g, att, j)
            print(f"  t{trial} j={j}: dim={dim} (exp {g if j==0 else g-1}) "
                  f"perbridge-h0={dims} vT={vTs}", flush=True)
            for (bs, rs) in supp:
                print(f"      section: bridges {bs}, interior rationals {rs}",
                      flush=True)


def add_pts(P1, P2):
    """Group law on y^2 + 2xy + y = x^3 (a1=2, a3=1)."""
    x1, y1 = P1
    x2, y2 = P2
    if x1 == x2 and (y1 + y2 + 2*x1 + 1) == 0:
        return 'O'
    if P1 == P2:
        lam = (3*x1^2 - 2*y1) / (2*y1 + 2*x1 + 1)
    else:
        lam = (y2 - y1) / (x2 - x1)
    x3 = lam^2 + 2*lam - x1 - x2
    y3 = lam*(x1 - x3) - y1 - 2*x3 - 1
    return (x3, y3)


print("=== EXCLUSION probe: Q = P (+) T  (attachment difference in <eps>) ===",
      flush=True)
for g in (2,):
    for trial in range(4):
        random.seed(int(500 + trial))
        att = []
        for _ in range(g):
            while True:
                P = random.choice(aff)
                Q = add_pts(P, Tpt)
                if Q != 'O' and Q[0] != 0 and Q != P:
                    break
            att.append((P, Q))
        for j in range(3):
            dim, dims, supp, vTs = chain_occupancy(g, att, j)
            print(f"  t{trial} j={j}: dim={dim} (smooth-val {g if j==0 else g-1})"
                  f" perbridge-h0={dims} vT={vTs}", flush=True)
            for (bs, rs) in supp:
                print(f"      section: bridges {bs}, interior rationals {rs}",
                      flush=True)
