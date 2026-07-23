# h^0(O(W)) for the constructed failing W on the mu_3 tower.
# W = (2 of 3 t-preimages) over each point of the u-fiber {u=c} on C.
# L(W) = (1/(u-c)) * { g in L(D9) : g(v_i) = 0, i=1..3 }, where D9 = the nine
# O-places of C~ with pole <= 1, and v_i = the EXCLUDED preimages.
# Predictions: dim L(D9) = 4 ({1,u} + {t} + {x/t} isotypics); kernel = 1
# (contains u-c) => h^0(O(W)) = 1 => literal h^0=1 counterexample on the
# thetanull curve.

load('petri_t1.sage')   # F, E0S, UB, TB, MONS machinery; zeta3 = 2 in F_7

ZETA = F(2)
assert ZETA^3 == 1 and ZETA != 1

# pool: x^p y^q u^i t^j
def build_pool(PMIN, PMAX):
    return [(p, q, i, j) for p in range(PMIN, PMAX+1) for q in (0, 1)
            for i in (0, 1, 2) for j in (0, 1, 2)]


def L_D9(pool):
    rows = []
    for pl in ('T', 'Tp', 'O'):
        xs, ys = E0S[pl]
        tb = TB[pl]
        allow = 1 if pl == 'O' else 0
        for ub in UB[pl]:
            for k in range(3):
                tser = ZETA^k * tb
                sers = [xs^p * ys^q * ub^i * tser^j for (p, q, i, j) in pool]
                minv = min(t.valuation() for t in sers)
                for order in range(minv, -allow):
                    rows.append([t[order] for t in sers])
    M = matrix(F, rows)
    return M.right_kernel().basis_matrix()


for (pmin, pmax) in ((-2, 3), (-3, 4)):
    pool = build_pool(pmin, pmax)
    K9 = L_D9(pool)
    print(f"pool p in [{pmin},{pmax}] ({len(pool)} monomials): "
          f"dim L(D9) = {K9.nrows()} (predict 4)", flush=True)

pool = build_pool(-3, 4)
K9 = L_D9(pool)

# --- excluded points: pick a u-fiber, for each of its 3 base points pick ONE
# t-preimage to exclude (W = the other two).  Try several fibers and choices.
import random
random.seed(int(719))
P.<z> = PolynomialRing(F)
Rx.<xx> = PolynomialRing(F)


def eval_g(vec, pt):
    x0, y0, u0, t0 = pt
    v = F(0)
    for ccoef, (p, q, i, j) in zip(vec, pool):
        if ccoef:
            v += ccoef * x0^p * y0^q * u0^i * t0^j
    return v


tested = 0
ci = 0
while tested < 6 and ci < 300:
    ci += 1
    c = F.random_element()
    if c == 0:
        continue
    yy = -(c^3 + c*xx + 1)
    rts = (yy^2 + 2*xx*yy + yy - xx^3).roots()
    if len(rts) != 3:
        continue
    base = []
    ok = True
    for (x0, _) in rts:
        y0 = -(c^3 + c*x0 + 1)
        if x0 == 0 or y0 == 0 or 3*c^2 + x0 == 0:
            ok = False
            break
        trs = (z^3 - y0).roots()
        if len(trs) != 3:
            ok = False
            break
        base.append((x0, y0, [r for r, _ in trs]))
    if not ok:
        continue
    # two exclusion patterns: random choice, and "aligned" choice (first root)
    for tag in ('random', 'aligned'):
        excl = []
        for (x0, y0, trs) in base:
            t0 = random.choice(trs) if tag == 'random' else trs[0]
            excl.append((x0, y0, c, t0))
        rows = [[eval_g(K9.row(r), pt) for r in range(K9.nrows())]
                for pt in excl]
        M = matrix(F, rows)
        h0W = K9.nrows() - M.rank()
        print(f"  fiber c={c} [{tag}]: h^0(O(W)) = {h0W} "
              f"({'LITERAL h^0=1 counterexample' if h0W == 1 else 'h>=2 point'})",
              flush=True)
    tested += 1