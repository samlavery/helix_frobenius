# W2 specimen builder: bielliptic genus-4 tower with certified NON-thetanull.
# E0: y^2+2xy+y = x^3;  C: u^2 = h(x,y), h in L(6O) = <1,x,x^2,x^3,y,xy>
# (x^3 reduced by the curve relation => quadric z0^2 = Q(1,x,y));
# C~: t^3 = y (etale mu_3, eps = pullback of [T-O], nonzero automatically).
# Certificates: (a) rank Q = 3  <=> canonical quadric rank 4 <=> NO vanishing
# thetanull; (b) 6 simple branch zeros avoiding T/T'/O-fibers; (c) eigenspace
# gates dim H^0(omega_C~)_j = 4/3/3  (certifies genus 4 + connected cover).

p = 7
F = GF(p)
R2.<X, Y> = PolynomialRing(F)
G = Y^2 + 2*X*Y + Y - X^3

import random
random.seed(int(20260719))

# --- scan for h = c0 + c1 x + c2 x^2 + c3 x^3 + c4 y + c5 xy with the certs
def reduce_h(cs):
    """h with x^3 replaced via curve: x^3 = y^2+2xy+y  =>  quadratic in (1,x,y)."""
    c0, c1, c2, c3, c4, c5 = cs
    # h = c0 + c1 X + c2 X^2 + c3 X^3 + c4 Y + c5 XY
    # X^3 -> Y^2 + 2XY + Y
    hq = c0 + c1*X + c2*X^2 + c4*Y + c5*X*Y + c3*(Y^2 + 2*X*Y + Y)
    return hq  # quadratic in (1, X, Y) when viewed with monomials 1,X,Y,X^2,XY,Y^2


def Qrank(hq):
    """Rank of hq as a quadratic form in (1, X, Y) (char 7 != 2)."""
    m = matrix(F, 3, 3)
    def co(i, j):
        if i == 0 and j == 0:
            return hq.constant_coefficient()
        return hq.monomial_coefficient(X^i * Y^j)
    m[0,0] = co(0,0)
    m[1,1] = co(2,0)
    m[2,2] = co(0,2)
    m[0,1] = co(1,0)/2; m[1,0] = m[0,1]
    m[0,2] = co(0,1)/2; m[2,0] = m[0,2]
    m[1,2] = co(1,1)/2; m[2,1] = m[1,2]
    return m.rank()


def Dh(hpoly):
    """Invariant derivation on E0: D = (2y+2x+1) d/dx + (3x^2-2y) d/dy."""
    return (2*Y + 2*X + 1)*hpoly.derivative(X) + (3*X^2 - 2*Y)*hpoly.derivative(Y)


K6 = GF(p^6, 'w')


def branch_ok(hpoly):
    """6 distinct simple zeros on E0, none over x=0 (T/T') or at O."""
    RX.<xx> = PolynomialRing(F)
    res = hpoly.resultant(G, Y)      # poly in X
    resx = RX(res(xx, 0))
    if resx == 0:
        return False
    dh = Dh(hpoly)
    cnt = 0
    for (x0, mult) in resx.roots(K6):
        # y-roots over x0 on the curve
        RY.<yy> = PolynomialRing(K6)
        for (y0, _) in RY(G(x0, yy)).roots():
            if hpoly(x0, y0) == 0:
                if x0 == 0:
                    return False
                if dh(x0, y0) == 0:
                    return False
                cnt += 1
    return cnt == 6


found = None
for trial in range(400):
    cs = [F(random.randrange(p)) for _ in range(6)]
    if cs[3] == 0:
        cs[3] = F(1)          # keep x^3 present => h has exact pole order 6 at O
    hpoly = cs[0] + cs[1]*X + cs[2]*X^2 + cs[3]*X^3 + cs[4]*Y + cs[5]*X*Y
    hq = reduce_h(cs)
    if Qrank(hq) != 3:
        continue
    if not branch_ok(hpoly):
        continue
    found = (cs, hpoly, hq)
    print(f"SPECIMEN found (trial {trial}): h = {hpoly}", flush=True)
    print(f"  reduced quadric Q = {hq}   rank(Q) = 3  => canonical quadric rank 4:"
          f" NON-THETANULL CERTIFIED", flush=True)
    break
if found is None:
    raise SystemExit("no specimen in scan range")
cs, hpoly, hq = found

# --- eigenspace gates on C~ = {u^2 = h, t^3 = y}: conditions only at the six
# places over O (pool monomials have poles nowhere else).
NTRUNC = 20
S.<s> = LaurentSeriesRing(K6, default_prec=NTRUNC)

P1.<z> = PolynomialRing(K6)
ZETA = K6(F(2))                      # 2^3 = 1 mod 7


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


def cover_places(pl):
    """All C~-places over the E0-place pl: (xs, ys, u-series, t-series) tuples,
    with the omega0-pullback shift implicit (div omega0-pullback = R~, away
    from T/T'/O)."""
    xs, ys = e0_series(pl)
    hser = hpoly(xs, ys)
    lead = hser.coefficients()[0]
    ubrs = []
    for (u0, _) in (z^2 - lead).roots():
        v = hser.valuation()
        assert v % 2 == 0
        u = u0 * s^(v // 2)
        for _ in range(NTRUNC + 4):
            u = u - (u^2 - hser)/(2*u)
        ubrs.append(u)
    assert len(ubrs) == 2, f"u-cover not split at {pl}"
    yv = ys.valuation()
    assert yv % 3 == 0
    tl = (z^3 - ys.coefficients()[0]).roots()
    assert tl, f"t-cover leading coeff not a cube at {pl}"
    t0 = tl[0][0] * s^(yv // 3)
    for _ in range(NTRUNC + 4):
        t0 = t0 - (t0^3 - ys)/(3*t0^2)
    out = []
    for u in ubrs:
        for k in range(3):
            out.append((xs, ys, u, ZETA^k * t0))
    return out


PLACES = {pl: cover_places(pl) for pl in ('O', (F(0), F(0)), (F(0), F(6)))}
POOL = [(pp, q, i, j) for pp in range(-2, 4) for q in (0, 1)
        for i in (0, 1) for j in (0, 1, 2)]


def gate(j):
    """dim of the t^j-eigenspace of H^0(omega_C~): eta = (A/u) * omega0-pullback,
    A = x^p y^q u^i t^j; regularity at the six O-places (poles allowed nowhere)
    plus the twelve T/T'-places (p = -1 monomials have poles there)."""
    rows = []
    ncols = len([1 for mp in POOL if mp[3] == j])
    for pl, places in PLACES.items():
        for (xs, ys, u, t) in places:
            sers = [(xs^pp * ys^q * u^i * t^j) / u
                    for (pp, q, i, jj) in POOL if jj == j]
            minv = min(tt.valuation() for tt in sers)
            for order in range(minv, 0):
                rows.append([tt[order] for tt in sers])
    M = matrix(K6, rows)
    return ncols - M.rank()


dims = [gate(j) for j in range(3)]
print(f"GATES: eigenspace dims = {dims}  (expect [4, 3, 3]:"
      f" genus 4 + connected etale mu_3 cover, eps != 0)", flush=True)
