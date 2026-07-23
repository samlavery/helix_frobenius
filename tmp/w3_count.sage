# W3/J1: exact |V^1(F_7)|-count (rational effective W with pi_*W in |omega|)
# on the bielliptic specimen, via E0-side closed-point arithmetic.
# eta = (c0 u + l(x,y))/u * omega0,  l = c1 + c2 x + c3 y.
# c0 = 1 (343 etas): div(eta) = zeros of F = l^2 - h on E0, each lifting to
#   the UNIQUE u-sheet u = -l; t-fiber splits iff y-value is a cube.
# c0 = 0 (57 etas): div(eta) = pullback of div0(l) + (3-a)(O+ + O-), a = the
#   O-pole of l; u-sheet now a choice (h-value square test); O+- is one
#   closed degree-2 point (sqrt(-2) irrational) with 3 degree-2 t-points.

p = 7
F7 = GF(p)
R2.<X, Y> = PolynomialRing(F7)
G = Y^2 + 2*X*Y + Y - X^3
hpoly = -2*X^3 + X^2 - X*Y + 3*X + 1
RX.<xx> = PolynomialRing(F7)


def Dop(f):
    return (2*Y + 2*X + 1)*f.derivative(X) + (3*X^2 - 2*Y)*f.derivative(Y)


def is_cube(v, K):
    if v == 0:
        return True          # y=0 only at T; leading coeff 1 is a cube
    return v^((K.order() - 1) // 3) == 1


def is_square(v, K):
    if v == 0:
        return None          # branch point — caller flags
    return v^((K.order() - 1) // 2) == 1


def comb2(m):
    return (m + 2)*(m + 1)//2


def closed_zeros(fpoly):
    """Closed points of div0(fpoly) on E0: list of (d, m, x0, y0, K).
    Multiplicity by D-iteration.  Returns None if degenerate."""
    res = fpoly.resultant(G, Y)
    resx = RX(res(xx, 0))
    if resx == 0:
        return None
    out = []
    for (pfac, _) in resx.factor():
        if pfac.degree() == 0:
            continue
        dx = pfac.degree()
        K = GF(p^dx, 'a') if dx > 1 else F7
        x0 = pfac.roots(K)[0][0] if dx > 1 else pfac.roots()[0][0]
        RY.<yy> = PolynomialRing(K)
        gy = RY(G(x0, yy))
        yr = gy.roots()
        found_pair = False
        for (y0, _) in yr:
            if fpoly(x0, y0) != 0:
                continue
            m = 0
            ftest = fpoly
            while ftest(x0, y0) == 0:
                m += 1
                ftest = Dop(ftest)
                if m > 6:
                    return None
            out.append((dx, m, x0, y0, K))
        if not yr:                      # y in quadratic extension
            K2 = GF(p^(2*dx), 'b')
            RY2.<y2> = PolynomialRing(K2)
            x02 = pfac.roots(K2)[0][0]
            for (y0, _) in RY2(G(x02, y2)).roots():
                if fpoly(x02, y0) != 0:
                    continue
                if found_pair:
                    continue            # conjugate — same closed point
                found_pair = True
                m = 0
                ftest = fpoly
                while ftest(x02, y0) == 0:
                    m += 1
                    ftest = Dop(ftest)
                    if m > 6:
                        return None
                out.append((2*dx, m, x02, y0, K2))
    return out


total = 0
hist = {}
skipped = []
# --- c0 = 1 family: l = c1 + c2 x + c3 y, F = l^2 - h
for c1 in F7:
    for c2 in F7:
        for c3 in F7:
            l = c1 + c2*X + c3*Y
            Fq = l^2 - hpoly
            pts = closed_zeros(Fq)
            if pts is None:
                skipped.append(('c0=1', c1, c2, c3, 'degenerate'))
                continue
            degsum = sum(d*m for (d, m, _, _, _) in pts)
            if degsum != 6:
                skipped.append(('c0=1', c1, c2, c3, f'degsum={degsum}'))
                continue
            nl = 1
            ok = True
            for (d, m, x0, y0, K) in pts:
                if l(x0, y0) == 0 and hpoly(x0, y0) == 0:
                    ok = False          # zero hits a branch point
                    break
                if is_cube(y0, K):
                    nl *= comb2(m)
                else:
                    nl *= (1 if m % 3 == 0 else 0)
                if nl == 0:
                    break
            if not ok:
                skipped.append(('c0=1', c1, c2, c3, 'branch-hit'))
                continue
            total += nl
            hist[nl] = hist.get(nl, 0) + 1

# --- c0 = 0 face: eta = (l/u) omega0
def opart_lifts(mult_per_side):
    """O+- = one closed deg-2 point; 3 deg-2 t-points; symmetric mult
    (m, m): Frobenius-stable assignments = compositions of m into 3."""
    return comb2(mult_per_side)


for (c1, c2, c3) in [(0, 0, 1), (0, 1, 0)] + \
        [(c1, c2, 1) for c1 in F7 for c2 in F7 if (c1, c2) != (0, 0)] + \
        [(c1, 1, 0) for c1 in F7 if c1 != 0] + [(1, 0, 0)]:
    l = c1 + c2*X + c3*Y
    a = 3 if c3 != 0 else (2 if c2 != 0 else 0)
    nl = opart_lifts(3 - a)
    ok = True
    if a > 0:
        pts = closed_zeros(l)
        if pts is None:
            skipped.append(('c0=0', c1, c2, c3, 'degenerate'))
            continue
        degsum = sum(d*m for (d, m, _, _, _) in pts)
        if degsum != a:
            skipped.append(('c0=0', c1, c2, c3, f'degsum={degsum}!={a}'))
            continue
        for (d, m, x0, y0, K) in pts:
            hv = hpoly(x0, y0)
            sq = is_square(hv, K)
            if sq is None:
                ok = False
                break
            if sq:      # u splits: 2 pts deg d
                if is_cube(y0, K):      # 6 pts deg d
                    nl *= (m+5)*(m+4)*(m+3)*(m+2)*(m+1)//120
                else:                   # 2 pts deg 3d
                    nl *= (m//3 + 1) if m % 3 == 0 else 0
            else:       # u inert: 1 pt deg 2d
                K2 = GF(p^(2*d), 'c')
                y02 = K2(y0) if d == 1 else y0.minimal_polynomial().roots(K2)[0][0]
                if is_cube(y02, K2):    # 3 pts deg 2d
                    nl *= comb2(m//2) if m % 2 == 0 else 0
                else:                   # 1 pt deg 6d
                    nl *= 1 if m % 6 == 0 else 0
            if nl == 0:
                break
    if not ok:
        skipped.append(('c0=0', c1, c2, c3, 'branch-hit'))
        continue
    total += nl
    hist[nl] = hist.get(nl, 0) + 1

print(f"RAW COUNT (sum over eta of rational lifts) = {total}", flush=True)
print(f"  [= #V^1(F_7) weighted by #|L|(F_7); depth-one L count once]", flush=True)
print(f"heuristic scale: |P^3(F_7)| = 400, 7^3 = 343", flush=True)
print(f"lift-count histogram (lifts-per-eta: #etas): "
      f"{dict(sorted(hist.items()))}", flush=True)
print(f"skipped/exceptional etas: {len(skipped)}", flush=True)
for srow in skipped[:12]:
    print(f"  {srow}", flush=True)