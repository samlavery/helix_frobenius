# W3/J3: |V^1(F_49)|-weighted count (k = 2 census) — irreducibility test:
# irreducible dim-3 => count/49^3 -> ~1 + O(q^{-1/2}); several components
# => ratio ~ #components.  Field-generic adaptation of w3_count.sage.

q = 49
K1 = GF(q, 'g2')
R2.<X, Y> = PolynomialRing(K1)
G = Y^2 + 2*X*Y + Y - X^3
hpoly = -2*X^3 + X^2 - X*Y + 3*X + 1
RX.<xx> = PolynomialRing(K1)
OSPLIT = K1(-2).is_square()          # True over F_49


def Dop(f):
    return (2*Y + 2*X + 1)*f.derivative(X) + (3*X^2 - 2*Y)*f.derivative(Y)


def is_cube(v, K):
    return v == 0 or v^((K.order() - 1) // 3) == 1


def comb2(m):
    return (m + 2)*(m + 1)//2


EXT = {}
def ext_field(d):
    if d not in EXT:
        EXT[d] = K1.extension(d, f'e{d}')
    return EXT[d]


def closed_zeros(fpoly):
    res = fpoly.resultant(G, Y)
    resx = RX(res(xx, 0))
    if resx == 0:
        return None
    out = []
    for (pfac, _) in resx.factor():
        if pfac.degree() == 0:
            continue
        dx = pfac.degree()
        K = ext_field(dx) if dx > 1 else K1
        x0 = pfac.roots(K)[0][0]
        RY.<yy> = PolynomialRing(K)
        yr = RY(G(x0, yy)).roots()
        found_pair = False
        if yr:
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
        else:
            K2 = ext_field(2*dx)
            RY2.<y2> = PolynomialRing(K2)
            x02 = pfac.roots(K2)[0][0]
            for (y0, _) in RY2(G(x02, y2)).roots():
                if fpoly(x02, y0) != 0 or found_pair:
                    continue
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
nzero = 0
skipped = 0
done = 0
import sys
for c1 in K1:
    for c2 in K1:
        for c3 in K1:
            l = c1 + c2*X + c3*Y
            Fq = l^2 - hpoly
            pts = closed_zeros(Fq)
            done += 1
            if done % 20000 == 0:
                print(f"  ...{done} etas, total so far {total}", flush=True)
            if pts is None:
                skipped += 1
                continue
            if sum(d*m for (d, m, _, _, _) in pts) != 6:
                skipped += 1
                continue
            nl = 1
            ok = True
            for (d, m, x0, y0, K) in pts:
                if l(x0, y0) == 0 and hpoly(x0, y0) == 0:
                    ok = False
                    break
                if is_cube(y0, K):
                    nl *= comb2(m)
                else:
                    nl *= (1 if m % 3 == 0 else 0)
                if nl == 0:
                    break
            if not ok:
                skipped += 1
                continue
            if nl == 0:
                nzero += 1
            total += nl

# c0 = 0 face (O-part: two rational O-points over F_49, independent sides)
def opart(mside):
    return comb2(mside)^2 if OSPLIT else comb2(mside)


face = [(K1(0), K1(0), K1(1)), (K1(0), K1(1), K1(0)), (K1(1), K1(0), K1(0))]
face += [(c1, c2, K1(1)) for c1 in K1 for c2 in K1 if (c1, c2) != (0, 0)]
face += [(c1, K1(1), K1(0)) for c1 in K1 if c1 != 0]
for (c1, c2, c3) in face:
    l = c1 + c2*X + c3*Y
    a = 3 if c3 != 0 else (2 if c2 != 0 else 0)
    nl = opart(3 - a)
    ok = True
    if a > 0:
        pts = closed_zeros(l)
        if pts is None or sum(d*m for (d, m, _, _, _) in pts) != a:
            skipped += 1
            continue
        for (d, m, x0, y0, K) in pts:
            hv = hpoly(x0, y0)
            if hv == 0:
                ok = False
                break
            if hv^((K.order()-1)//2) == 1:
                if is_cube(y0, K):
                    nl *= (m+5)*(m+4)*(m+3)*(m+2)*(m+1)//120
                else:
                    nl *= (m//3 + 1) if m % 3 == 0 else 0
            else:
                K2 = ext_field(2*d) if K is K1 else ext_field(2*d)
                y02 = K2(y0) if K.degree() == 1 else \
                    y0.minimal_polynomial().roots(K2)[0][0]
                if is_cube(y02, K2):
                    nl *= comb2(m//2) if m % 2 == 0 else 0
                else:
                    nl *= 1 if m % 6 == 0 else 0
            if nl == 0:
                break
    if not ok:
        skipped += 1
        continue
    total += nl

print(f"K2 CENSUS: weighted count = {total}", flush=True)
print(f"  ratio to 49^3 = {float(total/49^3):.3f}   "
      f"(k=1 ratio was 1502/343 = 4.38)", flush=True)
print(f"  zero-lift etas: {nzero}; skipped {skipped}", flush=True)