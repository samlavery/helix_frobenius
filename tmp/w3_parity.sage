# W3: rational-lift parity distributions per eta (F_7, c0=1 clean stratum).
# Relative parity of a lift vs a reference = sum_i d_i k_i mod 3 (d_i = the
# closed point's degree, k_i = the zeta-shift of the chosen cube root).
# PREDICTIONS from the SIGMA-parity structure:
#   * some d_i != 0 mod 3  => lifts split UNIFORMLY (1/3 each component);
#   * all d_i == 0 mod 3   => ALL lifts land in ONE component (e.g. the
#     Gauss base point: a single degree-6 point);
#   * this non-uniformity is why 1502 is not divisible by 3.

p = 7
F7 = GF(p)
R2.<X, Y> = PolynomialRing(F7)
G = Y^2 + 2*X*Y + Y - X^3
hpoly = -2*X^3 + X^2 - X*Y + 3*X + 1
RX.<xx> = PolynomialRing(F7)


def Dop(f):
    return (2*Y + 2*X + 1)*f.derivative(X) + (3*X^2 - 2*Y)*f.derivative(Y)


def is_cube(v, K):
    return v == 0 or v^((K.order() - 1) // 3) == 1


from itertools import product as iproduct
hist = {}
tested = 0
for c1 in F7:
    for c2 in F7:
        for c3 in F7:
            l = c1 + c2*X + c3*Y
            Fq = l^2 - hpoly
            res = Fq.resultant(G, Y)
            resx = RX(res(xx, 0))
            if resx == 0 or not resx.is_squarefree():
                continue
            degs = []
            ok = True
            for (pfac, _) in resx.factor():
                if pfac.degree() == 0:
                    continue
                d = pfac.degree()
                K = GF(p^d, 'a') if d > 1 else F7
                x0 = pfac.roots(K)[0][0]
                RY.<yy> = PolynomialRing(K)
                got = False
                for (y0, _) in RY(G(x0, yy)).roots():
                    if Fq(x0, y0) != 0:
                        continue
                    got = True
                    if not is_cube(y0, K) or Dop(Fq)(x0, y0) == 0:
                        ok = False
                        break
                    degs.append(d)
                if not ok or not got:
                    ok = ok and got
                    if not ok:
                        break
            if not ok or sum(degs) != 6:
                continue
            # parity distribution over the prod(3) lifts
            dist = [0, 0, 0]
            for ks in iproduct(range(3), repeat=len(degs)):
                par = sum(d*k for d, k in zip(degs, ks)) % 3
                dist[par] += 1
            key = (tuple(sorted(degs)), tuple(sorted(dist, reverse=True)))
            hist[key] = hist.get(key, 0) + 1
            tested += 1

print(f"clean all-split etas tested: {tested}", flush=True)
print("(point-degrees) -> sorted parity-distribution : #etas", flush=True)
for key in sorted(hist):
    print(f"  {key[0]} -> {key[1]} : {hist[key]}", flush=True)
print("PREDICTION CHECK: uniform (n,n,n) iff some degree !≡ 0 mod 3;"
      " concentrated (N,0,0) iff all degrees ≡ 0 mod 3 (e.g. (3,3), (6,)).",
      flush=True)