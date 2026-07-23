# v2 (involution-hardened) sixfold: degree-12 L-poly at p=7, full k<=6 tower.
# C' : u^3 + x*u + (y+a) = 0 over E0;  C : t^3 = y.  n_u now depends on BOTH coordinates.
# O-fiber for u: residual cubic w^3 + w + 1 (disc -31; sign-independent).
# THE QUESTION: is P_B still a square at the split prime -- or not (tau-mechanism gone)?

p = 13
a_par = 1
KMAX = 6

def counts(q):
    F = GF(q)
    R.<u> = PolynomialRing(F)
    three_div = (q - 1) % 3 == 0
    e3 = (q - 1) // 3 if three_div else None
    def n_cube(v):
        if v == 0:
            return 1
        if not three_div:
            return 1
        return 3 if v**e3 == 1 else 0
    sum_nt = 0; nCp = 0; nC = 0; nE0 = 1
    nuO = len((u**3 + u + 1).roots(multiplicities=False))   # residual at O
    ntO = n_cube(F(-1))
    sum_nt += ntO; nCp += nuO; nC += nuO * ntO
    two = F(2); four = F(4)
    for x in F:
        b = two * x + 1; d = b*b + four * x**3
        if d == 0:
            ys = [-b / two]
        elif d.is_square():
            s = d.sqrt(); ys = [(-b + s)/two, (-b - s)/two]
        else:
            ys = []
        for y0 in ys:
            nE0 += 1
            nu = len((u**3 + x*u + (y0 + a_par)).roots(multiplicities=False))
            nt = n_cube(F(1)) if (x == 0 and y0 == 0) else n_cube(y0)
            sum_nt += nt; nCp += nu; nC += nu * nt
    assert sum_nt == nE0, (q, sum_nt, nE0)
    return nE0, nCp, nC

s = []
for k in range(1, KMAX + 1):
    q = p**k
    nE0, nCp, nC = counts(q)
    s.append(nCp - nC)
    print(f"k={k} q={q}: #E0={nE0} #C'={nCp} #C={nC}  s_{k}={nCp-nC}")

e = [QQ(1)]
for k in range(1, KMAX + 1):
    acc = QQ(0)
    for i in range(1, k + 1):
        acc += (-1)**(i - 1) * e[k - i] * s[i - 1]
    e.append(acc / k)
for j in range(7, 13):
    e.append(QQ(p)**(j - 6) * e[12 - j])
RZ.<T> = ZZ[]
P = RZ(sum((-1)**j * e[j] * T**j for j in range(13)))
print("\nP_B(T) =", P)
print("\nfactor over ZZ:", P.factor())
print("\n|roots|^2 * p (want all 1.000):",
      sorted(set(round(abs(r)**2 * p, 3) for r in P.roots(CC, multiplicities=False))))
