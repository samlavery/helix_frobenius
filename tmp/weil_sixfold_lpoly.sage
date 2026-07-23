# Weil sixfold candidate: degree-12 Prym L-polynomial via exact counts over GF(p^k), k<=6.
# RUN: sage tmp/weil_sixfold_lpoly.sage      (Sage GF only -- no FunctionField, per house note)
#
# Construction (weil-sixfold-hunt dossier, validated k=1 by tmp/weil_sixfold.py, 14/14 PASS):
#   E0 : y^2 + 2xy + y = x^3   (Schoen curve, cond 19);  C' : u^3 + x*u + c = 0 (genus 4,
#   non-Galois cubic cover -- involution-free bet);  C : t^3 = y (etale, genus 10).
#   Prym dim 6, signature (3,3), Q(zeta3)-multiplication.
#   s_k = #C(F_{p^k}) - #C'(F_{p^k}) = sum of 12 Frobenius eigenvalues^k.
# Newton -> e_1..e_6 (exact in QQ), functional equation e_{12-j} = p^{6-j} e_j -> P_B(T).
# Verdict: factor P_B over QQ.  Simple-candidate signature: no square factor, no low-degree
# split matching the decomposable (occ-18) pattern that killed the bielliptic route.

p = 7
c = 1
KMAX = 6

def counts(q):
    F = GF(q)
    R.<u> = PolynomialRing(F)
    three_div = (q - 1) % 3 == 0
    e3 = (q - 1) // 3 if three_div else None
    def n_t(y0):
        if y0 == 0:
            return 1
        if not three_div:
            return 1
        return 3 if y0**e3 == 1 else 0
    def n_cube(a):  # roots of t^3 = a
        return n_t(a) if a != 0 else 1
    sum_nt = 0; nCp = 0; nC = 0; nE0 = 1  # start with O
    # O contributions
    nuO = 1 + (2 if F(-1).is_square() else 0)
    ntO = n_cube(F(-1))
    sum_nt += ntO; nCp += nuO; nC += nuO * ntO
    two = F(2); four = F(4)
    for x in F:
        # y^2 + (2x+1) y - x^3 = 0
        b = two * x + 1; d = b*b + four * x**3
        if d == 0:
            ys = [-b / two]
        elif d.is_square():
            s = d.sqrt(); ys = [(-b + s)/two, (-b - s)/two]
        else:
            ys = []
        if not ys:
            continue
        nu = len((u**3 + x*u + c).roots(multiplicities=False))
        for y0 in ys:
            nE0 += 1
            nt = n_cube(F(1)) if (x == 0 and y0 == 0) else n_t(y0)  # T: leading 1/a3 = 1
            sum_nt += nt; nCp += nu; nC += nu * nt
    assert sum_nt == nE0, (q, sum_nt, nE0)   # cross-check A (3-isogeny)
    return nE0, nCp, nC

s = []
for k in range(1, KMAX + 1):
    q = p**k
    nE0, nCp, nC = counts(q)
    s.append(nCp - nC)   # Prym power sum: a_C(k) - a_C'(k) = #C' - #C  (Schoen convention)
    print(f"k={k} q={q}: #E0={nE0} #C'={nCp} #C={nC}  s_{k}={nCp-nC}")

# Newton's identities (power sums -> elementary symmetric), exact over QQ
e = [QQ(1)]
for k in range(1, KMAX + 1):
    acc = QQ(0)
    for i in range(1, k + 1):
        acc += (-1)**(i - 1) * e[k - i] * s[i - 1]
    e.append(acc / k)
# functional equation completes e_7..e_12
for j in range(7, 13):
    e.append(QQ(p)**(j - 6) * e[12 - j])
RZ.<T> = ZZ[]
P = RZ(sum((-1)**j * e[j] * T**j for j in range(13)))
print("\nP_B(T) =", P)
print("\nfactor over ZZ:", P.factor())
# Weil purity: roots at |r| = 1/sqrt(p), i.e. |r|^2 * p = 1 exactly
print("\n|roots|^2 * p (want all 1.000):",
      sorted(set(round(abs(r)**2 * p, 3) for r in P.roots(CC, multiplicities=False))))
