# Eightfold flex construction: C' : u^3 - 3(1+x)^2 u + (2(1+x)^3 + y + 2x + 1) = 0
# over E0 : y^2 + 2xy + y = x^3;  C : t^3 = y.  Claimed g' = 5, Prym dim 8, sig (4,4).
#
# Stage 1 (p = 7): counts k = 1..6; FE-complete an assumed-degree-10 numerator from
#   k <= 5, purity check, AND overdetermination: predict #C'(F_{7^6}) from the poly,
#   compare to the actual count  ==> genus-5 certificate at full strength.
# Stage 2 (p = 7): counts of C up to k = 8; Prym power sums s_k = #C' - #C (Schoen
#   convention); Newton with g = 8 -> FE-complete deg-16 P_Prym; purity; factor over ZZ.
#   IRREDUCIBLE at the split prime 7  ==>  the eightfold is SIMPLE (any isogeny factor
#   over Q or over K = Q(sqrt(-3)) would factor P).
# Stage 3 (p = 13): genus-5 certificate cross-check (k <= 6).

def counts(p, k):
    q = p ^ k
    F = GF(q, 'g')
    R = PolynomialRing(F, 'U')
    U = R.gen()
    one_third = 3 if q % 3 == 1 else 1
    third = (q - 1) // 3 if q % 3 == 1 else 0
    nE0 = 1
    nCp = 0
    nC = 0
    for x0 in F:
        b = 2 * x0 + 1
        D = b * b + 4 * x0 ^ 3
        if D == 0:
            ys = [-b / 2]
        elif D.is_square():
            s = D.sqrt()
            ys = [(-b + s) / 2, (-b - s) / 2]
        else:
            ys = []
        for y0 in ys:
            nE0 += 1
            f = U ^ 3 - 3 * (1 + x0) ^ 2 * U + (2 * (1 + x0) ^ 3 + y0 + 2 * x0 + 1)
            nu = len(f.roots(multiplicities=False))
            if y0 == 0:
                nt = one_third
            elif q % 3 == 1:
                nt = 3 if y0 ^ third == 1 else 0
            else:
                nt = 1
            nCp += nu
            nC += nu * nt
    nCp += 2                      # O: e=2 place + unramified slope-2 branch
    nC += 2 * one_third
    return nE0, nCp, nC


def fe_lpoly_from_powersums(p, s, g):
    # s[k-1] = power sum of the 2g Frobenius roots, k = 1..g; FE-complete.
    e = [1] + [0] * g
    for k in range(1, g + 1):
        acc = 0
        for i in range(1, k + 1):
            acc += (-1) ^ (i - 1) * e[k - i] * s[i - 1]
        e[k] = acc / k
    c = [0] * (2 * g + 1)
    for j in range(g + 1):
        c[j] = (-1) ^ j * e[j]
    for j in range(g):
        c[2 * g - j] = p ^ (g - j) * c[j]
    S = PolynomialRing(QQ, 'T')
    T = S.gen()
    return sum(QQ(c[j]) * T ^ j for j in range(2 * g + 1))


def purity(P, p):
    rts = P.change_ring(CDF).roots(multiplicities=False)
    return all(abs(abs(r) ^ 2 * p - 1) < 1e-6 for r in rts), \
        sorted(set(round(abs(r) ^ 2 * p, 3) for r in rts))


print("=" * 60)
print("STAGE 1+2: p = 7, k = 1..8")
NsC, NsCp = [], []
for k in range(1, 9):
    nE0, nCp, nC = counts(7, k)
    NsCp.append(nCp)
    NsC.append(nC)
    print(f"k={k} q={7^k}: #E0={nE0} #C'={nCp} #C={nC}  s_k={nCp - nC}")
    sys.stdout.flush()

tC = [7 ^ k + 1 - NsCp[k - 1] for k in range(1, 6)]
P5 = fe_lpoly_from_powersums(7, tC, 5)
ok5, pur5 = purity(P5, 7)
print("P_C'(T) deg", P5.degree(), ":", P5)
print("|root|^2 * 7:", pur5, "->", "PASS" if ok5 else "FAIL")
# overdetermination: predict #C'(F_{7^6}) from P5
S = PolynomialRing(QQ, 'T')
T = S.gen()
alpha_pows6 = sum(r ^ 6 for r in P5.change_ring(CDF).roots(multiplicities=False))
pred6 = 7 ^ 6 + 1 - alpha_pows6.real()
print(f"overdetermination k=6: predicted #C' = {pred6:.2f}, actual = {NsCp[5]}",
      "PASS" if abs(pred6 - NsCp[5]) < 0.5 else "FAIL")
print("GENUS 5 CERTIFICATE (p=7):",
      "PASS" if ok5 and abs(pred6 - NsCp[5]) < 0.5 else "FAIL")
print("factor over ZZ:", factor(P5))
sys.stdout.flush()

sPrym = [NsCp[k - 1] - NsC[k - 1] for k in range(1, 9)]
print("Prym power sums s_1..s_8:", sPrym)
PP = fe_lpoly_from_powersums(7, sPrym, 8)
okP, purP = purity(PP, 7)
print("P_Prym(T) deg", PP.degree(), ":", PP)
print("|root|^2 * 7:", purP, "->", "PASS" if okP else "FAIL")
fac = factor(PP)
print("factor over ZZ:", fac)
irr = len(list(fac)) == 1 and fac[0][1] == 1
print("SIMPLICITY CERTIFICATE (deg-16 irreducible at split p=7):",
      "PASS -- SIMPLE ABELIAN EIGHTFOLD" if irr else "NOT IRREDUCIBLE -- inspect")
sys.stdout.flush()

print("=" * 60)
print("STAGE 3: p = 13 genus-5 cross-check, k = 1..6")
Ns13 = []
for k in range(1, 7):
    nE0, nCp, nC = counts(13, k)
    Ns13.append(nCp)
    print(f"k={k} q={13^k}: #E0={nE0} #C'={nCp} #C={nC}  s_k={nCp - nC}")
    sys.stdout.flush()
t13 = [13 ^ k + 1 - Ns13[k - 1] for k in range(1, 6)]
Q5 = fe_lpoly_from_powersums(13, t13, 5)
ok13, pur13 = purity(Q5, 13)
alpha6 = sum(r ^ 6 for r in Q5.change_ring(CDF).roots(multiplicities=False))
pred = 13 ^ 6 + 1 - alpha6.real()
print("P_C'(T):", Q5)
print("|root|^2 * 13:", pur13)
print(f"overdetermination k=6: predicted {pred:.2f}, actual {Ns13[5]}")
print("GENUS 5 CERTIFICATE (p=13):",
      "PASS" if ok13 and abs(pred - Ns13[5]) < 0.5 else "FAIL")
print("factor over ZZ:", factor(Q5))
