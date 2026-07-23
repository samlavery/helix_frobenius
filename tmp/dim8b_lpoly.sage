# Dim-8 re-roll verdict tower.  Usage: sage tmp/dim8b_lpoly.sage al be ga a_num a_den
# C' : u^3 + al*x^2*u + (x*y + be*y + ga*x + a) = 0 over E0;  C : t^3 = y.
# Stage 1: p=7 k=1..6: genus-5 certificate with the CORRECT overdetermination
#   (power-sum recurrence: p_k = e1 p_{k-1} - ... , NOT roots of the printed poly).
# Stage 2: p=7 k=7,8: deg-16 P_Prym via Newton+FE; purity; factor over ZZ ==>
#   SIMPLICITY verdict.  O-fiber: unramified, n_u(O) = 1 + 2*[-al is a QR];
#   n_t per O-branch = gcd(3, q-1)-style (y-leading -1 = cube).

import sys
args = sys.argv[1:]
AL, BE, GA = ZZ(args[0]), ZZ(args[1]), ZZ(args[2])
A_ = QQ(args[3]) / QQ(args[4])
print(f"family: al={AL} be={BE} ga={GA} a={A_}")


def counts(p, k):
    q = p ^ k
    F = GF(q, 'g')
    R = PolynomialRing(F, 'U')
    U = R.gen()
    one_third = 3 if q % 3 == 1 else 1
    third = (q - 1) // 3 if q % 3 == 1 else 0
    al, be, ga, aa = F(AL), F(BE), F(GA), F(A_)
    nCp = nC = 0
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
            f = U ^ 3 + al * x0 ^ 2 * U + (x0 * y0 + be * y0 + ga * x0 + aa)
            nu = len(f.roots(multiplicities=False))
            if y0 == 0:
                nt = one_third
            elif q % 3 == 1:
                nt = 3 if y0 ^ third == 1 else 0
            else:
                nt = 1
            nCp += nu
            nC += nu * nt
    nuO = 1 + (2 if (-al).is_square() else 0)
    nCp += nuO
    nC += nuO * one_third
    return nCp, nC


def newton_e(tpow, g):
    e = [QQ(1)] + [QQ(0)] * g
    for k in range(1, g + 1):
        acc = QQ(0)
        for i in range(1, k + 1):
            acc += (-1) ^ (i - 1) * e[k - i] * tpow[i - 1]
        e[k] = acc / k
    return e


def fe_extend(e, p, g):
    # full elementary symmetric list e_0..e_{2g} via FE c_{2g-j} = p^{g-j} c_j,
    # c_j = (-1)^j e_j
    c = [(-1) ^ j * e[j] for j in range(g + 1)] + [0] * g
    for j in range(g):
        c[2 * g - j] = p ^ (g - j) * c[j]
    return [(-1) ^ j * c[j] for j in range(2 * g + 1)], c


def powersum_extend(e_full, tpow, upto):
    # p_k = sum_{i<k} (-1)^{i-1} e_i p_{k-i} + (-1)^{k-1} k e_k  (k <= deg)
    ps = list(tpow)
    n = len(e_full) - 1
    for k in range(len(ps) + 1, upto + 1):
        acc = QQ(0)
        for i in range(1, min(k, n) + 1):
            acc += (-1) ^ (i - 1) * e_full[i] * (ps[k - i - 1] if k - i >= 1 else 0)
        if k <= n:
            acc += (-1) ^ (k - 1) * k * e_full[k]
        ps.append(acc)
    return ps


p = 7
NsCp, NsC = [], []
for k in range(1, 9):
    nCp, nC = counts(p, k)
    NsCp.append(nCp)
    NsC.append(nC)
    print(f"k={k} q={p^k}: #C'={nCp} #C={nC} s_k={nCp - nC}")
    sys.stdout.flush()
    if k == 6:
        t5 = [p ^ j + 1 - NsCp[j - 1] for j in range(1, 6)]
        e5 = newton_e(t5, 5)
        eF, cF = fe_extend(e5, p, 5)
        ps = powersum_extend(eF, t5, 6)
        pred = p ^ 6 + 1 - ps[5]
        ok = (pred == NsCp[5])
        print(f"GENUS 5 CERTIFICATE: predicted #C'(7^6) = {pred}, actual = "
              f"{NsCp[5]} -> {'PASS' if ok else 'FAIL'}")
        S = PolynomialRing(QQ, 'T')
        T = S.gen()
        P5 = sum(QQ(cF[j]) * T ^ j for j in range(11))
        rts = P5.change_ring(CDF).roots(multiplicities=False)
        print("purity:", "PASS" if all(abs(abs(r) ^ 2 * p - 1) < 1e-6 for r in rts)
              else "FAIL")
        sys.stdout.flush()

sPrym = [NsCp[j] - NsC[j] for j in range(8)]
print("Prym power sums:", sPrym)
e8 = newton_e(sPrym, 8)
eF, cF = fe_extend(e8, p, 8)
S = PolynomialRing(QQ, 'T')
T = S.gen()
PP = sum(QQ(cF[j]) * T ^ j for j in range(17))
print("P_Prym:", PP)
rts = PP.change_ring(CDF).roots(multiplicities=False)
print("purity:", "PASS" if all(abs(abs(r) ^ 2 * p - 1) < 1e-6 for r in rts) else "FAIL")
fac = factor(PP)
print("factor over ZZ:", fac)
irr = len(list(fac)) == 1 and fac[0][1] == 1
print("SIMPLICITY:", "PASS -- SIMPLE ABELIAN EIGHTFOLD, the pipeline inherits"
      if irr else "NOT SIMPLE -- decomposition, diagnose correspondence")
