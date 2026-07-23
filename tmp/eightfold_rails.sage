# Rail-native reading for the EIGHTFOLD (flex construction), sigma-twisted counts.
# C' : u^3 - 3(1+x)^2 u + (2(1+x)^3 + y + 2x + 1) = 0 over E0;  C : t^3 = y.
# Rail V_omega has dim 8 (g_C - g_C' = 13 - 5).  T_1(k) for k = 1..8 at p = 7 ->
# Newton over Q(zeta_3) -> f_omega deg 8 in Z[zeta_3][T].
# Cross-checks: sum_m = 3#C'; T_0 = C'-trace; integrality; f*fbar == P_Prym (from
# tmp/eightfold_lpoly.log); purity.  FREEZE: r = e_8/p^4 in mu_6?
# Smooth-model conventions (validated on the sixfold): T-points (y=0): 3 points each,
# bin 0; O: e=2 place + unram branch, y-leading = -(cube): each 3 points, bin 0.
import re

K = CyclotomicField(3, 'w')
w = K.gen()


def zeta_int(p):
    for z in range(2, p):
        if (z * z + z + 1) % p == 0:
            return z
    raise ValueError


def twisted_counts(p, k):
    q = p ^ k
    F = GF(q, 'g')
    R = PolynomialRing(F, 'U')
    U = R.gen()
    z = F(zeta_int(p))
    zpow = [F(1), z, z * z]
    e3 = (q - 1) // 3
    nCp = 0
    Cm = [0, 0, 0]
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
            f = U ^ 3 - 3 * (1 + x0) ^ 2 * U + (2 * (1 + x0) ^ 3 + y0 + 2 * x0 + 1)
            nu = len(f.roots(multiplicities=False))
            nCp += nu
            if y0 == 0:
                Cm[0] += 3 * nu
            else:
                c = y0 ^ e3
                m = zpow.index(c)
                Cm[m] += 3 * nu
    nCp += 2                 # O: e=2 place + unramified slope-2 branch
    Cm[0] += 6               # each carries 3 C-points, y-leading = -(cube): bin 0
    return nCp, Cm


def newton_charpoly(T1, d):
    e = [K(1)] + [K(0)] * d
    for k in range(1, d + 1):
        acc = K(0)
        for i in range(1, k + 1):
            acc += (-1) ^ (i - 1) * e[k - i] * T1[i - 1]
        e[k] = acc / k
    S = PolynomialRing(K, 'T')
    T = S.gen()
    return sum((-1) ^ j * e[j] * T ^ (d - j) for j in range(d + 1)), e


p = 7
print("EIGHTFOLD RAILS  p = 7, k = 1..8")
T1 = []
ok_conv = True
for k in range(1, 9):
    nCp, Cm = twisted_counts(p, k)
    q = p ^ k
    S = [q + 1 - Cm[m] for m in range(3)]
    okSum = (sum(Cm) == 3 * nCp)
    t0 = (S[0] + S[1] + S[2]) / 3
    t1 = (S[0] + w ^ (-1) * S[1] + w ^ (-2) * S[2]) / 3
    ok_conv = ok_conv and okSum and (t0 == q + 1 - nCp)
    T1.append(t1)
    print(f"k={k}: #C'={nCp} C_m={Cm} sum={'OK' if okSum else 'FAIL'} "
          f"T0={t0} (C': {q + 1 - nCp})")
    sys.stdout.flush()
print("conventions:", "PASS" if ok_conv else "FAIL")

f, e = newton_charpoly(T1, 8)
print("rail char poly f_omega(T) =", f)
print("coefficients integral:", "PASS" if all(c.is_integral()
      for c in f.coefficients()) else "FAIL")
fbar = f.map_coefficients(lambda c: c.conjugate())
prod = f * fbar
SQ = PolynomialRing(QQ, 'T')
prodQ = SQ([QQ(c) for c in prod.list()])
try:
    txt = open('tmp/eightfold_lpoly.log').read()
    m = re.search(r'P_Prym\(T\) deg 16 : (.*)', txt)
    T = SQ.gen()
    PP = SQ(sage_eval(m.group(1), locals={'T': T}))
    PPrev = SQ(list(reversed(PP.list())))
    PPrev = PPrev / PPrev.leading_coefficient()
    print("f * fbar == P_Prym (monic reciprocal):",
          "PASS" if prodQ == PPrev else "FAIL")
except Exception as ex:
    print("P_Prym cross-check skipped:", ex)
e8 = e[8]
r = e8 / p ^ 4
print("det(Frob | V_omega) = e_8 =", e8)
units = {K(1): "+1", K(-1): "-1", w: "+w", -w: "-w", w ^ 2: "+w^2", -w ^ 2: "-w^2"}
if r in units:
    print(f"*** FREEZE: r = e_8/p^4 = {units[K(r)]}  (mu_6 unit; ORDER LAW)")
else:
    rn = CDF(K(r).complex_embedding())
    print(f"no mu_6 freeze: r = {r}, |r| = {abs(rn):.6f}, "
          f"arg/(pi/3) = {rn.arg() / (pi / 3).n():.4f}")
rts = [CDF(rr[0]) for rr in f.change_ring(CDF).roots()]
print("rail purity:", "PASS" if all(abs(abs(r0) ^ 2 / p - 1) < 1e-6 for r0 in rts)
      else "FAIL")
# One-prime End sharpening: irreducibility of f_omega over Q(zeta_3)
print("f_omega irreducible over Q(zeta_3):",
      "PASS" if f.is_irreducible() else "FACTORS: " + str(f.factor()))
