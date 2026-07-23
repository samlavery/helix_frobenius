# EXACT integral homology models for cyclic etale covers of a genus-4 curve.
# Cut-and-glue: cut C' along a_1 (genus drops to 3, two boundary circles), take n
# cyclically glued sheets.  H_1(C,Z) basis: per sheet i the six handle classes
# a_j^(i), b_j^(i) (j = 2,3,4), plus the gluing-circle class atil (all n gluing
# circles are homologous) and the long lift beta of b_1 (crosses each circle once).
# Unimodular: 3n handle pairs + (atil, beta).  sigma: sheet shift, fixes atil, beta.
# pi_*: handles -> handles, atil -> a_1, beta -> n*b_1.
# Uniqueness of the topological type: MCG acts transitively on primitive H^1(Z/n)
# classes (Sp(Z/n)-transitivity), so this IS the tower's (C, sigma) for n = 3, 6.
#
# TASK 1 (n = 3, the mu_3 sixfold battery):
#   (a) SNF of E on V = ker pi_*  -> polarization type; expect (1,1,1,3,3,3): m = 3
#       verified IN-HOUSE (independent of Lange-Ortega).
#   (b) Pf(s E + t E_V) with E_V = E - Q/3, Q = pi_*^T E' pi_*: expect s^4 (s+t)^6
#       -> THE BATTERY q_k = k! C(6,k) verified exactly (modulo classical Poincare).
# TASK 2 (n = 6, the mu6 tower):
#   (c) L-O cross-check: SNF of E on full ker pi_* (rank 30): expect (1^12, 6^3).
#   (d) THE VERDICT: SNF of E on Lambda_6 = ker Psi_6(sigma), Psi_6 = Phi1*Phi2*Phi3
#       = t^4 + t^3 - t - 1  (the chi-primitive B6 lattice, Z[zeta_6]-free rank 6):
#       v_2(prod d_i) ODD  ==> disc not in +-Nm (2 inert in Q(sqrt-3)) ==> NON-SPLIT.
#   (e) companions: Lambda_3 = ker(t^4 - t^3 + t - 1), Lambda_2 = ker(t^5 - t^4 +
#       t^3 - t^2 + t - 1).

def build(n):
    N = 6 * n + 2
    E = matrix(ZZ, N, N)
    for i in range(n):
        for j in range(3):
            E[6*i + 2*j, 6*i + 2*j + 1] = 1
            E[6*i + 2*j + 1, 6*i + 2*j] = -1
    E[N-2, N-1] = 1
    E[N-1, N-2] = -1
    S = matrix(ZZ, N, N)
    for i in range(n):
        for j in range(3):
            for e in range(2):
                S[6*((i+1) % n) + 2*j + e, 6*i + 2*j + e] = 1
    S[N-2, N-2] = 1
    S[N-1, N-1] = 1
    P = matrix(ZZ, 8, N)          # to (a1,b1,a2,b2,a3,b3,a4,b4)
    for i in range(n):
        for j in range(3):
            P[2 + 2*j, 6*i + 2*j] = 1
            P[3 + 2*j, 6*i + 2*j + 1] = 1
    P[0, N-2] = 1
    P[1, N-1] = n
    Ep = matrix(ZZ, 8, 8)
    for j in range(4):
        Ep[2*j, 2*j+1] = 1
        Ep[2*j+1, 2*j] = -1
    return N, E, S, P, Ep


def sanity(n, N, E, S, P, Ep):
    ok = True
    ok &= (abs(E.det()) == 1)
    ok &= (S.transpose() * E * S == E)
    ok &= (S ^ n == identity_matrix(N))
    ok &= (P * S == P)
    print(f"n={n}: unimodular/symplectic-sigma/order/equivariance:",
          "PASS" if ok else "FAIL")
    return ok


def sub_snf(E, B, label):
    G = B * E * B.transpose()
    d = G.smith_form(transformation=False)[0] if False else G.elementary_divisors()
    d = [x for x in d if x != 0]
    pairs = sorted(set(d))
    from collections import Counter
    cnt = Counter(d)
    prod_type = prod([x for x in d]) if d else 1
    # symplectic type: divisors come in pairs (d_i, d_i); Pf = product over one of each pair
    half = sorted(d)[::2]
    Pf = prod(half)
    print(f"{label}: rank {B.nrows()}, elementary divisors {dict(cnt)}, "
          f"type {half}, Pf = {Pf} = {factor(Pf) if Pf > 1 else 1}")
    return half, Pf


print("=" * 70)
print("TASK 1: n = 3 (the mu_3 sixfold battery verification)")
N, E, S, P, Ep = build(3)
sanity(3, N, E, S, P, Ep)
V = P.right_kernel().basis_matrix()
half, Pf = sub_snf(E, V, "V = ker pi_* (Prym lattice)")
print("   expected type (1,1,1,3,3,3), Pf = 27  ->",
      "PASS: m = 3 VERIFIED IN-HOUSE" if half == [1, 1, 1, 3, 3, 3] else "MISMATCH")
# battery: E_V = E - Q/3 over QQ, Pf(s E + t E_V)
R = PolynomialRing(QQ, ['s', 't'])
s, t = R.gens()
Q = P.transpose() * Ep * P
EV = matrix(QQ, E) - matrix(QQ, Q) / 3
# checks: E_V = E on V, E_V = 0 on H' = im(pi^*)
pistar = matrix(ZZ, N, 8)
for j in range(4):
    pass
# build pi^*: a1 -> 3*atil? NO: pi^* a1 = sum of gluing circles = 3*atil; b1 -> beta;
# a_{j+2} -> sum over sheets
pistar = matrix(ZZ, N, 8)
pistar[N-2, 0] = 3
pistar[N-1, 1] = 1
for i in range(3):
    for j in range(3):
        pistar[6*i + 2*j, 2 + 2*j] = 1
        pistar[6*i + 2*j + 1, 3 + 2*j] = 1
chk1 = (V * (EV - matrix(QQ, E)) == 0)
chk2 = (pistar.transpose() * EV * pistar == 0)
print("   adjunction: E_V = E on V:", "PASS" if chk1 else "FAIL",
      "| E_V = 0 on H':", "PASS" if chk2 else "FAIL")
M = s * matrix(R, E) + t * matrix(R, N, N, [R(x) for x in EV.list()])
pf = M.pfaffian()
print("   Pf(sE + tE_V) =", factor(pf))
print("   BATTERY:", "PASS -- q_k = k! C(6,k) VERIFIED"
      if pf in (s^4 * (s+t)^6, -s^4 * (s+t)^6) else "MISMATCH")

print("=" * 70)
print("TASK 2: n = 6 (the mu6 tower glue verdict)")
N, E, S, P, Ep = build(6)
sanity(6, N, E, S, P, Ep)
Vfull = P.right_kernel().basis_matrix()
half, Pf = sub_snf(E, Vfull, "full Prym ker pi_* (rank 30)")
print("   Lange-Ortega n=6 predicts type (1^12, 6^3), Pf = 216  ->",
      "PASS: model validated at n=6" if half == [1]*12 + [6]*3 else "MISMATCH")
T = S  # sigma
x = polygen(ZZ)
pieces = {
    "Lambda_6 (B6, chi-primitive -- THE VERDICT)": x^2 - x + 1,
    "Lambda_3 (B3, mu_3 piece)": x^2 + x + 1,
    "Lambda_2 (B2, Z/2 piece)": x + 1,
}
for label, psi in pieces.items():
    Mpsi = sum(ZZ(c) * T^k for k, c in enumerate(psi.list()))
    L = Mpsi.right_kernel().basis_matrix()
    half, Pf = sub_snf(E, L, label)
    if "VERDICT" in label:
        v2 = Pf.valuation(2)
        v3 = Pf.valuation(3)
        print(f"   *** Pf(E|B6-lattice) = {factor(Pf)}: v_2 = {v2}, v_3 = {v3}")
        print("   *** NON-SPLIT VERDICT (v_2 odd => disc not in +-Nm, 2 inert):",
              "NON-SPLIT -- BEYOND MARKMAN" if v2 % 2 == 1 else
              "split-class (v_2 even)")
