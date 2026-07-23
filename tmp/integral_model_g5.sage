# Integral cut-and-glue model, generalized to arbitrary base genus g' = h + 1:
# n sheets, h handle pairs per sheet, plus (atil, beta).  Here: n = 3, g' = 5
# (the dim-8 target): verify IN ADVANCE (topological, curve-independent):
#   (a) Prym polarization type (1,1,1,1,3,3,3,3)  =>  m = 4 in-house (L-O: n occurs
#       g'-1 = 4 times);
#   (b) the dim-8 battery identity Pf(sE + tE_V) = s^5 (s+t)^8  =>  q_k = k! C(8,k).

def build_g(n, h):
    N = 2 * h * n + 2
    E = matrix(ZZ, N, N)
    for i in range(n):
        for j in range(h):
            r = 2 * h * i + 2 * j
            E[r, r + 1] = 1
            E[r + 1, r] = -1
    E[N - 2, N - 1] = 1
    E[N - 1, N - 2] = -1
    S = matrix(ZZ, N, N)
    for i in range(n):
        for j in range(h):
            for e in range(2):
                S[2 * h * ((i + 1) % n) + 2 * j + e, 2 * h * i + 2 * j + e] = 1
    S[N - 2, N - 2] = 1
    S[N - 1, N - 1] = 1
    nc = 2 * h + 2
    P = matrix(ZZ, nc, N)
    for i in range(n):
        for j in range(h):
            P[2 + 2 * j, 2 * h * i + 2 * j] = 1
            P[3 + 2 * j, 2 * h * i + 2 * j + 1] = 1
    P[0, N - 2] = 1
    P[1, N - 1] = n
    Ep = matrix(ZZ, nc, nc)
    for j in range(h + 1):
        Ep[2 * j, 2 * j + 1] = 1
        Ep[2 * j + 1, 2 * j] = -1
    return N, E, S, P, Ep


n, h = 3, 4                      # g' = 5, Prym dim 2(g'-1) = 8
N, E, S, P, Ep = build_g(n, h)
ok = (abs(E.det()) == 1 and S.transpose() * E * S == E
      and S ^ n == identity_matrix(N) and P * S == P)
print(f"g'={h+1}, n={n}: gates:", "PASS" if ok else "FAIL")
V = P.right_kernel().basis_matrix()
G = V * E * V.transpose()
d = [x for x in G.elementary_divisors() if x != 0]
half = sorted(d)[::2]
print("Prym lattice rank", V.nrows(), " type", half, " Pf =", prod(half))
print("(a) m = 4 in-house:", "PASS" if half == [1, 1, 1, 1, 3, 3, 3, 3] else "MISMATCH")
R = PolynomialRing(QQ, ['s', 't'])
s, t = R.gens()
Q = P.transpose() * Ep * P
EV = matrix(QQ, E) - matrix(QQ, Q) / 3
M = s * matrix(R, E) + t * matrix(R, N, N, [R(x) for x in EV.list()])
pf = M.pfaffian()
print("(b) Pf(sE + tE_V) =", factor(pf), "->",
      "PASS: dim-8 battery q_k = k! C(8,k) VERIFIED" if pf in
      (s ^ 5 * (s + t) ^ 8, -s ^ 5 * (s + t) ^ 8) else "MISMATCH")
