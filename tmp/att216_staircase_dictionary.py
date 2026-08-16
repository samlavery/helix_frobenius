"""att216: staircase dictionary test (pre-registered, ledger 214). At s0=0.9, n=32
the flipped pencil has TWO negative directions. Decompose each direction's energy
v^T H v = (trivial part) + sum_j c_j(v),  c_j = 2 Re sum_{k,l} v_k v_l (k+l)!/(s0-rho_j)^{k+l+1}.
Prediction: direction 1 dominated by gamma_1 = 14.13, direction 2 by gamma_2 = 21.02."""
from mpmath import mp, zeta, diff, mpf, factorial, matrix, eigsy, mpc, sqrt, nstr

mp.dps = 100
N = 32
KTOP = 2 * N
S0 = mpf("0.9")
f_reg = lambda s: -zeta(s, derivative=1) / zeta(s) - 1 / (s - 1)
Z = [mpf(l.strip()) for l in open("tmp/zeros150_dps45.txt")]

m = [f_reg(S0)]
for k in range(1, 9):
    m.append(((-1) ** k) * diff(f_reg, S0, k))
a = S0 - mpf(1) / 2
for k in range(9, KTOP + 1):
    p = k + 1
    zsum = 2 * sum(((a - mpc(0, 1) * g) ** (-p)).real for g in Z)
    tsum = 2 ** (-p) * zeta(p, 1 + S0 / 2)
    m.append(-factorial(k) * (zsum + tsum))
mf = [-x for x in m]

H = matrix(N, N)
for j in range(N):
    for k in range(N):
        H[j, k] = mf[j + k]
d = [1 / sqrt(abs(H[j, j])) for j in range(N)]
S = matrix(N, N)
for j in range(N):
    for k in range(N):
        S[j, k] = H[j, k] * d[j] * d[k]
E, Q = eigsy(S)
neg = [i for i in range(N) if E[i] < 0]
print("negative scaled eigenvalues:", [nstr(E[i], 4) for i in neg], flush=True)

for idx, i0 in enumerate(neg):
    v = [Q[j, i0] * d[j] for j in range(N)]        # unscaled polynomial coeffs
    tot = sum(v[j] * H[j, k] * v[k] for j in range(N) for k in range(N))
    contrib = []
    for jz in range(12):
        rho = mpc(mpf(1) / 2, Z[jz])
        s = mpc(0)
        for k in range(N):
            for l in range(N):
                s += v[k] * v[l] * factorial(k + l) * (S0 - rho) ** (-(k + l + 1))
        contrib.append(2 * s.real)
    triv = tot - sum(contrib) - 2 * sum(
        sum(v[k] * v[l] * factorial(k + l) *
            ((a - mpc(0, 1) * g) ** (-(k + l + 1))).real
            for k in range(N) for l in range(N)) for g in Z[12:])
    print("\ndirection %d  (v^T H v = %s):" % (idx + 1, nstr(tot, 4)), flush=True)
    print("  trivial+tail part: %s" % nstr(triv, 4))
    for jz in range(6):
        print("  c_%d (gamma=%.3f): %s" % (jz + 1, float(Z[jz]), nstr(contrib[jz], 4)))
