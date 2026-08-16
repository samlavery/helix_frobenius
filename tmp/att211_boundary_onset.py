"""att211: the boundary scalar at the onset. rem:selfcal predicts the continuation's
content enters through the ONE boundary channel h_n. Test: in the flipped chart
(positive pencil), compute h_n = (-1)[m_{2n} - sum w lam^{2n}] for n = 8..17 at
s0 = 0.9 and locate where h_n loses manifest positivity relative to the inertia
onset n_c (full chart n_c = 15)."""
from mpmath import mp, zeta, zetazero, diff, mpf, factorial, matrix, eig, lu_solve, inverse, mpc, nstr

mp.dps = 55
f_reg = lambda s: -zeta(s, derivative=1) / zeta(s) - 1 / (s - 1)
Z = [mpf(l.strip()) for l in open("tmp/zeros150_dps45.txt")]
print("loaded %d zeros" % len(Z), flush=True)

def mreg(s0, K):
    s0 = mpf(s0)
    out = [f_reg(s0)]
    for k in range(1, 9):
        out.append(((-1) ** k) * diff(f_reg, s0, k))
    a = s0 - mpf(1) / 2
    for k in range(9, K + 1):
        p = k + 1
        zsum = 2 * sum(((a - mpc(0, 1) * g) ** (-p)).real for g in Z)
        tsum = 2 ** (-p) * zeta(p, 1 + s0 / 2)
        out.append(-factorial(k) * (zsum + tsum))
    return out

s0 = 0.9
m = mreg(s0, 36)
mf = [-x for x in m]                      # flipped chart: positive pencil
print("n    h_n (flipped)         nodes real?   ")
for n in range(8, 18):
    G0 = matrix(n, n); G1 = matrix(n, n)
    for j in range(n):
        for k in range(n):
            G0[j, k] = mf[j + k]
            G1[j, k] = mf[j + k + 1]
    # generalized nodes: eig of G0^{-1} G1
    Ginv1 = inverse(G0) * G1
    E, _ = eig(Ginv1)
    lam = sorted(E, key=lambda z: z.real)
    nreal = sum(1 for z in lam if abs(z.imag) < 1e-25 * (1 + abs(z.real)))
    # weights from Vandermonde on the first n moments
    V = matrix(n, n)
    rhs = matrix(n, 1)
    for r in range(n):
        rhs[r, 0] = mf[r]
        for c in range(n):
            V[r, c] = lam[c] ** r
    w = lu_solve(V, rhs)
    S = sum(w[c, 0] * lam[c] ** (2 * n) for c in range(n))
    h = mf[2 * n] - S
    tag = "ALL REAL" if nreal == n else "%d real, %d complex" % (nreal, n - nreal)
    print("%2d   %-20s  %s" % (n, nstr(h, 6), tag), flush=True)
