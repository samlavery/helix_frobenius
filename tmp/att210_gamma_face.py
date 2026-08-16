"""att210: the gamma-face of the event. FE-paired hermitian form
   A_jk = sum_rho (s0-rho)^{-(j+1)} (s0-1+rho)^{-(k+1)},
hermitian by conjugation-closure; on-line atoms contribute |P(rho)|^2 (PSD),
off-line pairs are sign-free (the Weil/nullflow pair mechanism in the w-chart).
Same data and dimensions as the x-face event (att207-209): compare inertia."""
from mpmath import mp, zetazero, mpf, mpc, matrix, eighe, mpf as _m, nstr

mp.dps = 40
NZ = 150
G = [mpf(l.strip()) for l in open("tmp/zeros150_dps45.txt")]
print("loaded %d zeros" % len(G), flush=True)

for s0 in [0.999, 0.9, 0.6]:
    s = mpf(s0)
    for n in [8, 12, 16, 17]:
        A = matrix(n, n)
        for j in range(n):
            for k in range(n):
                tot = mpc(0)
                for g in G:
                    for sgn in (1, -1):        # rho = 1/2 + i sgn g
                        rho = mpc(mpf(1) / 2, sgn * g)
                        tot += (s - rho) ** (-(j + 1)) * (s - 1 + rho) ** (-(k + 1))
                A[j, k] = tot
        # hermitian: symmetrize tiny asymmetry from truncation, take real eigs
        Ah = (A + A.transpose_conj()) / 2
        ev = [e.real for e in eighe(Ah, eigvals_only=True)]
        npos = sum(1 for e in ev if e > 0)
        nneg = sum(1 for e in ev if e < 0)
        emin = min(ev)
        print("s0=%-6s n=%2d  gamma-face inertia (%d,%d)  min-eig %s"
              % (s0, n, npos, nneg, nstr(emin, 4)), flush=True)
