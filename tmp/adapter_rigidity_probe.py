#!/usr/bin/env python3
"""Phase 2a: rigidity/corank of the Sym^r reflection -- numerical Hamburger.

How much of the coefficient sequence does the rank Gamma-stack FE alone pin
down?  Build the linear map A : (c_n)_{n<=N} -> (D(x_i))_{i<=M} where
D = c-closure defect with the Sym^r stack and measured eps; SVD; count the
numerical nullity; check the true lambda_r line lies in the nullspace.
The deficiency (nullity as N grows) is the empirical information gap the
converse theorem's twist family must close.  Truncation-honest reading:
nullity counts sequences supported on n<=N satisfying the windowed FE --
a proxy for the infinite-dimensional question, stated as such.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
from adapter_sym_probe import tau_coeffs, sym_coeffs, gammaR_params, kernel_factory

mp.mp.dps = 30

def build(r, N, M, eps, delta=1):
    K = kernel_factory(gammaR_params(r, delta))
    xs = [mp.mpf(1) + mp.mpf('0.8') * i / (M - 1) for i in range(M)]
    A = mp.zeros(M, N)
    for i, x in enumerate(xs):
        for n in range(1, N + 1):
            A[i, n - 1] = K(n / x) - eps * x * K(n * x)
    return A

def run(r, N, eps, delta=1):
    M = 2 * N
    print(f"# rigidity probe Sym^{r}, N={N}, M={M}, eps={eps}")
    A = build(r, N, M, eps, delta)
    U, S, V = mp.svd_r(A)
    svals = [S[i] for i in range(N)]
    smax = svals[0]
    print("#  top sv:", mp.nstr(smax, 5))
    print("#  last 8 sv/smax:", [mp.nstr(s / smax, 3) for s in svals[-8:]])
    for thresh in ('1e-8', '1e-14', '1e-20'):
        t = mp.mpf(thresh)
        nullity = sum(1 for s in svals if s / smax < t)
        print(f"#  nullity(rel<{thresh}): {nullity} / {N}")
    tau = tau_coeffs(N)
    if r > 1:
        lam = sym_coeffs(r, N, tau)
    else:
        KM1 = 11
        lam = [mp.mpf(0)] + [mp.mpf(tau[n]) / mp.mpf(n) ** (mp.mpf(KM1) / 2)
                             for n in range(1, N + 1)]
    v = mp.matrix(N, 1)
    for n in range(1, N + 1):
        v[n - 1] = lam[n]
    Av = A * v
    print("#  true-vector rel residual:", mp.nstr(mp.norm(Av) / (smax * mp.norm(v)), 4))

if __name__ == '__main__':
    r = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    eps = int(sys.argv[3]) if len(sys.argv) > 3 else -1
    delta = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    run(r, N, eps, delta)
