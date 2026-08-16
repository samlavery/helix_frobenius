"""att207: push the frontier map past the double-precision wall.
Hybrid jets at high precision: k<=8 direct diff of f_reg; k>=9 Hadamard zero-sum
(converges ~ gamma^{-(k+1)}: 150 zeros ample) + EXACT trivial part via Hurwitz zeta:
   sum_{m>=1} (s0+2m)^{-p} = 2^{-p} * zeta(p, 1+s0/2).
Inertia via mp.eigsy at dps 50. Question: does definiteness persist toward
arithmetic-resolving n, and which feature (primes vs zeros) breaks it first?"""
from mpmath import mp, zeta, zetazero, diff, mpf, factorial, matrix, eigsy, mpc

mp.dps = 50
NZ = 150
KTOP = 32
f_reg = lambda s: -zeta(s, derivative=1) / zeta(s) - 1 / (s - 1)

print("computing %d zeros at dps %d..." % (NZ, mp.dps), flush=True)
Z = [zetazero(j).imag for j in range(1, NZ + 1)]
print("done; gamma_max = %s" % mp.nstr(Z[-1], 8), flush=True)


def mreg(s0, K):
    s0 = mpf(s0)
    out = [(-1) ** 0 * f_reg(s0)]
    for k in range(1, min(K, 8) + 1):
        out.append(((-1) ** k) * diff(f_reg, s0, k))
    a = s0 - mpf(1) / 2
    for k in range(9, K + 1):
        p = k + 1
        zsum = 2 * sum(((a - mpc(0, 1) * g) ** (-p)).real for g in Z)
        tsum = 2 ** (-p) * zeta(p, 1 + s0 / 2)
        out.append(-factorial(k) * (zsum + tsum))
    return out


for s0 in [0.999, 0.6]:
    m = mreg(s0, KTOP)
    print("\ns0 = %s" % s0, flush=True)
    for n in [10, 12, 14, 16]:
        H = matrix(n, n)
        for j in range(n):
            for k in range(n):
                H[j, k] = m[j + k]
        ev = eigsy(H, eigvals_only=True)
        npos = sum(1 for e in ev if e > 0)
        nneg = sum(1 for e in ev if e < 0)
        small = min(abs(e) for e in ev)
        big = max(abs(e) for e in ev)
        print("  n=%2d  inertia (%d,%d)   |ev| range [%s, %s]"
              % (n, npos, nneg, mp.nstr(small, 3), mp.nstr(big, 3)), flush=True)
