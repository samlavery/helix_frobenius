"""att214: the conditioned frontier map -- inertia of the pole-subtracted pencil at
arithmetic-resolving dimension. Diagonal congruence D H D (unit diagonal) preserves
inertia and removes the k! dynamic range; dps 100 does the rest. Track the inertia
profile and the det-ratio (boundary-scalar) sign sequence across n at two depths."""
from mpmath import mp, zeta, diff, mpf, factorial, matrix, eigsy, mpc, sqrt, nstr

mp.dps = 100
KTOP = 64
f_reg = lambda s: -zeta(s, derivative=1) / zeta(s) - 1 / (s - 1)
Z = [mpf(l.strip()) for l in open("tmp/zeros150_dps45.txt")]
print("loaded %d zeros (dps45 ordinates; zero-sum terms k>=9 limited ~1e-44 rel)" % len(Z),
      flush=True)

def mreg(s0):
    s0 = mpf(s0)
    out = [f_reg(s0)]
    for k in range(1, 9):
        out.append(((-1) ** k) * diff(f_reg, s0, k))
    a = s0 - mpf(1) / 2
    for k in range(9, KTOP + 1):
        p = k + 1
        zsum = 2 * sum(((a - mpc(0, 1) * g) ** (-p)).real for g in Z)
        tsum = 2 ** (-p) * zeta(p, 1 + s0 / 2)
        out.append(-factorial(k) * (zsum + tsum))
    return out

for s0 in [0.9, 0.6]:
    print("\ns0 = %s" % s0, flush=True)
    m = mreg(s0)
    mf = [-x for x in m]                    # flipped chart
    for n in [16, 20, 24, 28, 32]:
        H = matrix(n, n)
        for j in range(n):
            for k in range(n):
                H[j, k] = mf[j + k]
        # diagonal congruence: D = diag(1/sqrt(|H_jj|))
        d = [1 / sqrt(abs(H[j, j])) for j in range(n)]
        S = matrix(n, n)
        for j in range(n):
            for k in range(n):
                S[j, k] = H[j, k] * d[j] * d[k]
        ev = eigsy(S, eigvals_only=True)
        npos = sum(1 for e in ev if e > 0)
        nneg = sum(1 for e in ev if e < 0)
        emin, emax = min(abs(e) for e in ev), max(abs(e) for e in ev)
        print("  n=%2d  inertia (%d,%d)   scaled |ev| in [%s, %s]"
              % (n, npos, nneg, nstr(emin, 3), nstr(emax, 3)), flush=True)
