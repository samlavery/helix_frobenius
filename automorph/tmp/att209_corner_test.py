"""att209: is the exit map's sole inertia event the RENORMALIZED CORNER?
The k>=1 jets are exact Laplace moments of the trivial+zero density; the k=0 entry
is renormalized (the density mass diverges ~ -log at x=0), carrying the constant
(B-)block of the defect. Test: the SHIFTED Hankel H1 = (m_{j+k+1}) uses only pure
measure moments -- if it is definite everywhere the event is the corner, a rank-one
explicit defect block. Also locate the corner threshold t* where inertia flips."""
from mpmath import mp, zeta, zetazero, diff, mpf, factorial, matrix, eigsy, mpc, nstr

mp.dps = 55
NZ = 150
f_reg = lambda s: -zeta(s, derivative=1) / zeta(s) - 1 / (s - 1)
print("zeros...", flush=True)
Z = [zetazero(j).imag for j in range(1, NZ + 1)]
print("done", flush=True)


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


def inertia(mom, n, shift=0, corner=None):
    H = matrix(n, n)
    for j in range(n):
        for k in range(n):
            H[j, k] = mom[j + k + shift]
    if corner is not None:
        H[0, 0] = corner
    ev = eigsy(H, eigvals_only=True)
    return sum(1 for e in ev if e > 0), sum(1 for e in ev if e < 0)


for s0 in [0.999, 0.9, 0.6]:
    m = mreg(s0, 36)
    full16 = inertia(m, 16)
    full17 = inertia(m, 17)
    sh16 = inertia(m, 16, shift=1)
    sh17 = inertia(m, 17, shift=1)
    print("s0=%-6s  full: n16 (%d,%d) n17 (%d,%d)   SHIFTED: n16 (%d,%d) n17 (%d,%d)"
          % (s0, *full16, *full17, *sh16, *sh17), flush=True)

# corner threshold at s0=0.9, n=16: sweep m00 -> m00 - t (making corner more negative)
m = mreg(0.9, 36)
m00 = m[0]
lo, hi = mpf(0), mpf(2)
if inertia(m, 16, corner=m00 - hi)[0] != 0:
    print("corner sweep: still (1,.) at t=2 -- widen", flush=True)
else:
    for _ in range(40):
        mid = (lo + hi) / 2
        if inertia(m, 16, corner=m00 - mid)[0] == 0:
            hi = mid
        else:
            lo = mid
    print("corner threshold at s0=0.9, n=16:  t* = %s  (shift m00 -> m00 - t*)"
          % nstr(hi, 8), flush=True)
    print("i.e. the event is a corner deficit of size < %s in the (0,0) entry"
          % nstr(hi, 4), flush=True)
