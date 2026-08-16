"""att208: confirm + localize the first inertia event ((1,15) at s0=0.999, n=16).
Checks: (a) pole-proximity artifact -- sweep s0 in {0.999, 0.99, 0.95, 0.9} (stencil
distance to the pole varies 30x); (b) onset in n -- n in {15,16,17}; (c) localization
-- print the positive eigenvalue and the roots of its eigenpolynomial (which
x-feature it resolves: prime atom log2=0.693? zero scale 2pi/gamma_1=0.44? seam?)."""
from mpmath import mp, zeta, zetazero, diff, mpf, factorial, matrix, eigsy, mpc, polyroots, nstr

mp.dps = 60
NZ = 150
f_reg = lambda s: -zeta(s, derivative=1) / zeta(s) - 1 / (s - 1)
print("zeros at dps %d..." % mp.dps, flush=True)
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


for s0 in [0.999, 0.99, 0.95, 0.9]:
    m = mreg(s0, 34)
    line = ["s0=%-6s" % s0]
    for n in [15, 16, 17]:
        H = matrix(n, n)
        for j in range(n):
            for k in range(n):
                H[j, k] = m[j + k]
        E, Q = eigsy(H)
        pos = [(i, E[i]) for i in range(n) if E[i] > 0]
        line.append("n=%d:(%d,%d)" % (n, len(pos), n - len(pos)))
        if pos and n == 16:
            i0, lam0 = pos[0]
            v = [Q[j, i0] for j in range(n)]
            roots = polyroots([v[n - 1 - k] for k in range(n)], maxsteps=200,
                              extraprec=100)
            rr = [r for r in roots if abs(r.imag) < 1e-20]
            line.append("lam+=%s" % nstr(lam0, 4))
            line.append("real roots: " + " ".join(nstr(r.real, 4) for r in
                        sorted(rr, key=lambda t: t.real)))
    print("  ".join(line), flush=True)
