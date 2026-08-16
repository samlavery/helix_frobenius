"""att217: the anchor lift -- the FE-paired hermitian form at complex anchor
s0 = 0.9 + i*tau. Hermitian for every tau; on-line atoms contribute |P|^2; the form
localizes near gamma ~ tau as the anchor rises: the windowing step IS the lift.
Pre-registered: PSD at all tau (verified range); mass concentrates near tau;
min-eig structure as tau passes each gamma_j."""
from mpmath import mp, mpf, mpc, matrix, eighe, nstr

mp.dps = 40
N = 8
Z = [mpf(l.strip()) for l in open("tmp/zeros150_dps45.txt")]

def gamma_face(s0c, n):
    A = matrix(n, n)
    for j in range(n):
        for k in range(n):
            tot = mpc(0)
            for g in Z:
                for sgn in (1, -1):
                    rho = mpc(mpf(1) / 2, sgn * g)
                    tot += (s0c - rho) ** (-(j + 1)) * \
                           (s0c.conjugate() - (1 - rho)) ** (-(k + 1))
            A[j, k] = tot
    return (A + A.transpose_conj()) / 2

print(" tau     inertia    min-eig        max-eig       dominant zeros (|term| share)")
for tau in [0, 5, 10, 14.135, 17.5, 21.022, 25, 30]:
    s0c = mpc(mpf("0.9"), mpf(tau))
    A = gamma_face(s0c, N)
    ev = [e.real for e in eighe(A, eigvals_only=True)]
    npos = sum(1 for e in ev if e > 0)
    nneg = sum(1 for e in ev if e < 0)
    # mass localization: |(s0-rho)|^-2 weight share of the three nearest zeros
    ws = [(abs(s0c - mpc(mpf(1)/2, g)) ** (-2) +
           abs(s0c - mpc(mpf(1)/2, -g)) ** (-2), g) for g in Z]
    tot = sum(w for w, _ in ws)
    ws.sort(reverse=True)
    dom = "  ".join("%.2f:%.0f%%" % (float(g), 100 * float(w / tot)) for w, g in ws[:3])
    print(" %6.3f  (%d,%d)     %-12s  %-12s  %s"
          % (tau, npos, nneg, nstr(min(ev), 3), nstr(max(ev), 3), dom), flush=True)
