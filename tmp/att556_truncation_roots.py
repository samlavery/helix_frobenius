# THE COMPOSITION-POINT PROBE (pre-registered; rules fixed before run).
# Q: are theta-mode truncations Xi_N real-rooted?  (Xi_N = FT of symmetrized N-mode Phi)
# Xi_N(z) = 2 Int_0^L Phi_N^sym(u) cos(zu) du     (even in z, real on R by construction)
# DECISION: winding count in UPPER rectangle = 0 for all N -> real-rootedness supported,
#   adopt as constructive claim; any count > 0 -> that N is NOT real-rooted (report where).
# POWER CONTROL: the counter must return 2 for Xi_90 on [10,25]x[-1,1] (zeros 14.13, 21.02).
# VALIDATION: Xi_90(x)/xi_exact(1/2+ix) must be a constant (normalization) at two x.
from mpmath import mp, mpf, mpc, exp, cos, pi, quad, gamma, zeta, arg, log
mp.dps = 15
L = mpf(6)
def PhiRaw(u, N):
    s = mpf(0)
    for n in range(1, N+1):
        nn = mpf(n*n)
        s += (2*pi**2*nn*nn*exp(9*u/2) - 3*pi*nn*exp(5*u/2))*exp(-pi*nn*exp(2*u))
    return 4*s
def PhiSym(u, N): return (PhiRaw(u, N) + PhiRaw(-u, N))/2
def Xi(z, N): return 2*quad(lambda u: PhiSym(u, N)*cos(z*u), [0, 1, L])
# --- validation
for x in [10, 14]:
    s0 = mpc(0.5, x)
    ex = (s0*(s0-1)/2 * pi**(-s0/2) * gamma(s0/2) * zeta(s0)).real
    print(f"validate: Xi_90({x})/xi_exact = {float((Xi(mpf(x),90)/ex).real):.6f}")
def winding(N, x0, x1, y0, y1, npts=60):
    pts = []
    for k in range(npts): pts.append(mpc(x0+(x1-x0)*k/npts, y0))
    for k in range(npts): pts.append(mpc(x1, y0+(y1-y0)*k/npts))
    for k in range(npts): pts.append(mpc(x1-(x1-x0)*k/npts, y1))
    for k in range(npts): pts.append(mpc(x0, y1-(y1-y0)*k/npts))
    vals = [Xi(p, N) for p in pts]
    tot = mpf(0)
    for k in range(len(vals)):
        a, b = vals[k], vals[(k+1) % len(vals)]
        d = arg(b/a)
        tot += d
    return tot/(2*pi)
print("POWER CONTROL Xi_90 on [10,25]x[-1,1]:", float(winding(90, mpf(10), mpf(25), mpf(-1), mpf(1))))
print(f"{'N':>4} {'winding, upper [0,30]x[0.05,2]':>32}")
for N in [1, 2, 3, 5, 90]:
    w = winding(N, mpf(0), mpf(30), mpf('0.05'), mpf(2))
    print(f"{N:>4} {float(w):>32.4f}")
