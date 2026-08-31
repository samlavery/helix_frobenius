# WARPED/SCALED GEOMETRIC KERNEL, finite EXTENT (not finite mode count).
# Phi(u) = 4*sum_n (2pi^2 n^4 e^{9u/2} - 3pi n^2 e^{5u/2}) e^{-pi n^2 e^{2u}}   [warp e^{2u}, scale pi]
# Stage U:  Xi_U(z) = 2 Int_0^U Phi(u) cos(zu) du   -- entire, even, real on R, -> Xi as U->inf.
# Q: is Xi_U real-rooted?  (real-rooted + convergent stages => compiled cascade door => RH)
# PRE-REGISTERED: counter must pass BOTH controls or results are void:
#   (P1) G3 countermodel box around known complex zero 1.5708+0.6585i  -> 1
#   (P2) G3 empty box [3,4]x[0.3,1.0]                                   -> 0
# Then: count in upper box for U = 0.5,1,2,3.  0 => real-rooted (constructive claim);
#   >0 => complex zeros exist, report U and count.  Convergence check: Xi_3 vs Xi_6 on R.
from mpmath import mp, mpf, mpc, exp, cos, pi, quad, arg, acosh
mp.dps = 15
NM = 10
def Phi(u):
    a = abs(u); s = mpf(0)
    for n in range(1, NM+1):
        nn = mpf(n*n)
        s += (2*pi**2*nn*nn*exp(9*a/2) - 3*pi*nn*exp(5*a/2))*exp(-pi*nn*exp(2*a))
    return 4*s
def XiU(z, U): return 2*quad(lambda u: Phi(u)*cos(z*u), [0, min(mpf('0.5'),U), U])
lam3, a3 = mpf('0.5'), mpf(2)
def G3(z):
    g = lambda u: exp(-u**2/2) + (lam3/2)*(exp(-(u-a3)**2/2) + exp(-(u+a3)**2/2))
    return 2*quad(lambda u: g(u)*cos(z*u), [0, 2, 8])
def winding(f, x0, x1, y0, y1, n0=48, depth=7):
    def path():
        P = []
        for k in range(n0): P.append(mpc(x0+(x1-x0)*k/n0, y0))
        for k in range(n0): P.append(mpc(x1, y0+(y1-y0)*k/n0))
        for k in range(n0): P.append(mpc(x1-(x1-x0)*k/n0, y1))
        for k in range(n0): P.append(mpc(x0, y1-(y1-y0)*k/n0))
        return P
    P = path(); V = [f(p) for p in P]; tot = mpf(0)
    for k in range(len(P)):
        a, b = P[k], P[(k+1) % len(P)]; fa, fb = V[k], V[(k+1) % len(V)]
        d = arg(fb/fa); lvl = 0
        while abs(d) > pi/2 and lvl < depth:      # refine until every step < pi/2
            mids = [a + (b-a)*mpf(j)/(2**(lvl+1)) for j in range(1, 2**(lvl+1))]
            vals = [fa] + [f(m) for m in mids] + [fb]
            d = sum(arg(vals[i+1]/vals[i]) for i in range(len(vals)-1)); lvl += 1
        tot += d
    return tot/(2*pi)
print("P1 (G3 box w/ known complex zero) =", float(winding(G3, mpf(1), mpf(2), mpf('0.3'), mpf(1))))
print("P2 (G3 empty box)                 =", float(winding(G3, mpf(3), mpf(4), mpf('0.3'), mpf(1))))
print("convergence Xi_3 vs Xi_6 at z=10 :", float(XiU(mpf(10), mpf(3)).real), float(XiU(mpf(10), mpf(6)).real))
print(f"{'U':>5} {'winding, [0,25]x[0.05,3]':>26}")
for U in [mpf('0.5'), mpf(1), mpf(2), mpf(3)]:
    print(f"{float(U):>5} {float(winding(lambda z: XiU(z, U), mpf(0), mpf(25), mpf('0.05'), mpf(3))):>26.4f}")
