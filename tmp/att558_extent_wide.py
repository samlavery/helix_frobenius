# Extended: does the finite-extent stage develop complex zeros where it is NOT tracking Xi?
# (Type U => real-zero density <= U/pi; Xi's density ~ log(t/2pi)/2pi. Beyond t ~ e^{2U},
#  the stage cannot follow Xi -- if it stays real-rooted THERE, that is the informative fact.)
# Controls repeated inline.  Pre-registered: any nonzero count = complex zeros, report box.
from mpmath import mp, mpf, mpc, exp, cos, pi, quad, arg
mp.dps = 15
NM = 10
def Phi(u):
    a = abs(u); s = mpf(0)
    for n in range(1, NM+1):
        nn = mpf(n*n)
        s += (2*pi**2*nn*nn*exp(9*a/2) - 3*pi*nn*exp(5*a/2))*exp(-pi*nn*exp(2*a))
    return 4*s
def XiU(z, U): return 2*quad(lambda u: Phi(u)*cos(z*u), [0, min(mpf('0.5'),U), U])
def winding(f, x0, x1, y0, y1, n0=48, depth=7):
    P = []
    for k in range(n0): P.append(mpc(x0+(x1-x0)*k/n0, y0))
    for k in range(n0): P.append(mpc(x1, y0+(y1-y0)*k/n0))
    for k in range(n0): P.append(mpc(x1-(x1-x0)*k/n0, y1))
    for k in range(n0): P.append(mpc(x0, y1-(y1-y0)*k/n0))
    V = [f(p) for p in P]; tot = mpf(0)
    for k in range(len(P)):
        a, b = P[k], P[(k+1) % len(P)]; fa, fb = V[k], V[(k+1) % len(V)]
        d = arg(fb/fa); lvl = 0
        while abs(d) > pi/2 and lvl < depth:
            mids = [a + (b-a)*mpf(j)/(2**(lvl+1)) for j in range(1, 2**(lvl+1))]
            vals = [fa] + [f(m) for m in mids] + [fb]
            d = sum(arg(vals[i+1]/vals[i]) for i in range(len(vals)-1)); lvl += 1
        tot += d
    return tot/(2*pi)
print(f"{'U':>4} {'box':>22} {'count':>8}")
for U, (x0,x1,y0,y1) in [(mpf(5), (60,100,0.05,4)), (mpf(5), (100,140,0.05,4))]:
                          (mpf(1), (25,80,0.05,4)), (mpf(1), (80,140,0.05,4)),
                          (mpf(3), (25,60,0.05,4)), (mpf(3), (60,100,0.05,4)),
                          (mpf(5), (25,60,0.05,4))]:
    c = winding(lambda z: XiU(z, U), mpf(x0), mpf(x1), mpf(y0), mpf(y1))
    print(f"{float(U):>4} [{x0:>3},{x1:>3}]x[{y0},{y1}] {float(c):>8.3f}")
