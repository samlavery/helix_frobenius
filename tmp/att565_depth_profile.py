# att565 — DEPTH PROFILE of the extent stage's complex zeros (pre-registered).
#
# ROUTE QUESTION (mass-register kill tree, arrow 2 feeding): the channel compact
# sits at distance >= delta from the line; a complex zero hurts stage mass only
# inside its depth-disk.  So the needed behavior is NOT the clean band: zeros may
# persist if their DEPTHS shrink below the margin, or they may vacate upward.
#
# CLAIM UNDER TEST (route-favorable, A): in a fixed height window, as U grows the
# complex-zero count drops to zero (vacate) AND/OR occupancy migrates to the
# shallowest depth band (flatten onto the axis — the Polya collision mechanism).
# REFUTING OUTCOME (B): counts persist at stable depth >= 0.4 after the front
# passes the window.
# PREDICTION: A, vacate-dominant with stragglers flattening.  Reason: locally
# uniform convergence in an RH-true computed range forbids off-axis accumulation.
#
# SOUNDNESS (audit finding att558): |Xi(x)| ~ e^{-pi x/4}; dps 15 is noise below
# height ~45.  This run: dps 32, heights <= 60 only; every box reports
# min|XiU| / e^{-pi x/4} on its boundary; boxes with flag < 1e-9 are UNRELIABLE.
# CONTROL (q=0 style): U = 1.5 at [40,60] (front ~ 4e^3 = 80 >> 60, stage == Xi
# to below Xi's own scale): all complex bands MUST read 0.

from mpmath import mp, mpf, mpc, exp, cos, pi, arg, sqrt
import sys, time

mp.dps = 32
NM = 8

def Phi(u):
    a = abs(u); s = mpf(0)
    for n in range(1, NM + 1):
        nn = mpf(n * n)
        s += (2 * pi**2 * nn * nn * exp(9 * a / 2) - 3 * pi * nn * exp(5 * a / 2)) * exp(-pi * nn * exp(2 * a))
    return 4 * s

from mpmath import quad

def XiU(z, U, xosc):
    # subdivide [0,U] against the oscillation rate |z|~xosc
    npts = max(6, int(float(xosc) * float(U) / 3.0))
    pts = [U * mpf(k) / npts for k in range(npts + 1)]
    return 2 * quad(lambda u: Phi(u) * cos(z * u), pts)

def winding(U, x0, x1, y0, y1, n0=22, depth=6):
    xm = mpf(x1)
    f = lambda z: XiU(z, U, xm)
    P = []
    for k in range(n0): P.append(mpc(x0 + (x1 - x0) * mpf(k) / n0, y0))
    for k in range(n0): P.append(mpc(x1, y0 + (y1 - y0) * mpf(k) / n0))
    for k in range(n0): P.append(mpc(x1 - (x1 - x0) * mpf(k) / n0, y1))
    for k in range(n0): P.append(mpc(x0, y1 - (y1 - y0) * mpf(k) / n0))
    V = [f(p) for p in P]
    scale = exp(-pi * mpf(x0) / 4)   # generous (largest) reference amplitude
    mn = min(abs(v) for v in V) / scale
    tot = mpf(0)
    for k in range(len(P)):
        a, b = P[k], P[(k + 1) % len(P)]
        fa, fb = V[k], V[(k + 1) % len(V)]
        d = arg(fb / fa); lvl = 0
        va, vb = fa, fb
        while abs(d) > pi / 2 and lvl < depth:
            mids = [a + (b - a) * mpf(j) / (2 ** (lvl + 1)) for j in range(1, 2 ** (lvl + 1))]
            vals = [fa] + [f(m) for m in mids] + [fb]
            mn = min(mn, min(abs(v) for v in vals) / scale)
            d = sum(arg(vals[i + 1] / vals[i]) for i in range(len(vals) - 1)); lvl += 1
        tot += d
    return tot / (2 * pi), mn

BANDS = [(mpf('0.02'), mpf('0.1')), (mpf('0.1'), mpf('0.4')),
         (mpf('0.4'), mpf('1.2')), (mpf('1.2'), mpf('3.0'))]
WINDOWS = [(mpf(20), mpf(40)), (mpf(40), mpf(60))]

# argv[1] selects the job: one of 0.8 / 1.0 / 1.2 / 1.35 / control
job = sys.argv[1]
print(f"job {job}: {'U':>5} {'window':>10} {'band':>12} {'count':>7} {'minamp':>10}  flag")
sys.stdout.flush()
t0 = time.time()
if job == "control":
    # U = 1.5 at [40,60]: stage == Xi below its own scale; all bands must be 0
    for (y0, y1) in BANDS:
        c, mn = winding(mpf('1.5'), mpf(40), mpf(60), y0, y1)
        flag = "UNRELIABLE" if mn < mpf('1e-9') else "ok"
        print(f"CTRL {1.5:>5} [ 40, 60] [{float(y0):>4},{float(y1):>4}] {float(c):>7.2f} "
              f"{float(mn):>10.2e}  {flag}   t={time.time()-t0:.0f}s")
        sys.stdout.flush()
else:
    U = mpf(job)
    for (x0, x1) in WINDOWS:
        for (y0, y1) in BANDS:
            c, mn = winding(U, x0, x1, y0, y1)
            flag = "UNRELIABLE" if mn < mpf('1e-9') else "ok"
            print(f"{float(U):>5} [{float(x0):>3.0f},{float(x1):>3.0f}] [{float(y0):>4},{float(y1):>4}] "
                  f"{float(c):>7.2f} {float(mn):>10.2e}  {flag}   t={time.time()-t0:.0f}s")
            sys.stdout.flush()
print(f"job {job} total {time.time()-t0:.0f}s")
