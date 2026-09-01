# att566 — ESCORT-PREDICTION TEST of the edge-wave model (pre-registered).
#
# Model: Xi_U = Xi − T_U, T_U(z) ≈ Φ(U)[e^{izU}/(c−iz) + e^{−izU}/(c+iz)],
# c = 2π e^{2U} − 9/2.  Balance curve y*(x) = D(x)/δ(x),
# δ(x) = U − (1/2)log(x/2π).  Retrodictions: x_a(1.0) ≈ 31, x_a(1.2) ≈ 45.8
# (both inside Sam's measured brackets).
#
# PRE-REGISTERED PREDICTIONS (decision rules BEFORE the run):
#  T1 (U=1.00): exactly one zero in [28,34]x[0.3,1.6]; bisection puts it at
#      x = 30.5 ± 2, y = 0.8 ± 0.4.
#  T2 (U=1.02, THE DISCRIMINATOR): DIVE predicted — one pair member in
#      [27,34]x[3.5,11], ZERO in [27,34]x[0.02,0.5].  Collision-with-axis
#      would give the reverse.  Transition band [0.5,3.5] recorded either way.
#  T3 (U=0.80): exactly one zero in [18,23]x[0.05,0.6] at x = 20 ± 2,
#      y = 0.3 ± 0.15.
# Any outcome outside these rules = model refuted at that point; report as-is.
#
# Soundness: dps 32; heights ≤ 34 (|Xi| ≥ ~e^{-27}); minamp flag per box.

from mpmath import mp, mpf, mpc, exp, cos, pi, arg
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
    npts = max(6, int(float(xosc) * float(U) / 3.0))
    pts = [U * mpf(k) / npts for k in range(npts + 1)]
    return 2 * quad(lambda u: Phi(u) * cos(z * u), pts)

def winding(U, x0, x1, y0, y1, n0=20, depth=6):
    xm = mpf(x1)
    f = lambda z: XiU(z, U, xm)
    P = []
    for k in range(n0): P.append(mpc(x0 + (x1 - x0) * mpf(k) / n0, y0))
    for k in range(n0): P.append(mpc(x1, y0 + (y1 - y0) * mpf(k) / n0))
    for k in range(n0): P.append(mpc(x1 - (x1 - x0) * mpf(k) / n0, y1))
    for k in range(n0): P.append(mpc(x0, y1 - (y1 - y0) * mpf(k) / n0))
    V = [f(p) for p in P]
    scale = exp(-pi * mpf(x0) / 4)
    mn = min(abs(v) for v in V) / scale
    tot = mpf(0)
    for k in range(len(P)):
        a, b = P[k], P[(k + 1) % len(P)]
        fa, fb = V[k], V[(k + 1) % len(V)]
        d = arg(fb / fa); lvl = 0
        while abs(d) > pi / 2 and lvl < depth:
            mids = [a + (b - a) * mpf(j) / (2 ** (lvl + 1)) for j in range(1, 2 ** (lvl + 1))]
            vals = [fa] + [f(m) for m in mids] + [fb]
            mn = min(mn, min(abs(v) for v in vals) / scale)
            d = sum(arg(vals[i + 1] / vals[i]) for i in range(len(vals) - 1)); lvl += 1
        tot += d
    return tot / (2 * pi), mn

def report(tag, U, x0, x1, y0, y1, t0):
    c, mn = winding(mpf(U), mpf(x0), mpf(x1), mpf(y0), mpf(y1))
    flag = "UNRELIABLE" if mn < mpf('1e-9') else "ok"
    print(f"{tag} U={U} [{x0},{x1}]x[{y0},{y1}] count={float(c):.2f} minamp={float(mn):.2e} {flag} t={time.time()-t0:.0f}s")
    sys.stdout.flush()
    return float(c)

job = sys.argv[1]
t0 = time.time()
if job == "T1":
    c = report("T1", '1.0', 28, 34, '0.3', '1.6', t0)
    if abs(c - 1) < 0.3:
        # bisect in x, then in y
        cl = report("T1x", '1.0', 28, 31, '0.3', '1.6', t0)
        report("T1x", '1.0', 31, 34, '0.3', '1.6', t0)
        lo, hi = (28, 31) if abs(cl - 1) < 0.3 else (31, 34)
        report("T1y", '1.0', lo, hi, '0.3', '0.8', t0)
        report("T1y", '1.0', lo, hi, '0.8', '1.6', t0)
elif job == "T2":
    report("T2-dive", '1.02', 27, 34, '3.5', '11', t0)
    report("T2-coll", '1.02', 27, 34, '0.02', '0.5', t0)
    report("T2-mid ", '1.02', 27, 34, '0.5', '3.5', t0)
elif job == "T3":
    c = report("T3", '0.8', 18, 23, '0.05', '0.6', t0)
    if abs(c - 1) < 0.3:
        cl = report("T3x", '0.8', 18, mpf('20.5'), '0.05', '0.6', t0)
        report("T3x", '0.8', mpf('20.5'), 23, '0.05', '0.6', t0)
print(f"job {job} done t={time.time()-t0:.0f}s")
