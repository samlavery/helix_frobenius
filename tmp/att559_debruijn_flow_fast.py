#!/usr/bin/env python3
"""
att559 (fast, v2) — the de Bruijn–Newman warp of the fiber kernel, H_t(z) = ∫_0^∞ e^{tu²} Φ(u) cos(zu) du,
tracked from t = 0.5 down to t = 0 on heights [10, 120].
  P1 no zero leaves the axis at any t (box count = real count).
  P2 for each tracked pair (by RANK — zeros cannot cross on the axis under the flow), the gap shrinks
     monotonically as t ↓ 0; gap² ≈ affine in t with slope c against the isolated two-body 8.
  P3 the fiber's zeros at t = 0 are ζ's (first zero 14.1347…).
Speed: fixed 384-node Gauss–Legendre rule on [0, 1.9] with Φ(u_j)w_j precomputed (exact to ≤1e−9 vs
adaptive quadrature at heights ≤ 105, checked); zeros by coarse sign scan (step 0.3) + bisection —
no Newton, no continuation (v1's Newton returned non-converged points that preserved the count).
"""
import math, time, numpy as np, mpmath as mp
mp.mp.dps = 40
PI = mp.pi
def Phi(u):
    e2 = mp.exp(2*u); e9 = mp.exp(mp.mpf(9)/2*u); e5 = mp.exp(mp.mpf(5)/2*u)
    return mp.fsum((2*PI**2*n**4*e9 - 3*PI*n**2*e5)*mp.exp(-PI*n*n*e2) for n in range(1, 14))
nodes = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(mp.mpf(0), mp.mpf("1.9"), 8, mp.mp.prec)
U = [x for (x, w) in nodes]; PW = [Phi(x)*w for (x, w) in nodes]; U2 = [x*x for x in U]
def make_H(t):
    E = [pw*mp.exp(t*u2) for pw, u2 in zip(PW, U2)]
    return lambda z: mp.fsum(e*mp.cos(z*u) for e, u in zip(E, U))
xi = lambda s: mp.mpf(1)/2*s*(s - 1)*PI**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
out = open("tmp/att559_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.write(s + "\n"); out.flush()
H0 = make_H(mp.mpf(0))
say("normalization/accuracy at t=0: H_0(z) = ξ(½+iz)/4 (this Φ): rel dev at z=20,60,110 = %s" %
    [mp.nstr(abs(H0(mp.mpf(z)) - xi(mp.mpf(1)/2 + 1j*z).real/4)/abs(xi(mp.mpf(1)/2 + 1j*z).real/4), 2) for z in (20, 60, 110)])

def zeros_bracket(H, a, b, step=0.3, bis=38):
    xs = np.arange(a, b + step/2, step); v = [H(mp.mpf(x)).real for x in xs]; zs = []
    for i in range(len(xs) - 1):
        if v[i]*v[i+1] < 0:
            lo, hi, flo = mp.mpf(xs[i]), mp.mpf(xs[i+1]), v[i]
            for _ in range(bis):
                mid = (lo + hi)/2; fm = H(mid).real
                if flo*fm <= 0: hi = mid
                else: lo, flo = mid, fm
            zs.append(float((lo + hi)/2))
    return zs
def winding(H, a, b, n):
    tot = mp.mpf(0); prev = None
    for k in range(n + 1):
        z = a + (b - a)*mp.mpf(k)/n; ph = mp.arg(H(z))
        if prev is not None:
            d = ph - prev
            while d > PI: d -= 2*PI
            while d < -PI: d += 2*PI
            if abs(d) > PI/2: raise RuntimeError("phase step too large; densify")
            tot += d
        prev = ph
    return tot
def box_count(H, T0, T1, Hh, per_unit=8):
    c = [mp.mpc(T0, -Hh), mp.mpc(T1, -Hh), mp.mpc(T1, Hh), mp.mpc(T0, Hh), mp.mpc(T0, -Hh)]
    ns = [int((T1 - T0)*per_unit), int(2*Hh*per_unit)]*2
    return int(mp.nint(sum(winding(H, a, b, n) for (a, b), n in zip(zip(c[:-1], c[1:]), ns))/(2*PI)))

T0, T1 = 10.0, 120.0
ts = [0.5, 0.22, 0.10, 0.05, 0.02, 0.0]
Z = {}
say("\nde Bruijn–Newman warp on [%.0f, %.0f]  (P1: box count vs real count at every t)" % (T0, T1))
for t in ts:
    t0 = time.time(); H = make_H(mp.mpf(t)); zs = zeros_bracket(H, T0, T1); nb = box_count(H, mp.mpf(T0), mp.mpf(T1), mp.mpf(2))
    Z[t] = zs; gaps = np.diff(zs); i = int(np.argmin(gaps))
    say(" t=%.2f : real zeros %d, box %d (%s) ; global min gap %.4f at rank %d (%.3f, %.3f) ; first zero %.4f ; %.1fs"
        % (t, len(zs), nb, "all real" if nb == len(zs) else "PAIR OFF AXIS", gaps[i], i, zs[i], zs[i+1], zs[0], time.time() - t0))
zt = [float(mp.zetazero(k).imag) for k in range(1, 40)]; zt = [z for z in zt if T0 <= z <= T1]
say("\nP3 t=0 vs ζ zeros in range: count %d vs %d ; max |dev| = %.2e" % (len(Z[0.0]), len(zt), max(abs(a - b) for a, b in zip(Z[0.0], zt))))
# P2: the three closest pairs at t = 0, tracked by rank
g0 = np.diff(Z[0.0]); ranks = list(np.argsort(g0)[:3])
say("\nP2 tracked pairs (by rank), gap(t) and gap²(t):")
for r in ranks:
    rows = [(t, Z[t][r+1] - Z[t][r]) for t in ts]
    mono = all(rows[k][1] >= rows[k+1][1] - 1e-9 for k in range(len(rows) - 1))
    tt = np.array([x[0] for x in rows]); g2 = np.array([x[1]**2 for x in rows]); c, g20 = np.polyfit(tt, g2, 1)
    say(" rank %2d  (%.4f, %.4f at t=0)  gaps t=0.5→0: %s  monotone: %s ; gap² ≈ %.3f + %.2f·t  (two-body 8)"
        % (r, Z[0.0][r], Z[0.0][r+1], ["%.4f" % x[1] for x in rows], "yes" if mono else "NO", g20, c))
drift = [np.mean(np.abs(np.array(Z[t]) - np.array(Z[0.0]))) for t in ts]
say("\nmean |z(t) − z(0)| over the 38 zeros: %s" % ["%.3f" % d for d in drift])
say("first zero along the flow: %s" % ["%.4f" % Z[t][0] for t in ts])
out.close()
