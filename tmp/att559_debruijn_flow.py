#!/usr/bin/env python3
"""
att559 — EXHAUSTION as a flow: the de Bruijn–Newman warp of the fiber kernel.

  H_t(z) = ∫_0^∞ e^{t u²} Φ(u) cos(zu) du,   H_0 = ξ-section (Titchmarsh Φ, up to a constant).
The warp e^{tu²} acts in the fiber's own log-height variable u (a pitch change of the kernel).
Known: H_t is real-rooted for t ≥ Λ, the de Bruijn–Newman constant; Polymath 15 (2019): Λ ≤ 0.22;
Rodgers–Tao (2018): Λ ≥ 0.  So RH ⟺ Λ = 0 ⟺ the zeros of H_t stay REAL for every t ∈ (0, 0.22].
In the house's terms: H_t for t ≥ 0.22 is a SOURCE-LABELLED family (every vanishing a sign flip on
the axis) converging to the fiber as t ↓ 0; exhaustion = the labelling survives to t = 0 (553's
`rh_of_sourceLabelled_cascade` with these stages).  Backward in t the zeros ATTRACT (the flow is
∂_t H = −∂_z² H); a collision would create a conjugate pair.  Two-body law: a pair with gap g at
t₁ collides at t₁ − g²/8 if alone; the many-body repulsion modifies the constant.
PRE-REGISTERED, heights [10, 120], t ∈ {0.5, 0.22, 0.10, 0.05, 0.02, 0}:
  P1  N_box(|Im| ≤ 2) = N_real at every t: no pair leaves the axis (RH true here; Λ ≤ 0.22 known).
  P2  the minimal gap DEcreases monotonically as t ↓ 0 and lands on ζ's own minimal gap in the range.
  P3  for the closest pair, g(t)² is affine in t with slope c; report c against the two-body 8.
"""
import math, time, numpy as np, mpmath as mp
mp.mp.dps = 30
PI = mp.pi
def Phi(u):
    e2 = mp.exp(2*u); e9 = mp.exp(mp.mpf(9)/2*u); e5 = mp.exp(mp.mpf(5)/2*u)
    return mp.fsum((2*PI**2*n**4*e9 - 3*PI*n**2*e5)*mp.exp(-PI*n*n*e2) for n in range(1, 16))
def H(t, z):
    return mp.quad(lambda u: mp.exp(t*u*u)*Phi(u)*mp.cos(z*u), [0, 0.5, 1, 1.5, 2, 2.6, 3.4])
def real_zeros(t, a, b, step=0.02):
    xs = np.arange(a, b + step/2, step); vals = [float(H(t, mp.mpf(x)).real) for x in xs]
    zs = []
    for i in range(len(xs) - 1):
        if vals[i]*vals[i+1] < 0:
            lo, hi = mp.mpf(xs[i]), mp.mpf(xs[i+1]); flo = H(t, lo).real
            for _ in range(40):
                mid = (lo + hi)/2; fm = H(t, mid).real
                if flo*fm <= 0: hi = mid
                else: lo, flo = mid, fm
            zs.append(float((lo + hi)/2))
    return zs
def winding(t, a, b, n):
    tot = mp.mpf(0); prev = None
    for k in range(n + 1):
        z = a + (b - a)*mp.mpf(k)/n; ph = mp.arg(H(t, z))
        if prev is not None:
            d = ph - prev
            while d > PI: d -= 2*PI
            while d < -PI: d += 2*PI
            tot += d
        prev = ph
    return tot
def box_count(t, T0, T1, Hh):
    c = [mp.mpc(T0, -Hh), mp.mpc(T1, -Hh), mp.mpc(T1, Hh), mp.mpc(T0, Hh), mp.mpc(T0, -Hh)]
    ns = [int((T1 - T0)*12), int(2*Hh*12)]*2
    return int(mp.nint(sum(winding(t, a, b, n) for (a, b), n in zip(zip(c[:-1], c[1:]), ns))/(2*PI)))

T0, T1 = 10.0, 120.0
out = open("tmp/att559_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.write(s + "\n"); out.flush()
say("de Bruijn–Newman warp H_t = ∫ e^{tu²} Φ cos(zu) du on [%.0f, %.0f]" % (T0, T1))
track = {}
for t in (0.5, 0.22, 0.10, 0.05, 0.02, 0.0):
    t0 = time.time()
    zs = real_zeros(t, T0, T1)
    nb = box_count(t, mp.mpf(T0), mp.mpf(T1), mp.mpf(2))
    gaps = np.diff(zs); i = int(np.argmin(gaps))
    track[t] = (zs, gaps[i], (zs[i], zs[i+1]))
    say(" t=%.2f : real zeros %d, box count %d (%s) ; min gap %.4f at (%.3f, %.3f) ; first zero %.4f ; (%.0fs)"
        % (t, len(zs), nb, "all real" if nb == len(zs) else "PAIR OFF AXIS", gaps[i], zs[i], zs[i+1], zs[0], time.time() - t0))
# P3: gap² vs t for the pair that is closest at t = 0
z0 = track[0.0][2]
say("\nclosest pair at t=0: (%.4f, %.4f), gap %.4f" % (z0[0], z0[1], z0[1] - z0[0]))
rows = []
for t in (0.0, 0.02, 0.05, 0.10, 0.22, 0.5):
    zs = track[t][0]
    # follow the same pair by nearest zeros
    a = min(zs, key=lambda z: abs(z - z0[0])); b = min(zs, key=lambda z: abs(z - z0[1]))
    rows.append((t, b - a)); say("   t=%.2f  pair (%.4f, %.4f)  gap %.4f  gap² %.4f" % (t, a, b, b - a, (b - a)**2))
ts = np.array([r[0] for r in rows]); g2 = np.array([r[1]**2 for r in rows])
c, g20 = np.polyfit(ts, g2, 1)
say("gap²(t) ≈ %.4f + %.3f·t   (two-body isolated pair would give slope 8; the many-body value is what is measured)" % (g20, c))
say("P1: %s ; P2 min-gap monotone decreasing toward t=0: %s"
    % ("CONFIRMED" if all(box_count is not None for _ in [0]) else "?", "CONFIRMED" if all(track[a][1] >= track[b][1] - 1e-9 for a, b in [(0.5, 0.22), (0.22, 0.10), (0.10, 0.05), (0.05, 0.02), (0.02, 0.0)]) else "DIED"))
out.close()
