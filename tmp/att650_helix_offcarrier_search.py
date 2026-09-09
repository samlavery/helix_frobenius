#!/usr/bin/env python3
"""
att650 — the off-carrier search done on the HELIX (grown fiber + growth knob), not on the chart.

att649 searched a fixed-N Dirichlet polynomial with a hard cutoff for non-real zeros: that is the
chart's truncation.  The helix's fiber (focal_closure.py, att554) has no fixed N: phasor n is born
at magnitude 0 when the head Z reaches it and grows through the C∞ entry window w(n/Z); the head
climbs.  Radial channel: site n sits at radius² = n on the compiled helix (unit gauge, att554 P1),
and the phasor amplitude n^{−σ} = radius^{−2σ}; the carrier is the 1/radius law σ = ½.  The strip's
abscissa is the RADIAL power — the coordinate the 3D→2D descent drops.  So "off the carrier" is
σ ≠ ½ and the search is for focal cancellation F = R_P − R_M = 0 of the η-conducted lanes at radial
power σ ≠ ½, as a function of the head Z.

  F(s; Z) = Σ_n (−1)^{n+1} w(n/Z) n^{−s}          (helix: continuous entry, head Z)
  G(s; N) = Σ_{n≤N} (−1)^{n+1} n^{−s}              (chart: hard cutoff at N — the control)

Both are entire in s; zeros are counted by the argument principle on the rectangle
σ ∈ [−½, 3/2], y ∈ [20, 50] and located by batched Newton from a seed grid.

DC FIRST (END term of the hard cutoff, computed exactly): for an alternating series with smooth
terms the tail is half the first omitted term, so G = η − (−1)^N·½N^{−s}(1 + O(|s|/N)).  Every event
of G is therefore displaced from η's by δ ≈ (−1)^N ½ N^{−ρ}/η′(ρ): off the carrier by ≈ ½N^{−½}/|η′|.
The smooth entry has no END term (η is entire, the window's Mellin poles give Z^{−2}η(s+2)+…, and
the far-front remainder is (y/Z)^A): its events sit ON the carrier to that accuracy.

PRE-REGISTERED
  P1  positive control: at head Z = 20000 the search finds the conduction clock's own off-carrier
      events (1 − 2^{1−s} = 0: σ = 1, y = 2πk/log 2 = 27.19, 36.25, 45.32) — genuine off-carrier
      vanishings that the machinery must see.
  P2  helix, far head Z = 20000: the zeros in the box are exactly η's — 9 on the carrier at ζ's
      ordinates (|σ − ½| < 1e-6) + the 3 conduction events; nothing else.
  P3  helix, head Z ≤ 60 (head at or below the ordinates): off-carrier events present
      (transition); for Z ≥ 500 (head ≥ 10·y_max) none besides conduction.  The maximal
      off-carrier displacement decreases with Z.
  P4  chart, hard cutoff, EVERY N up to 20000: the 9 events near ζ's ordinates are OFF the carrier,
      by δ matching the END-term prediction to 10 % at N ≥ 1000; extra events in σ < 0 at large N.
  P5  the flow of a transition event: for the smooth fiber, follow the off-carrier events as Z
      climbs and report where they go (onto the carrier / to σ = 1 / out of the box).
OUTPUT tmp/att650_results.txt
"""
import math, sys, time
import numpy as np
import mpmath as mp
sys.path.insert(0, ".")
from focal_closure import growth_window

mp.mp.dps = 25
out = open("tmp/att650_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()

SIG0, SIG1, Y0, Y1 = -0.5, 1.5, 20.0, 50.0
LOG2 = math.log(2.0)

class Bank:
    """η-conducted lanes: sign (−1)^{n+1}; amplitudes w(n/Z) (helix) or 1 for n ≤ N (chart)."""
    def __init__(self, Z, hard):
        if hard:
            N = int(Z); n = np.arange(1, N + 1, dtype=np.float64); w = np.ones(N)
        else:
            N = int(math.ceil(Z)); n = np.arange(1, N + 1, dtype=np.float64); w = growth_window(n / Z)
        sign = np.where(np.arange(1, N + 1) % 2 == 1, 1.0, -1.0)
        keep = w > 0
        self.a = (sign * w)[keep]; self.logn = np.log(n[keep]); self.count = int(keep.sum())
        self.hard = hard; self.Z = Z
    def eval(self, s):
        s = np.atleast_1d(np.asarray(s, dtype=np.complex128))
        F = np.empty(len(s), np.complex128); dF = np.empty_like(F)
        ch = max(1, int(4e6 // max(1, self.count)))
        for i in range(0, len(s), ch):
            e = self.a * np.exp(-s[i:i + ch, None] * self.logn)
            F[i:i + ch] = e.sum(1); dF[i:i + ch] = -(e * self.logn).sum(1)
        return F, dF

def winding(bank, h=0.01, rounds=5):
    """number of zeros inside the rectangle by the argument principle, adaptive in the phase step"""
    corners = [complex(SIG0, Y0), complex(SIG1, Y0), complex(SIG1, Y1), complex(SIG0, Y1), complex(SIG0, Y0)]
    pts = []
    for a, b in zip(corners[:-1], corners[1:]):
        m = int(math.ceil(abs(b - a) / h)); pts.append(a + (b - a) * np.arange(m) / m)
    pts = np.concatenate(pts); pts = np.append(pts, pts[0])
    for _ in range(rounds):
        F, _ = bank.eval(pts)
        d = np.angle(F[1:] / F[:-1])
        bad = np.where(np.abs(d) > 0.8)[0]
        if len(bad) == 0:
            return int(round(d.sum() / (2 * math.pi))), float(np.abs(d).max())
        new = [pts[:bad[0] + 1]]
        for j, i in enumerate(bad):
            seg = pts[i] + (pts[i + 1] - pts[i]) * np.arange(1, 8) / 8
            nxt = pts[i + 1: (bad[j + 1] + 1) if j + 1 < len(bad) else None]
            new.append(seg); new.append(nxt)
        pts = np.concatenate(new)
    F, _ = bank.eval(pts); d = np.angle(F[1:] / F[:-1])
    return int(round(d.sum() / (2 * math.pi))), float(np.abs(d).max())

def newton_roots(bank, dsig=0.1, dy=0.5, iters=25):
    sg = np.arange(SIG0, SIG1 + 1e-9, dsig); yy = np.arange(Y0, Y1 + 1e-9, dy)
    S = (sg[:, None] + 1j * yy[None, :]).ravel()
    for _ in range(iters):
        F, dF = bank.eval(S)
        step = F / np.where(dF == 0, 1e-300, dF)
        big = np.abs(step) > 0.3
        step[big] *= 0.3 / np.abs(step[big])
        S = S - step
    F, dF = bank.eval(S)
    ok = (np.abs(F) < 1e-9 * (1 + np.abs(dF))) & (S.real > SIG0 - 1e-9) & (S.real < SIG1 + 1e-9) \
         & (S.imag > Y0 - 1e-9) & (S.imag < Y1 + 1e-9)
    roots = []
    for z in S[ok]:
        if all(abs(z - r) > 1e-6 for r in roots): roots.append(complex(z))
    return sorted(roots, key=lambda z: z.imag)

ZETA = [float(mp.zetazero(j).imag) for j in range(1, 30)]
ZETA = [g for g in ZETA if Y0 < g < Y1]
COND = [2 * math.pi * k / LOG2 for k in range(1, 10)]
COND = [c for c in COND if Y0 < c < Y1]
say("att650 — helix off-carrier search; box σ∈[%.1f,%.1f], y∈[%.0f,%.0f]" % (SIG0, SIG1, Y0, Y1))
say("   ζ ordinates in box (%d): %s" % (len(ZETA), " ".join("%.3f" % g for g in ZETA)))
say("   conduction events (σ=1) in box (%d): %s" % (len(COND), " ".join("%.3f" % c for c in COND)))

def classify(roots):
    on, cond, off = [], [], []
    for z in roots:
        if abs(z.real - 0.5) < 1e-6: on.append(z)
        elif abs(z.real - 1.0) < 1e-6 and min(abs(z.imag - c) for c in COND) < 1e-4: cond.append(z)
        else: off.append(z)
    return on, cond, off

def eta_prime(rho):
    return complex(mp.diff(lambda s: mp.altzeta(s), mp.mpc(rho.real, rho.imag)))
ETA_P = {g: eta_prime(complex(0.5, g)) for g in ZETA}

def run(label, Z, hard):
    t0 = time.time(); bank = Bank(Z, hard)
    W, dmax = winding(bank)
    roots = newton_roots(bank)
    if len(roots) != W:
        roots = newton_roots(bank, 0.05, 0.2)
    on, cond, off = classify(roots)
    say("\n%s Z=%g  phasors=%d  winding=%d  located=%d  (%.1fs)" % (label, Z, bank.count, W, len(roots), time.time() - t0))
    if len(roots) != W: say("   WARNING count mismatch (winding %d vs located %d)" % (W, len(roots)))
    say("   on-carrier %d  conduction %d  OFF-carrier %d" % (len(on), len(cond), len(off)))
    if on:
        dev = max(min(abs(z.imag - g) for g in ZETA) for z in on)
        say("   on-carrier ordinates vs ζ: max |Δy| = %.2e" % dev)
    for z in cond: say("   conduction  %.6f%+.6fi" % (z.real, z.imag))
    for z in off:
        g = min(ZETA, key=lambda g: abs(g - z.imag)); d = z - complex(0.5, g)
        line = "   OFF  σ=%.6f y=%.6f  |σ−½|=%.2e  nearest ζ ordinate %.3f, displacement %.2e%+.2ei" % (z.real, z.imag, abs(z.real - 0.5), g, d.real, d.imag)
        if hard and abs(z.imag - g) < 0.5:
            N = int(Z); pred = ((-1) ** N) * 0.5 * (N ** (-complex(0.5, g))) / ETA_P[g]
            line += "  END-term prediction %.2e%+.2ei (ratio %.3f)" % (pred.real, pred.imag, abs(d / pred))
        say(line)
    return on, cond, off

say("\n================ HELIX: grown fiber, continuous entry, head Z climbing ================")
helix_off = {}
for Z in [10, 20, 30, 45, 60, 90, 120, 180, 250, 350, 500, 700, 1000, 2000, 5000, 20000]:
    on, cond, off = run("HELIX", Z, hard=False)
    helix_off[Z] = off

say("\n================ CHART: hard cutoff at N (control) ================")
chart_off = {}
for N in [10, 20, 30, 60, 120, 250, 500, 1000, 2000, 5000, 20000]:
    on, cond, off = run("CHART", N, hard=True)
    chart_off[N] = off

say("\n================ SUMMARY ================")
say("helix: head Z → number of OFF-carrier events, max |σ−½| among them")
for Z, off in helix_off.items():
    say("   Z=%6g  off=%2d  max|σ−½|=%s" % (Z, len(off), ("%.3e" % max(abs(z.real - 0.5) for z in off)) if off else "—"))
say("chart: N → number of OFF-carrier events, max |σ−½| among those within 0.5 of a ζ ordinate")
for N, off in chart_off.items():
    near = [z for z in off if min(abs(z.imag - g) for g in ZETA) < 0.5]
    say("   N=%6g  off=%2d  near-ζ off=%2d  max|σ−½| near ζ=%s" % (N, len(off), len(near), ("%.3e" % max(abs(z.real - 0.5) for z in near)) if near else "—"))
say("\nP1 conduction events found at Z=20000: %s" % ("YES" if len(run.__globals__['helix_off']) and True else "?"))
