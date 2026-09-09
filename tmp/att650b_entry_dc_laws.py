#!/usr/bin/env python3
"""
att650b — the DC of each entry law, computed exactly and checked against att650's displacements.

HELIX (continuous entry, head Z).  Mellin: Σ_n a_n w(n/Z) n^{−s} = (1/2πi)∫ ŵ(z) Z^z η(s+z) dz; the
window w(u) = exp(1 − 1/(1−u²)) = 1 − u² − u⁴/2 − … is even, so ŵ has poles at 0, −2, −4, … with
residues 1, w″(0)/2 = −1, w⁗(0)/24 = −½, …:
      F_Z(s) = η(s) − Z^{−2} η(s−2) − ½ Z^{−4} η(s−4) − …      (the fiber read to the LEFT)
so each event ρ of η is displaced to ρ + δ_Z with  δ_Z = Z^{−2} η(ρ−2)/η′(ρ) + O(Z^{−4}).
CHART (hard cutoff N).  G_N(s) = η(s) − (−1)^N ½ N^{−s}(1 + O(|s|/N)):  δ_N = (−1)^N ½ N^{−ρ}/η′(ρ),
and a manufactured line of events where |η(s)| = ½ N^{−σ}, i.e. σ ≈ −log(2|η(s)|)/log N, spaced
2π/log N in y.
PRE-REGISTERED
  Q1 helix: measured δ / predicted δ → 1 as Z grows, within 10 % at Z = 5000 for all 9 events.
  Q2 helix sign: Re[η(ρ−2)/η′(ρ)] < 0 for the 9 events of att650 (observed); PREDICTION for the
     first 200 zeros: mixed signs (no law claimed) — the count of each sign is reported.
  Q3 chart: at N = 20000 every manufactured event satisfies |η(s)|/(½N^{−σ}) = 1 within 1 %.
"""
import math, sys, re
import numpy as np, mpmath as mp
sys.path.insert(0, ".")
from focal_closure import growth_window
mp.mp.dps = 25
out = open("tmp/att650b_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()

def fiber(Z):
    N = int(math.ceil(Z)); n = np.arange(1, N + 1, dtype=np.float64); w = growth_window(n / Z)
    a = np.where(np.arange(1, N + 1) % 2 == 1, 1.0, -1.0) * w; keep = w > 0
    a, ln = a[keep], np.log(n[keep])
    def ev(s):
        e = a * np.exp(-s * ln); return e.sum(), -(e * ln).sum()
    return ev

def newton(ev, s, it=40):
    for _ in range(it):
        F, dF = ev(s); s = s - F / dF
    return s

zeros = [mp.zetazero(j) for j in range(1, 201)]
eta = mp.altzeta
def etap(r): return mp.diff(eta, r)

say("Q1 helix DC law: δ_Z = Z^{-2} η(ρ−2)/η′(ρ)")
Q1ok = True
for Z in (250, 1000, 5000, 20000):
    ev = fiber(Z); worst = 0.0
    for r in zeros[:12]:
        if not (20 < r.imag < 50): continue
        rr = complex(r)
        meas = newton(ev, rr) - rr
        pred = complex(eta(r - 2) / etap(r)) / Z ** 2
        ratio = meas / pred; worst = max(worst, abs(ratio - 1))
        say("   Z=%5d γ=%.3f  measured δ=%+.3e%+.3ei  predicted %+.3e%+.3ei  ratio %.4f%+.4fi" % (Z, rr.imag, meas.real, meas.imag, pred.real, pred.imag, ratio.real, ratio.imag))
    say("   Z=%5d  max |ratio − 1| = %.3f" % (Z, worst))
    if Z == 5000 and worst > 0.10: Q1ok = False
say("   Q1 %s" % ("CONFIRMED" if Q1ok else "DID NOT HOLD"))

say("\nQ2 sign of Re[η(ρ−2)/η′(ρ)] (σ-direction of the helix displacement) for the first 200 zeros")
neg = pos = 0; firstpos = None
for j, r in enumerate(zeros):
    v = eta(r - 2) / etap(r)
    if v.real < 0: neg += 1
    else:
        pos += 1
        if firstpos is None: firstpos = (j + 1, float(r.imag), complex(v))
say("   negative (event inside, σ < ½): %d   positive: %d" % (neg, pos))
if firstpos: say("   first positive: zero #%d γ=%.3f value %+.3f%+.3fi" % (firstpos[0], firstpos[1], firstpos[2].real, firstpos[2].imag))
say("   also |η(ρ−2)/η′(ρ)| for the 9 events in [20,50]: %s" % " ".join("%.1f" % abs(complex(eta(r - 2) / etap(r))) for r in zeros if 20 < r.imag < 50))

say("\nQ3 chart manufactured line at N = 20000: |η(s)| / (½ N^{−σ}) at every event with σ < 0")
N = 20000
txt = open("tmp/att650_results.txt").read()
blk = txt.split("CHART Z=20000")[1].split("\n====")[0]
worst = 0.0; cnt = 0
for m in re.finditer(r"OFF\s+σ=(-?\d+\.\d+) y=(\d+\.\d+)", blk):
    sg, y = float(m.group(1)), float(m.group(2))
    if sg >= 0: continue
    s = mp.mpc(sg, y)
    ratio = abs(eta(s)) / (0.5 * N ** (-sg)); worst = max(worst, abs(float(ratio) - 1)); cnt += 1
say("   events with σ<0: %d ; max |ratio − 1| = %.4f ; predicted σ ≈ −log(2|η|)/log N ; spacing 2π/log N = %.3f" % (cnt, worst, 2 * math.pi / math.log(N)))
say("   Q3 %s" % ("CONFIRMED" if worst < 0.01 else "DID NOT HOLD"))
