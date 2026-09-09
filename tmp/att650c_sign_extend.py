#!/usr/bin/env python3
"""att650c — extend Q2: sign of Re[η(ρ−2k)/η′(ρ)] over the first 1000 zeros, k = 1 (house window) and k = 2.
PRE-REGISTERED: k=1 — after 200/200 negative, predict ≥ 990/1000 negative (a structure, not a law);
k=2 — predict mixed."""
import mpmath as mp, time
mp.mp.dps = 20
out = open("tmp/att650c_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
t0 = time.time()
neg = {1: 0, 2: 0}; pos = {1: 0, 2: 0}; firstpos = {1: None, 2: None}
minratio = None
for j in range(1, 1001):
    r = mp.zetazero(j); d = mp.diff(mp.altzeta, r)
    for k in (1, 2):
        v = mp.altzeta(r - 2 * k) / d
        if v.real < 0: neg[k] += 1
        else:
            pos[k] += 1
            if firstpos[k] is None: firstpos[k] = (j, float(r.imag), complex(v))
    v1 = mp.altzeta(r - 2) / d
    q = -v1.real / abs(v1)          # cos of the angle from the negative real axis
    if minratio is None or q < minratio[0]: minratio = (float(q), j, float(r.imag))
say("first 1000 zeros (%.0fs): k=1 negative %d positive %d ; k=2 negative %d positive %d" % (time.time() - t0, neg[1], pos[1], neg[2], pos[2]))
for k in (1, 2):
    if firstpos[k]: say("   k=%d first positive: zero #%d γ=%.3f  value %+.3f%+.3fi" % (k, firstpos[k][0], firstpos[k][1], firstpos[k][2].real, firstpos[k][2].imag))
say("   k=1 smallest −Re/|·| (closest approach to the axis): %.4f at zero #%d γ=%.3f" % minratio)
