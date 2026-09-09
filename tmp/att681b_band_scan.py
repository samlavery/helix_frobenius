#!/usr/bin/env python3
"""att681b — the FINITE BAND LAW test: for fixed small head Z, does F_Z have any atom in the band 0.55 ≤ Re s ≤ 0.95 at ANY
   height up to 5000 (the almost-periodic / Turán regime, far beyond the head)?  Winding-number census on boxes.
   PRE-REGISTERED: for Z = 12.5 band atoms EXIST at some heights ≤ 5000 (Turán-type); Z = 25, 50 likewise (fewer per height)."""
import numpy as np
out = open("tmp/att681b_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
def fiber(Z):
    n = np.arange(1, int(np.ceil(Z))); n = n[n < Z]
    w = np.exp(1 - 1/(1 - (n/Z)**2)); c = (-1.0)**(n+1)*w; ln = np.log(n)
    return lambda s: (c[None,:]*np.exp(-np.asarray(s)[:,None]*ln[None,:])).sum(axis=1)
def winding(F, a, b, t0, t1, m=3000):
    pts = np.concatenate([a + 1j*np.linspace(t0, t1, m), np.linspace(a, b, m//4) + 1j*t1,
                          b + 1j*np.linspace(t1, t0, m), np.linspace(b, a, m//4) + 1j*t0])
    v = F(pts); ph = np.unwrap(np.angle(v))
    return int(np.round((ph[-1] - ph[0] + (np.angle(v[0]) - np.angle(v[-1])) ) / (2*np.pi)))
for Z in (12.5, 25.0, 50.0, 100.0):
    F = fiber(Z); tot = 0; alt = 0; locs = []
    for t0 in np.arange(0, 5000, 25):
        # band box (0.55, 0.95)
        wnd = winding(F, 0.55, 0.95, t0 + 1e-3, t0 + 25 + 1e-3)
        if wnd:
            tot += wnd
            if len(locs) < 5: locs.append((t0, wnd))
        alt += winding(F, 0.95, 1.5, t0 + 1e-3, t0 + 25 + 1e-3)
    say("Z=%6.1f (%2d phasors): band atoms in [0.55,0.95]×[0,5000] = %d   (alternation-side [0.95,1.5]: %d vs 2πk/log2 count %d)   first boxes: %s"
        % (Z, int(np.ceil(Z))-1, tot, alt, int(5000*np.log(2)/(2*np.pi)), locs))
