#!/usr/bin/env python3
"""att681c — fate of a band atom as the head rises past it. At Z = 100, locate the band atoms in 0.55 ≤ Re ≤ 0.95,
   175 ≤ t ≤ 300 (above the head); then continue each in Z up to 4t. Does it (a) cross the carrier leftward
   (F_Z(½+it) = 0 at some Z), (b) converge to the alternation line, or (c) rise with the head?
   PRE-REGISTERED: (a) — the band atom crosses the carrier as the head passes its height."""
import numpy as np
out = open("tmp/att681c_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
def fiber(Z):
    n = np.arange(1, int(np.ceil(Z))); n = n[n < Z]
    w = np.exp(1 - 1/(1 - (n/Z)**2)); c = (-1.0)**(n+1)*w; ln = np.log(n)
    F = lambda s: np.sum(c*np.exp(-s*ln)); dF = lambda s: np.sum(-ln*c*np.exp(-s*ln))
    return F, dF
def newton(F, dF, s0, tol=1e-12, maxit=60):
    s = s0
    for _ in range(maxit):
        f = F(s); d = dF(s)
        if d == 0: return None
        ds = f/d; s -= ds
        if abs(ds) < tol: return s
    return None
Z0 = 100.0; F, dF = fiber(Z0); atoms = []
for t in np.arange(175, 300, 1.0):
    for sig in (0.6, 0.75, 0.9):
        r = newton(F, dF, complex(sig, t))
        if r is not None and 0.55 <= r.real <= 0.95 and 175 <= r.imag <= 300 and all(abs(r - a) > 1e-6 for a in atoms):
            atoms.append(r)
atoms.sort(key=lambda z: z.imag)
say("Z=100: band atoms in [0.55,0.95]×[175,300]: %d" % len(atoms))
for a in atoms[:12]:
    Z = Z0; s = a; path = [(Z, s)]; crossing = None; lost = None
    while Z < 4*a.imag:
        dZ = 0.5; Zn = Z + dZ; F, dF = fiber(Zn); sn = newton(F, dF, s); tries = 0
        while (sn is None or abs(sn - s) > 0.25) and tries < 8:
            dZ /= 2; Zn = Z + dZ; F, dF = fiber(Zn); sn = newton(F, dF, s); tries += 1
        if sn is None or abs(sn - s) > 0.25: lost = Z; break
        if crossing is None and (sn.real - 0.5)*(s.real - 0.5) < 0: crossing = (Zn, sn)
        Z, s = Zn, sn; path.append((Z, s))
    minre = min(p[1].real for p in path); fin = path[-1][1]
    say("atom %.4f%+.3fi: crossing %s | min Re %.3f | end Z=%.1f at %.4f%+.3fi (Z/t=%.2f) %s"
        % (a.real, a.imag, ("at Z=%.2f (Z/t=%.3f), s=%.5f%+.4fi" % (crossing[0], crossing[0]/crossing[1].imag, crossing[1].real, crossing[1].imag)) if crossing else "NONE",
           minre, path[-1][0], fin.real, fin.imag, path[-1][0]/fin.imag, ("LOST at Z=%.1f" % lost) if lost else ""))
