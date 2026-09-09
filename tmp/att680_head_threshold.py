#!/usr/bin/env python3
"""att680 — head law: at which head Z (relative to T) does the warped fiber stop deciding the band (½,1−ε)×(0,T)?
   For Z/T ∈ {4, 2, 1, ½, ¼, ⅛}: Newton atoms from ζ zeros and from the alternation line; Littlewood balance on [½,2]×[0,T]
   detects any EXTRA atom; count right-displaced events.
   PRE-REGISTERED: band atom-free (balance < 0.05, no right-displaced) for Z ≥ T; failures begin at Z ≤ T/2 (relative
   correction (t/2πZ)² reaches 0.1 at Z = T/2)."""
import numpy as np, mpmath as mp
mp.mp.dps = 20
out = open("tmp/att680_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
def make_fiber(Z):
    n = np.arange(1, int(Z)); w = np.exp(1 - 1/(1 - (n/Z)**2)); c = (-1.0)**(n+1)*w; ln = np.log(n)
    F = lambda s: np.sum(c*np.exp(-s*ln))
    return F, (lambda s: mp.mpc(F(complex(s))))
def cont_arg(F, pts):
    prev = np.angle(F(pts[0])); tot = [prev]
    for p in pts[1:]:
        a = np.angle(F(p))
        while a - prev > np.pi: a -= 2*np.pi
        while a - prev < -np.pi: a += 2*np.pi
        tot.append(a); prev = a
    return np.array(tot)
T = 100.3
zz = [float(mp.zetazero(j).imag) for j in range(1, 40) if float(mp.zetazero(j).imag) < T + 2]
for ratio in (4, 2, 1, 0.5, 0.25, 0.125):
    Z = ratio*T; F, Fmp = make_fiber(Z)
    ev = []
    for g in zz:
        try:
            r = complex(mp.findroot(Fmp, mp.mpc(0.5, g), tol=1e-18, maxsteps=60))
            if abs(r.imag - g) < 1.5: ev.append(r)
        except Exception: pass
    alts = []
    k = 1
    while 2*np.pi*k/np.log(2) < T + 2:
        try:
            r = complex(mp.findroot(Fmp, mp.mpc(1.0, 2*np.pi*k/np.log(2)), tol=1e-18, maxsteps=60))
            if abs(r.imag - 2*np.pi*k/np.log(2)) < 3: alts.append(r)
        except Exception: pass
        k += 1
    ev = list({(round(z.real,9), round(z.imag,9)) for z in ev}); ev = [complex(a,b) for a,b in ev]
    alts = list({(round(z.real,9), round(z.imag,9)) for z in alts}); alts = [complex(a,b) for a,b in alts]
    inR = [z for z in ev + alts if 0.5 < z.real < 2 and 0 < z.imag < T]
    lhs = 2*np.pi*sum(z.real - 0.5 for z in inR)
    ev_in = [z for z in ev if 0 < z.imag < T]
    bps = [0] + sorted(z.imag for z in ev_in) + [T]
    I_line = float(mp.quad(lambda t: float(np.log(abs(F(complex(0.5, float(t)))))), bps))
    I_two = float(mp.quad(lambda t: float(np.log(abs(F(complex(2.0, float(t)))))), [0, T/2, T]))
    sig = np.linspace(2, 0.5, 3001)
    A_top = -np.trapz(cont_arg(F, [complex(s, T) for s in sig]), sig)
    J = I_line - I_two + A_top
    right = [z for z in ev_in if z.real > 0.5]
    say("Z/T=%5.3f Z=%4d  events found=%2d/29  right-displaced=%2d  max|Re δ|=%.2e  alt atoms=%2d  J−LHS=%+.3f  (missing right-mass 2πΣ(β−½) if >0)"
        % (ratio, Z, len(ev_in), len(right), max(abs(z.real-0.5) for z in ev_in) if ev_in else 0, len([z for z in alts if z.imag < T]), J - lhs))
    if right: say("    right-displaced at:", ", ".join("%.4f%+.3fi" % (z.real, z.imag) for z in right[:6]))
