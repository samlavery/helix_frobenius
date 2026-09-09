#!/usr/bin/env python3
"""att683 — third retry at the transfer step in AXIS-native form: rung 1 (Laguerre L = Z'^2 − Z Z'' ≥ 0) for the
   unit-gauge fiber's real readout Z_W(t) = Re[e^{iϑ} F_W(½+it) / (1 − 2^{½−it})], W = 400 (matches Hardy Z).
   Bank identity (exact, for F = Σ a_n cos φ_n with φ_n' = θ_n): L(F) = ¼Σ_{m,n} a_m a_n[(θ_m+θ_n)²cos((θ_m−θ_n)t) + (θ_m−θ_n)²cos((θ_m+θ_n)t)];
   DC = Σ a_n² θ_n² > 0 (m = n), AC = cross terms. Rung 1 ⟺ the AC never overwhelms the DC. Measured: min L/DC on [10,100]."""
import mpmath as mp, numpy as np
mp.mp.dps = 20
out = open("tmp/att683_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
W = 400
n = np.arange(1, W); w = np.exp(1 - 1/(1 - (n/W)**2)); c = (-1.0)**(n+1)*w/np.sqrt(n); ln = np.log(n)
def G(t):
    F = np.sum(c*np.exp(-1j*t*ln)); th = float(mp.siegeltheta(t))
    return np.exp(1j*th)*F/(1 - 2**(0.5-1j*t))
def Z(t): return G(t).real
h = 1e-3
def L(t):
    z0 = Z(t); zp = Z(t+h); zm = Z(t-h)
    z1 = (zp - zm)/(2*h); z2 = (zp - 2*z0 + zm)/(h*h)
    return z1*z1 - z0*z2
def DC(t):
    th1 = float(mp.diff(mp.siegeltheta, t)); a = w/np.sqrt(n)
    return float(np.sum(a*a*(th1 - ln)**2))
ts = np.arange(10, 100, 0.05); Ls = np.array([L(t) for t in ts]); DCs = np.array([DC(t) for t in ts[::20]])
ratios = Ls/np.repeat(DCs, 20)[:len(Ls)]
i = int(np.argmin(ratios))
zeros = [float(mp.zetazero(k).imag) for k in range(1, 30)]
say("check: Z_W(50) = %.8f vs Hardy Z(50) = %.8f" % (Z(50.0), float(mp.siegelz(50))))
say("rung 1 on [10,100] (W=400): min L = %.4e at t=%.2f ; min L/DC = %.4f at t=%.2f ; negative samples: %d/%d"
    % (Ls.min(), ts[int(np.argmin(Ls))], ratios[i], ts[i], int((Ls < 0).sum()), len(Ls)))
say("   nearest events to the minimum: %s ; closest event pair in range: gap %.3f at %.3f"
    % ([round(g,3) for g in zeros if abs(g - ts[i]) < 4], min(zeros[k+1]-zeros[k] for k in range(28)), zeros[int(np.argmin([zeros[k+1]-zeros[k] for k in range(28)]))]))
say("   typical: median L/DC = %.3f ; DC(50) = %.3f ; L(50) = %.3f" % (float(np.median(ratios)), DC(50.0), L(50.0)))
