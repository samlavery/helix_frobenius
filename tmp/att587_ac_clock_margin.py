#!/usr/bin/env python3
"""
att587 — THE AC ≤ CLOCK LAW, measured (2026-09-03).
  D_R(t) = ϑ′(t)/π + END_x(t) − C_x(t)/π ≥ 0 (RH ⟺, 568 with the Weil-class converse).
  END_x(t) = Re[(x^{½−it} − 1)/(L(½−it)²)]/π is the pole's DC = the smooth main term of the prime sum,
  so the exact law is   C̃_x(t) := C_x(t) − π·END_x(t) ≤ ϑ′(t)   for all x, t:
  the DC-subtracted Riesz prime clock never exceeds the Γ-clock rate. Margin M_x(t) := ϑ′(t) − C̃_x(t) = π·D_R(t)
  = the Fejér comb (under RH). Report min over t ∈ [10, 300] of M/ϑ′ and where it sits (mid-gap of the widest gap).
PRE-REGISTERED: min M/ϑ′ ∈ (0, 0.1) at x = 10³ and smaller at 10⁴ (comb ~ 8/(L g²) at mid-gap, g_max ≈ 6.9 first gap…);
  the minimiser lies between two consecutive zeros at the widest local gap.
"""
import sys; sys.path.insert(0, "tmp")
import numpy as np, math, mpmath as mp
from att566_krein_constant import prime_powers, theta_prime_over_pi
zeros = [float(mp.zetazero(k).imag) for k in range(1, 170)]  # up to ~300
ts = np.arange(20.0, 290.0, 0.01)
thp = theta_prime_over_pi(ts)*math.pi   # ϑ′(t)
for x in (1e3, 1e4):
    ns, lams = prime_powers(int(x)); ns = np.array(ns, float); lams = np.array(lams, float); L = math.log(x)
    w = np.maximum(1 - np.log(ns)/L, 0)
    C = np.array([np.sum(w*lams*ns**-0.5*np.cos(t*np.log(ns))) for t in ts])
    s = 0.5 - 1j*ts
    END = ((x**s - 1)/(L*s*s)).real   # π·END_x(t)
    Ctil = C - END
    M = thp - Ctil
    r = M/thp
    i = int(np.argmin(r)); gaps = np.diff(zeros)
    # nearest zeros around the minimiser
    below = max([z for z in zeros if z < ts[i]], default=0.0); above = min([z for z in zeros if z > ts[i]], default=float("inf"))
    print("x = %.0e (L = %.2f): min_t M/ϑ′ = %.4f at t = %.2f (between zeros %.3f and %.3f, gap %.3f) ; M there = %.4f vs comb estimate 8/(L g²) = %.4f ; any M < 0: %s ; widest gap in range %.3f" % (
        x, L, r[i], ts[i], below, above, above - below, M[i], 8/(L*(above-below)**2), bool(np.any(M < 0)), np.max([g for g, z in zip(gaps, zeros[:-1]) if 10 < z < 300])))
