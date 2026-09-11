#!/usr/bin/env python3
"""att705 — the two-end ratio R_Z(s) = χ_η(s) F_Z(1−s) / F_Z(s) on the far side of the axis.
   G_Z = F_Z (1 + R_Z): the balanced fiber vanishes iff R_Z = −1 (or both ends vanish).  On the axis |R_Z| = 1.
   HERMITE–BIEHLER DOMINATION would be |R_Z| < 1 for Re s > ½ (the helix end dominates the anti-helix end off the
   axis); it would put every zero of G_Z on the axis by a mechanism the frame owns.
   PRE-REGISTERED PREDICTION: domination FAILS — for each δ > 0 the sign of |R_Z| − 1 changes along t (the truncation
   correction −Z^{−2}η(s−2) rotates), so the fraction of t with |R_Z| < 1 lies strictly between 0 and 1; and at the
   off-axis points where |R_Z| = 1 the phase arg R_Z stays away from π — the events are held on the axis by a PHASE
   LOCK, not by modulus domination.  Decision: domination holds at a head iff |R_Z| < 1 at every sampled (δ, t)."""
import numpy as np, mpmath as mp
mp.mp.dps = 25
out = open("tmp/att705_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
def w(u):
    u = np.asarray(u, dtype=float); r = np.zeros_like(u); m = u < 1
    r[m] = np.exp(1 - 1/(1 - u[m]**2)); return r
def F(Z, s):
    s = np.asarray(s, dtype=complex)
    n = np.arange(1, int(np.ceil(Z)) + 1, dtype=float)
    coef = ((-1.0)**(n + 1)) * w(n / Z)
    return np.einsum('n,ns->s', coef, np.exp(-np.outer(np.log(n), s)))
def chi_eta(s):
    s = mp.mpc(s)
    chi = 2**s * mp.pi**(s - 1) * mp.sin(mp.pi * s / 2) * mp.gamma(1 - s)
    return complex(chi * (1 - 2**(1 - s)) / (1 - 2**s))
def R(Z, s_arr):
    s_arr = np.asarray(s_arr, dtype=complex)
    ce = np.array([chi_eta(s) for s in s_arr])
    return ce * F(Z, 1 - s_arr) / F(Z, s_arr)
ts = np.arange(10.0, 50.0, 0.01)
zeta_ords = [float(mp.zetazero(k).imag) for k in range(1, 11)]
for Z in (60, 200, 1000):
    say(f"=== head Z = {Z} ===")
    for d in (0.005, 0.02, 0.05, 0.1, 0.2, 0.3):
        Rv = R(Z, 0.5 + d + 1j*ts)
        r = np.abs(Rv)
        frac_dom = np.mean(r < 1)
        # crossings of |R| = 1 along t, and the phase there
        sgn = np.sign(r - 1); cross = np.where(sgn[:-1]*sgn[1:] < 0)[0]
        phase_dist = []
        for i in cross:
            # linear interpolation of the crossing point; phase of R there, distance from π (mod 2π)
            a, b = r[i]-1, r[i+1]-1
            lam = a/(a-b) if a != b else 0.5
            tc = ts[i] + lam*(ts[i+1]-ts[i])
            Rc = R(Z, [0.5 + d + 1j*tc])[0]
            ph = np.angle(Rc)               # in (−π, π]
            phase_dist.append(min(abs(ph - np.pi), abs(ph + np.pi)))
        phase_dist = np.array(phase_dist) if len(phase_dist) else np.array([np.inf])
        # the ratio at the on-axis zeros' heights, displaced by δ
        r_at_zeros = np.abs(R(Z, [0.5 + d + 1j*g for g in zeta_ords]))
        say(f"δ={d:5.3f}  frac(|R|<1)={frac_dom:.3f}  min|R|-1={np.min(r-1):+.2e}  max|R|-1={np.max(r-1):+.2e}  "
            f"#crossings(|R|=1)={len(cross)}  min dist(arg R, π) at crossings={np.min(phase_dist):.3f} rad  "
            f"|R|-1 at zeros: {np.round(r_at_zeros-1, 4).tolist()}")
