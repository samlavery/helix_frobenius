# att648 — the Laguerre form of the real fiber on the carrier, L = Z'^2 - Z Z'', and the two-phasor law.
from mpmath import mp, mpf, siegelz, diff, cos, sin, log, sqrt, pi, findroot, mpc, exp, fabs
import numpy as np
mp.dps = 20
# (1) two-phasor law: f(t) = a cos(wa t) + b cos(wb t + phi). Non-real zeros predicted iff the FASTER phasor is the SMALLER one,
#     at imaginary height y* = log(big/small)/(w_fast - w_slow). Locate a complex zero by Newton from the predicted height.
def f2(t, a, wa, b, wb, phi): return a*cos(wa*t) + b*cos(wb*t + phi)
print("two-phasor law: (a,wa,b,wb) -> predicted y* ; Newton-located zero")
for (a, wa, b, wb) in ((1.0, 1.0, 0.6, 2.3), (0.6, 2.3, 1.0, 1.0), (1.0, 2.3, 0.6, 1.0), (1.0, 1.0, 0.9, 1.7)):
    big, small = (a, b) if a >= b else (b, a); wbig = wa if a >= b else wb; wsmall = wb if a >= b else wa
    faster_is_smaller = (wsmall > wbig)
    ystar = log(big/small)/fabs(wa - wb)
    z = None
    if faster_is_smaller:
        for x0 in np.linspace(0.3, 6.0, 25):
            try:
                r = findroot(lambda t: f2(t, a, wa, b, wb, 0), mpc(x0, ystar))
                if fabs(f2(r, a, wa, b, wb, 0)) < 1e-12 and fabs(r.imag) > 1e-6: z = r; break
            except Exception: pass
    print("   a=%.1f wa=%.1f b=%.1f wb=%.1f : faster-is-smaller=%s  y*=%.4f  zero=%s" % (a, wa, b, wb, faster_is_smaller, float(ystar), (str(z.real)[:7]+" + "+str(z.imag)[:7]+"i") if z is not None else "none sought (co-monotone)"))
# (2) Laguerre form of Hardy Z on the carrier: L(t) = Z'^2 - Z Z'', normalized by (Z^2 + Z'^2) and by the density theta'(t)
def Z(t): return siegelz(t)
def L(t):
    z = Z(t); z1 = diff(Z, t); z2 = diff(Z, t, 2)
    return z1*z1 - z*z2, z, z1
ts = np.linspace(10, 120, 1101)
mins = []
for t in ts:
    Lt, z, z1 = L(mpf(t))
    mins.append((float(Lt), float(z), float(z1), t))
Lmin = min(mins, key=lambda r: r[0])
print("Laguerre form of Z on [10,120] (1101 points): min L = %.4e at t = %.2f (Z=%.3e, Z'=%.3e); count L<0: %d" % (Lmin[0], Lmin[3], Lmin[1], Lmin[2], sum(1 for r in mins if r[0] < 0)))
# normalized phase velocity phi' = L/(Z^2+Z'^2) against the local density theta'(t)/... report min of L/((Z^2+Z'^2)) / (0.5*log(t/2pi))
nv = [(r[0]/(r[1]**2 + r[2]**2)) / (0.5*np.log(r[3]/(2*np.pi))) for r in mins if (r[1]**2 + r[2]**2) > 1e-30]
print("normalized phase velocity L/((Z^2+Z'^2)·½log(t/2π)): min %.4f  max %.4f  mean %.4f" % (min(nv), max(nv), sum(nv)/len(nv)))
