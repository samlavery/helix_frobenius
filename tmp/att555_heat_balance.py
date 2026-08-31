# THE HEAT BALANCE W(h) = 0: primes+geometry vs detector, Gaussian windows.
# h(r) = exp(-(r-t0)^2/(2 s2)) + exp(-(r+t0)^2/(2 s2))   (even)
# hhat(u) = (2*sig/sqrt(2pi)) * exp(-sig^2 u^2/2) * cos(t0 u)
# Explicit formula (calibration-locked below):
#   Sum_rho h(gamma) = (1/2pi) Int h(r)*[Re psi(1/4+ir/2) - log pi] dr
#                      + h(i/2) + h(-i/2)  - 2 Sum_n Lambda(n) n^{-1/2} hhat(log n)
# Detector side on verified range = zero sum (flips = simple on-line zeros).
# Pre-registered: |W| < 1e-8 at all centers => balance holds where checkable;
# structured residual => isolate.  Calibration window t0=0 must land < 1e-8
# or the normalization is wrong (fix ONCE, no refitting per-window).
from mpmath import mp, mpf, mpc, exp, cos, sqrt, pi, log, quad, digamma, zetazero, inf, re
mp.dps = 15
sig = mpf(6); s2 = sig*sig
zeros = []
n = 1
while True:
    g = zetazero(n).imag
    if g > 120: break
    zeros.append(g); n += 1
print(f"zeros loaded: {len(zeros)} up to {float(zeros[-1]):.2f}")
# von Mangoldt up to N where hhat(log n) negligible: sig=6: exp(-18*(log n)^2)*...:
# log n = 1.5 -> exp(-40) tiny; N=5 enough?! cos factor doesn't help; but keep N=50.
import sympy
LAM = {m: float(sympy.log(sympy.factorint(m).keys().__iter__().__next__())) if len(sympy.factorint(m))==1 else 0.0 for m in range(2,51)}
def W(t0):
    h  = lambda r: exp(-(r-t0)**2/(2*s2)) + exp(-(r+t0)**2/(2*s2))
    hh = lambda u: (2*sig/sqrt(2*pi))*exp(-s2*u*u/2)*cos(t0*u)
    zside = sum(h(g) for g in zeros)          # + h(-g) covered by evenness pairing:
    zside = 2*sum(exp(-(g-t0)**2/(2*s2)) + exp(-(g+t0)**2/(2*s2)) for g in zeros)/2
    # NOTE: rho and conj(rho) both count: zeros list has gamma>0 only -> h(gamma)+h(-gamma) = h even => 2h(gamma)? no: h already even-sym; each zero pair (gamma,-gamma) contributes h(gamma)+h(-gamma) = 2h(gamma)... but h(gamma) itself contains both bumps. Count: sum over ALL zeros (\pm gamma): = sum_{g>0} [h(g)+h(-g)] = 2*sum h(g).
    zside = 2*sum(h(g) for g in zeros)
    gterm = (1/(2*pi))*quad(lambda r: h(r)*(re(digamma(mpc(0.25, r/2))) - log(pi)), [-inf, 0, inf])
    poleterm = h(mpc(0,0.5)) + h(mpc(0,-0.5))
    pterm = 2*sum(LAM[m]/sqrt(m)*hh(log(m)) for m in range(2,51) if LAM[m] > 0)
    arith = gterm + poleterm.real - pterm
    return zside - arith    # W* = zero-side minus arithmetic side (should be 0 by EF);
                            # detector = zero side on verified range, so W = this.
for t0 in [0, 20, 30, 40, 50, 60]:
    w = W(mpf(t0))
    print(f"t0={t0:>3}: W = {float(w):>14.6e}")
