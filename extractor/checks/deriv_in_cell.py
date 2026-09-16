"""DOES Xi' actually vanish inside the extractor's bracket [a,b]?

The capstone assumes Xi' != 0 on the cell.  Between two consecutive zeros of Xi there is
necessarily a critical point (Rolle).  The bracket [a,b] straddles gamma_i; if it reaches
past either flanking extremum, Xi' vanishes inside it and the hypothesis is NOT met.
"""
import sys, math
sys.path.insert(0, 'extractor')
import mpmath as mp
from helix_extractor import Bank, Clocks, calibrate, height
mp.mp.dps = 40

def Xi(z):
    z = mp.mpmathify(z)
    s = mp.mpf(1)/2 + mp.mpc(0,1)*z
    return (mp.mpf(1)/4 + z**2) * mp.pi**(-s/2) * mp.gamma(s/2) * mp.zeta(s)
def XiRe(t): return mp.re(Xi(t))
def dXiRe(t):
    h = mp.mpf(10)**(-18)
    return (XiRe(t+h)-XiRe(t-h))/(2*h)

bank  = Bank(delta=math.pi/3, tol=1e-16)
cbank = Bank(delta=math.pi/3, tol=1e-6)
clocks = Clocks(100); anchor = calibrate(bank, clocks)

for i in (1, 10, 100, 1000):
    r0 = height(i, bank, cbank, clocks, anchor, mm=9)
    a, b = mp.mpf(r0['a']), mp.mpf(r0['b'])
    lo, hi = mp.mpf(r0['lo']), mp.mpf(r0['hi'])
    g = mp.mpf(r0['jet'])
    NS = 60
    ts = [a + (b-a)*mp.mpf(k)/NS for k in range(NS+1)]
    ds = [dXiRe(t) for t in ts]
    signs = [mp.sign(d) for d in ds]
    flips = [(ts[k], ts[k+1]) for k in range(NS) if signs[k]*signs[k+1] < 0]
    # same test on the NARROW sub-bracket [lo,hi] that stage 5 actually returns
    ts2 = [lo + (hi-lo)*mp.mpf(k)/NS for k in range(NS+1)]
    d2 = [dXiRe(t) for t in ts2]
    s2 = [mp.sign(x) for x in d2]
    flips2 = [(ts2[k], ts2[k+1]) for k in range(NS) if s2[k]*s2[k+1] < 0]
    print(f"i = {i}:  bracket [a,b] width {mp.nstr(b-a,4)},  sub-bracket width {mp.nstr(hi-lo,4)}")
    print(f"     Xi' sign changes in [a,b]      : {len(flips)}"
          + ("  <-- hypothesis VIOLATED" if flips else "  (none)"))
    print(f"     Xi' sign changes in [lo,hi]    : {len(flips2)}"
          + ("  <-- VIOLATED" if flips2 else "  (none)"))
    if flips:
        for (x,y) in flips[:2]:
            print(f"        critical point in [{mp.nstr(x,12)}, {mp.nstr(y,12)}]"
                  f"   (gamma_i = {mp.nstr(g,12)})")
    print()
