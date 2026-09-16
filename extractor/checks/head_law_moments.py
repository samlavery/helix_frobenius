"""Does the head law hold uniformly in the MOMENT order r?  (O3 is about the jets.)
M_r = sum_n taper * (-1)^{n-1} (log x_n)^r x_n^{-s}.  Reference: same sum at a much
larger head.  PRE-REGISTERED: report the observed -ln(err)/s per r; the printed claim
of uniformity in r stands only if the ranges overlap.
"""
import math
from mpmath import mp, mpf, mpc, exp, log, sqrt, pi, fabs
mp.dps = 60

def taper_mp(u, a=mpf('0.5')):
    if u <= a: return mpf(1)
    if u >= 1: return mpf(0)
    x = (1-u)/(1-a); f1 = exp(-1/x); f2 = exp(-1/(1-x))
    return f1/(f1+f2)

def moments(T, X, delta, rmax):
    s = mpf(1)/2 + mpc(0,1)*T
    out = [mpc(0)]*(rmax+1)
    for n in range(1, X+1):
        x = delta*n; lx = log(x)
        amp = taper_mp(mpf(n)/X) * (1 if n % 2 == 1 else -1)
        base = amp*exp(-s*lx)
        cur = base
        for r in range(rmax+1):
            out[r] += cur
            cur *= lx
    return out

T = mpf(143); delta = pi/3; R = 4
ref = moments(T, 1400, delta, R)     # far past the threshold: the reference
base = int(math.ceil(2.0*float(T)/math.pi))
print(f"{'r':>3} " + " ".join(f"{'s='+str(round(math.sqrt(math.pi*(base+e)/2-float(T)),1)):>10}" for e in (60,120,200,292)))
ranges = {}
for r in range(R+1):
    row = []
    for e in (60, 120, 200, 292):
        X = base + e
        m = moments(T, X, delta, R)
        err = fabs(m[r]-ref[r])/fabs(ref[r])
        s = math.sqrt(math.pi*X/2 - float(T))
        row.append(-float(log(err))/s)
    ranges[r] = (min(row), max(row))
    print(f"{r:>3} " + " ".join(f"{v:>10.4f}" for v in row))
print()
lo = min(v[0] for v in ranges.values()); hi = max(v[1] for v in ranges.values())
print(f"across r = 0..{R}: -ln(err)/s in [{lo:.4f}, {hi:.4f}]")
print("uniform in r?", "YES (ranges overlap)" if hi-lo < 0.25 else "NO -- r-dependent")
