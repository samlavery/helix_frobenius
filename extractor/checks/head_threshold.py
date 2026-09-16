"""X_min/(2T/pi) as a function of the target tolerance.

The head law X > 2T/pi is a DESIGN rule (keep the lane saddle n*=T/pi inside the window's
flat core).  Is it also the empirical accuracy threshold?  Sweep tolerance and height.
"""
import sys, math
sys.path.insert(0, 'extractor')
import numpy as np, mpmath as mp
from helix_extractor import Bank
mp.mp.dps = 30
delta = math.pi/3
bank = Bank(delta=delta, tol=1e-16)

def reference(T):
    s = mp.mpf(1)/2 + 1j*mp.mpf(T)
    return mp.mpf(delta)**(-s) * (1 - mp.mpf(2)**(1-s)) * mp.zeta(s)

print(f"{'T':>8} " + " ".join(f"{'tol=1e-'+str(k):>12}" for k in (6,9,12)))
for T in (500.0, 1500.0, 5000.0, 15000.0):
    ref = reference(T); aref = abs(ref); pred = 2.0*T/math.pi
    row=[]
    for k in (6,9,12):
        tol = 10.0**(-k)
        def ok(X):
            v = complex(bank.moments(T, X=int(X), mmax=0)[0])
            return abs(mp.mpc(v)-ref)/aref <= tol
        lo, hi = 8, int(pred*4)+400
        if not ok(hi): row.append(float('nan')); continue
        while hi-lo > 1:
            mid=(lo+hi)//2
            if ok(mid): hi=mid
            else: lo=mid
        row.append(hi/pred)
    print(f"{T:>8.0f} " + " ".join(f"{v:>12.4f}" for v in row))
print()
print("ratio > 1 => the 2T/pi design rule is also the accuracy threshold;")
print("ratio < 1 => at that tolerance the rule is CONSERVATIVE, not necessary.")
