"""(O4) The two-ended head in float64: Riemann-Siegel main sum, vectorised.

Z(t) = 2 * sum_{n<=N} cos(theta(t) - t log n)/sqrt(n) + R(t),  N = floor(sqrt(t/2pi)).
The theorems consume only the SIGN of the readout, and u = |w||Gamma_R| Z with both factors
positive, so a float64 RS main sum suffices wherever |Z| exceeds the RS remainder.
Measured: term counts, wall time, and sign agreement against the one-ended lane bank.
"""
import sys, math, time
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import numpy as np, mpmath as mp
from helix_extractor import Bank, winding, readout
mp.mp.dps = 25

def rs_N(t): return int(math.floor(math.sqrt(t/(2*math.pi))))

_cache = {}
def Z_rs_f64(t):
    """RS main sum + first correction term, all float64."""
    N = rs_N(t)
    if N not in _cache:
        n = np.arange(1, N+1, dtype=np.float64)
        _cache[N] = (np.log(n), 1.0/np.sqrt(n))
    logn, invsq = _cache[N]
    th = winding(t)                      # theta(t), exact via loggamma
    main = 2.0*np.sum(np.cos(th - t*logn)*invsq)
    # first RS correction: (-1)^{N-1} (t/2pi)^{-1/4} C0(p),  p = frac(sqrt(t/2pi))
    a = math.sqrt(t/(2*math.pi)); p = a - math.floor(a)
    C0 = math.cos(2*math.pi*(p*p - p - 1.0/16.0))/math.cos(2*math.pi*p)
    corr = ((-1)**(N-1)) * (t/(2*math.pi))**(-0.25) * C0
    return main + corr

bank = Bank(delta=math.pi/3, tol=1e-16)

print("=== accuracy of the float64 RS against mpmath.siegelz ===")
for t in (143.0, 1000.0, 7005.06, 14000.0):
    a = Z_rs_f64(t); b = float(mp.siegelz(mp.mpf(t)))
    print(f"  t={t:>10.2f}   RS={a:+.10f}   siegelz={b:+.10f}   |diff|={abs(a-b):.2e}")

print()
print("=== sign agreement with the one-ended lane bank (400 probes per height) ===")
for T in (143.0, 1000.0, 7005.06, 14000.0):
    bad = 0
    for k in range(400):
        t = T + 0.0037*k
        if math.copysign(1, readout(bank, t)) != math.copysign(1, Z_rs_f64(t)): bad += 1
    print(f"  T={T:>10.2f}   disagreements: {bad}/400")

print()
print("=== wall time, 2000 sign evaluations ===")
for T in (7005.06, 576000.0):
    X1 = bank.head(T); N = rs_N(T)
    t0=time.time()
    for k in range(2000): readout(bank, T+0.001*k)
    tb = time.time()-t0
    Z_rs_f64(T)   # warm the cache
    t0=time.time()
    for k in range(2000): Z_rs_f64(T+0.001*k)
    tr = time.time()-t0
    print(f"  T={T:>10.1f}  one-ended {X1:>7d} terms: {tb:7.3f}s   "
          f"two-ended {N:>5d} terms: {tr:7.3f}s   speedup {tb/tr:6.1f}x")
