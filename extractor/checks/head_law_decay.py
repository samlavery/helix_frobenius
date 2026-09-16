"""Head-law decay constant, measured in HIGH PRECISION so the error can actually fall.

The float64 bank saturates near 1e-13 relative, so a double-precision run cannot see the
decay at all -- it measures its own rounding floor.  Here the bank is summed in mpmath.

Claim in print: rel err ~ exp(-c s), s = sqrt(pi X/2 - T), with -ln(err)/s in [1.418,1.476].
PRE-REGISTERED: report the OBSERVED range; if it excludes [1.418,1.476] the printed
interval is refuted and must be replaced by what is measured.
"""
import math
from mpmath import mp, mpf, mpc, exp, log, sqrt, pi, zeta, fabs
mp.dps = 60

def taper_mp(u, a=mpf('0.5')):
    if u <= a: return mpf(1)
    if u >= 1: return mpf(0)
    x = (1-u)/(1-a)
    f1 = exp(-1/x); f2 = exp(-1/(1-x))
    return f1/(f1+f2)

def bank_mp(T, X, delta):
    s = mpf(1)/2 + mpc(0,1)*T
    tot = mpc(0)
    for n in range(1, X+1):
        x = delta*n
        amp = taper_mp(mpf(n)/X) * (1 if n % 2 == 1 else -1)
        tot += amp * exp(-s*log(x))
    return tot

def reference(T, delta):
    s = mpf(1)/2 + mpc(0,1)*T
    return delta**(-s) * (1 - mpf(2)**(1-s)) * zeta(s)

rows=[]
print(f"{'T':>7} {'delta':>8} {'X':>7} {'s':>7} {'rel err':>12} {'-ln(err)/s':>11}")
for T in (mpf(143), mpf(500), mpf(1500)):
    for delta in (pi/3, mpf(1)):
        ref = reference(T, delta); aref = fabs(ref)
        base = int(math.ceil(2.0*float(T)/math.pi))
        for extra in (20, 60, 120, 200, 300, 450):
            X = base + extra
            val = bank_mp(T, X, delta)
            err = fabs(val - ref)/aref
            arg = math.pi*X/2 - float(T)
            if arg <= 0 or err == 0: continue
            s = math.sqrt(arg)
            r = -float(log(err))/s
            rows.append((float(T), float(delta), X, s, float(err), r))
            print(f"{float(T):>7.0f} {float(delta):>8.4f} {X:>7d} {s:>7.2f} {float(err):>12.2e} {r:>11.4f}")

rs=[r[5] for r in rows]; errs=[r[4] for r in rows]
print()
print(f"observed -ln(err)/s: [{min(rs):.4f}, {max(rs):.4f}] over {len(rows)} samples")
print(f"error range: {min(errs):.2e} .. {max(errs):.2e} = "
      f"{math.log10(max(errs)/min(errs)):.1f} orders")
ok = min(rs) >= 1.418 and max(rs) <= 1.476
print("printed [1.418,1.476]:", "CONFIRMED" if ok else "REFUTED -- must be replaced by observed")
