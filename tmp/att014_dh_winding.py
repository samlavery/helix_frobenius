"""ATTEMPT 014, secondary -- re-run the attempt-008 Speiser/Levinson-Montgomery winding test
at MANY more boxes for Davenport-Heilbronn (the standing control with genuinely off-line zeros).

f(s) = 5^{-s} sum_{r=1..5} a_r zeta(s, r/5),  a = [1, XI, -XI, -1, 0],
XI = (sqrt(A^2+B^2)-A)/B,  A = (4/sqrt5) sin(2pi/5),  B = (4/sqrt5) sin(4pi/5).
Off-line pair at 0.80851718 / 0.19148282 + 85.69934849i.

CLAIM UNDER TEST (attempt 008, scoped to two boxes): the Levinson-Montgomery correspondence
   #{zeros of f' with Re < 1/2}  =  #{zeros of f with Re < 1/2}  + O(log T)
holds for DH, i.e. it is FE-driven, not Euler-driven.
NULL (pre-registered): the counts diverge at more boxes, i.e. 008's agreement was a two-box
coincidence and the correspondence is zeta-specific.
"""
import numpy as np, math, sys, time
import mpmath as mp

def P(*a): print(*a); sys.stdout.flush()
A_ = (4/math.sqrt(5))*math.sin(2*math.pi/5); B_ = (4/math.sqrt(5))*math.sin(4*math.pi/5)
XI = (math.sqrt(A_**2+B_**2)-A_)/B_
AV = np.array([1.0, XI, -XI, -1.0, 0.0])
BN = [1/6, -1/30, 1/42, -1/30, 5/66, -691/2730, 7/6]

def hurwitz(s, al, K=7):
    """zeta(s,al), d/ds zeta(s,al) for complex array s and scalar al."""
    s = np.atleast_1d(np.asarray(s, complex))
    N = int(max(40, 2.2*np.abs(s.imag).max() + 40))
    n = np.arange(0, N, dtype=float) + al
    ln = np.log(n)
    E = np.exp(-np.outer(s, ln))
    Z = E.sum(1); Zp = -(E*ln).sum(1)
    A = N + al; lA = math.log(A)
    Z += A**(1-s)/(s-1) + A**(-s)/2
    Zp += -lA*A**(1-s)/(s-1) - A**(1-s)/(s-1)**2 - lA*A**(-s)/2
    for k in range(1, K+1):
        m = 2*k-1
        poch = np.ones_like(s); dp = np.zeros_like(s)
        for j in range(m):
            poch = poch*(s+j); dp = dp + 1.0/(s+j)
        term = BN[k-1]/math.factorial(2*k)*poch*A**(-s-2*k+1)
        Z += term; Zp += term*(dp - lA)
    return Z, Zp

def dh(s):
    s = np.atleast_1d(np.asarray(s, complex))
    Z = np.zeros(s.shape, complex); Zp = np.zeros(s.shape, complex)
    for r in range(1, 6):
        if AV[r-1] == 0: continue
        z, zp = hurwitz(s, r/5.0)
        Z += AV[r-1]*z; Zp += AV[r-1]*zp
    p = 5.0**(-s)
    return p*Z, p*(Zp - math.log(5)*Z)

def winding(fn, comp, sl, sh, tl, th, dt=0.02, dsig=0.002):
    tot = 0.0; mx = 0.0; mn = np.inf
    sg = np.linspace(sl, sh, max(200, int((sh-sl)/dsig)))
    tt = np.linspace(tl, th, max(400, int((th-tl)/dt)))
    for pts in (sg+1j*tl, sh+1j*tt, sg[::-1]+1j*th, sl+1j*tt[::-1]):
        v = fn(pts)[comp]
        mn = min(mn, np.abs(v).min())
        d = np.angle(v[1:]/v[:-1]); tot += d.sum(); mx = max(mx, np.abs(d).max())
    return tot/(2*math.pi), mx, mn

if __name__ == "__main__":
    mp.mp.dps = 25
    P(__doc__)
    z0 = complex(0.80851718, 85.69934849)
    P(f"GATE  |f| at the literature off-line zero {z0}: {abs(dh(np.array([z0]))[0][0]):.3e}")
    for s in (complex(0.3, 40.0), complex(0.45, 120.0), complex(0.25, 250.0)):
        v, vp = [x[0] for x in dh(np.array([s]))]
        mv = sum(mp.mpf(AV[r-1])*mp.zeta(mp.mpc(s.real, s.imag), r/mp.mpf(5)) for r in range(1,6))*mp.mpf(5)**(-mp.mpc(s.real,s.imag))
        P(f"GATE  f({s}) EM {complex(v):.10f}  mpmath {complex(mv):.10f}  diff {abs(complex(v)-complex(mv)):.2e}")
    P("")
    P("WINDING of f and of f' on sigma in (0.02, 0.49)  [strictly LEFT of the critical line]")
    P(f"  {'t-window':>18}{'w(f)':>8}{'w(f-prime)':>12}{'min|f|':>11}{'min|fp|':>11}{'max step':>10}")
    boxes = [(60,80),(80,92),(92,110),(110,130),(130,150),(150,170),(170,190),(190,210),
             (210,230),(230,250),(250,270),(270,290),(290,310),(310,330),(330,350)]
    tf = tp = 0
    for (a, b) in boxes:
        w0, mx0, mn0 = winding(dh, 0, 0.02, 0.49, a, b)
        w1, mx1, mn1 = winding(dh, 1, 0.02, 0.49, a, b)
        tf += int(round(w0)); tp += int(round(w1))
        P(f"  {f'({a},{b})':>18}{w0:>8.3f}{w1:>12.3f}{mn0:>11.2e}{mn1:>11.2e}{max(mx0,mx1):>10.3f}")
    P(f"  TOTAL over t in (60,350):   f: {tf}    f': {tp}    difference {tp-tf}")
    P("")
    P("  refinement check (dt halved) on the three boxes with nonzero count:")
    for (a, b) in boxes:
        w0, _, _ = winding(dh, 0, 0.02, 0.49, a, b)
        if abs(w0) < 0.5: continue
        w0h, _, _ = winding(dh, 0, 0.02, 0.49, a, b, dt=0.01, dsig=0.001)
        w1h, _, _ = winding(dh, 1, 0.02, 0.49, a, b, dt=0.01, dsig=0.001)
        P(f"    ({a},{b}) dt=0.01 -> f: {w0h:.3f}   f': {w1h:.3f}")
