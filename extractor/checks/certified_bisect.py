"""(O3) With certified signs, the jets are a SPEED optimisation only.

Bisection driven by CERTIFIED signs narrows the enclosure to the evaluator's precision
without using the jets at all.  So the finite-bank alpha,beta affect neither soundness nor
the achievable narrowness -- only the number of evaluations spent getting there.
"""
import sys, math
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from certified_zeta import zeta_enclosure
from mpmath import mp, mpf, mpc, fabs, re as mre
from helix_extractor import Bank, Clocks, calibrate, height
mp.dps = 60

def Z_sign_certified(t):
    """returns +1/-1 if the sign of Hardy's Z is PROVED at t, else None."""
    t = mpf(t); s = mpf(1)/2 + mpc(0,1)*t
    zv, zr = zeta_enclosure(s)
    th = mp.im(mp.loggamma(mpf(1)/4 + mpc(0,1)*t/2)) - (t/2)*mp.log(mp.pi)
    Z = mre(mp.exp(mpc(0,1)*th)*zv)
    rad = zr + fabs(zv)*(fabs(th)+1)*mpf(10)**(-mp.dps)
    if fabs(Z) <= rad: return None
    return 1 if Z > 0 else -1

bank  = Bank(delta=math.pi/3, tol=1e-16)
cbank = Bank(delta=math.pi/3, tol=1e-6)
clocks = Clocks(100); anchor = calibrate(bank, clocks)

print(f"{'i':>7} {'start width':>13} {'certified width':>17} {'steps':>7} {'digits':>8}")
for i in (1, 10, 100, 1000):
    r0 = height(i, bank, cbank, clocks, anchor, mm=9)
    lo, hi = mpf(r0['lo']), mpf(r0['hi'])
    w0 = hi - lo
    slo = Z_sign_certified(lo); shi = Z_sign_certified(hi)
    assert slo is not None and shi is not None and slo != shi
    steps = 0
    for _ in range(200):
        m = (lo+hi)/2
        sm = Z_sign_certified(m)
        if sm is None: break          # evaluator precision reached
        steps += 1
        if sm == slo: lo = m
        else: hi = m
        if hi - lo < mpf(10)**(-50): break
    w = hi - lo
    print(f"{i:>7} {mp.nstr(w0,4):>13} {mp.nstr(w,4):>17} {steps:>7} "
          f"{int(-mp.log(w,10)):>8}")
print()
print("Narrowing is limited by the CERTIFIED EVALUATOR, not by the bank's alpha,beta.")
print("=> O3's two constants govern evaluation COUNT only: not soundness, not narrowness.")
