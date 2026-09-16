"""Validation harness for the height extractor: exhaustive low indices + spot checks high.

PRE-REGISTERED: every index must (a) reach Count(a)=i-1, Count(b)=i, (b) return a CERTIFIED
enclosure, (c) contain mpmath's zetazero(i).  Any failure is reported, not averaged away.
"""
import sys, os, math, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
from helix_extractor import Bank, Clocks, calibrate, height
mp.mp.dps = 30

bank  = Bank(delta=math.pi/3, tol=1e-16)
cbank = Bank(delta=math.pi/3, tol=1e-6)
clocks = Clocks(100)
anchor = calibrate(bank, clocks)

def run(idxs, verify=True, label=""):
    bad = []
    t0 = time.time()
    for i in idxs:
        r = height(i, bank, cbank, clocks, anchor, mm=9)
        ok = r['count_ok'] and r['certified']
        if verify:
            ref = float(mp.im(mp.zetazero(i)))
            ok = ok and (r['lo'] <= ref <= r['hi'])
        if not ok:
            bad.append((i, r['count_ok'], r['certified']))
    dt = time.time() - t0
    print(f"{label}: {len(idxs)} indices, {len(bad)} failures, {dt:.1f}s "
          f"({len(idxs)/max(dt,1e-9):.1f}/s)")
    for b in bad[:10]:
        print(f"    FAIL i={b[0]} count_ok={b[1]} certified={b[2]}")
    return len(bad)

total_bad = 0
total_bad += run(list(range(1, 201)), True, "exhaustive 1..200")
random.seed(20260916)
mid = sorted(random.sample(range(201, 20001), 90))
total_bad += run(mid, True, "random 201..20000 (90)")
hi = [50000, 123456, 314159, 500000, 1000000]
total_bad += run(hi, True, "spot checks to 1e6")
lehmer = [6709, 6710]
total_bad += run(lehmer, True, "Lehmer's pair")
print(f"\nTOTAL: {200+90+5+2} indices checked, {total_bad} failures")
