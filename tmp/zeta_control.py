import math, sys
import numpy as np
sys.path.insert(0, "tmp")
from amp_cross import eta_sweep

print("[2] zeta CONTROL at the Delta window: t in [200,500], span 300 (same as GL(2) run)")
taus, F = eta_sweep(200.0, 500.0, 0.01, 500.0)   # de-modulated |zeta|
absF = np.abs(F)
x = np.log(np.maximum(absF, np.percentile(absF, 1.0))); x -= x.mean()
P = np.abs(np.fft.rfft(x * np.hanning(len(x))))**2
freq = 2*math.pi*np.fft.rfftfreq(len(x), d=0.01)
res = 2*math.pi/300
targets = [("ln2",2),("ln3",3),("ln4",4),("ln5",5),("ln7",7),("ln11",11),("ln13",13),("ln18*",18)]
for name, nn in targets:
    om = math.log(nn)
    pk = np.abs(freq-om) < max(0.012, 2*res)
    bg = (np.abs(freq-om) > 0.08) & (np.abs(freq-om) < 0.25)
    for _, n2 in targets:
        if n2 != nn: bg &= np.abs(freq - math.log(n2)) > 0.04
    print(f"    {name:>6}: {float(P[pk].max()/np.median(P[bg])):>12.1f}")
