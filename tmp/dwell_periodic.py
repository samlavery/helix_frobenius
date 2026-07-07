#!/usr/bin/env python3
"""
dwell_periodic.py -- test the periodic warp  cross -> run -> dwell -> cross  on the real
carrier.  Claim (Sam): with the dwell laid in every period (= complete bank), every crossing
vanishes; delete the dwells (Altug's skip) and every crossing DISPLACES; and the reopening
rate (reverb) on the departure side is UNCHANGED either way (the dwell is only in the approach).

carrier = focal_closure chi3; closure c(Z) at readout y=log Z.
  complete = dwells intact (every value present)      -> each crossing should close
  cut      = perfect-square values deleted (no dwell)  -> each crossing displaced/shallow
reopening rate k: fit c(y) ~ A |y-y0|^k on the DEPARTURE side (y>y0) of each complete crossing,
and on the cut bank's own nearest crossing, to check the reverb exponent is the same.
Run: python3 tmp/dwell_periodic.py   (writes tmp/dwell_periodic_results.txt)
"""
import math, os, sys
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import focal_closure as FC
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "dwell_periodic_results.txt")

def make_skip(base):
    def make(N):
        c, k = base.make(N); c = c.copy(); m = 1
        while m*m <= N: c[m*m] = 0.0; m += 1
        return c, k
    return FC.Family(base.name+"_cut", base.kind, make, max_N=base.max_N)

def curve(fam, y0, y1, n):
    ys = np.linspace(y0, y1, n)
    return ys, np.array([FC.closure(fam, float(y)) for y in ys])

def reopen_k(ys, c, y0, side):
    # fit log c ~ k log|y-y0| just off the crossing on one side
    m = (ys > y0+0.01) & (ys < y0+0.25) if side>0 else (ys < y0-0.01) & (ys > y0-0.25)
    x = np.log(np.abs(ys[m]-y0)); yv = np.log(np.maximum(c[m],1e-300))
    if len(x) < 4: return float('nan')
    return float(np.polyfit(x, yv, 1)[0])

def main():
    f = open(OUT, "w")
    def emit(s=""): print(s, flush=True); f.write(s+"\n"); f.flush()
    base = FC.FAMILIES["chi3"]; cut = make_skip(base)
    emit("periodic warp  cross->run->dwell->cross : complete (dwells in) vs cut (dwells out)")
    emit("="*74)
    ys, cc = curve(base, 7.0, 11.0, 1200)
    loc = np.where((cc[1:-1] < cc[:-2]) & (cc[1:-1] <= cc[2:]))[0]+1
    xs = [(ys[i], cc[i]) for i in loc if cc[i] < 8e-2]
    emit(f"[complete] crossings in [7,11]: {[(round(y,3), f'{c:.1e}') for y,c in xs]}")
    ys2, ccut = curve(cut, 7.0, 11.0, 1200)
    emit(f"\n{'y0(cross)':>10} {'c_complete':>12} {'c_cut':>12} {'ratio':>9} {'k_reopen(complete)':>18} {'k_reopen(cut-near)':>18}")
    # cut-bank crossings
    loc2 = np.where((ccut[1:-1] < ccut[:-2]) & (ccut[1:-1] <= ccut[2:]))[0]+1
    cutx = [ys2[i] for i in loc2 if ccut[i] < 3e-1]
    for y0, c0 in xs:
        c_cut_here = FC.closure(cut, y0)
        kc = reopen_k(ys, cc, y0, +1)
        # nearest cut crossing and its reopening
        if cutx:
            y0c = min(cutx, key=lambda t: abs(t-y0)); kk = reopen_k(ys2, ccut, y0c, +1)
        else:
            y0c, kk = float('nan'), float('nan')
        emit(f"{y0:>10.3f} {c0:>12.2e} {c_cut_here:>12.2e} {c_cut_here/c0:>9.1e} {kc:>18.2f} {kk:>18.2f}")
    emit("")
    emit("[read] complete closes each crossing; cut is shallow at the SAME y0 (dwell deleted =>")
    emit("       displaced).  If k_reopen matches, the reverb exponent is unchanged by the dwell.")
    f.close()

if __name__ == "__main__":
    main()
