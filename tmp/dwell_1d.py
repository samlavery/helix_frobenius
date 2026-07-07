#!/usr/bin/env python3
"""
dwell_1d.py -- the periodic dwell warp, scaled DOWN to 1D so we can measure MANY crossings.

Pitch-1 helix projected to 1D: phasor n sits at height n (integer = z+1), readout
F(y) = sum_n a(n) e^{-i y n} (a trig polynomial -> dense, cheap crossings).  Two lanes of a
real character chi3: P = n==1 mod 3, M = n==2 mod 3; closure c(y) = |P-M|/max(|P|,|M|) is the
focal lane-balance (=0 at a crossing, where P=M).  Growth window w(n/N) (smooth entry) and the
carrier n^{-1/2} amplitude, as in focal_closure.

Test the pattern  cross -> run -> dwell -> cross  across many crossings:
  complete : every phasor present (dwells in)          -> each crossing closes
  cut      : perfect-square n deleted (dwells removed)  -> each crossing displaces/shallows
and the reopening exponent k (c ~ |y-y0|^k on the departure side) at each crossing, to check
the reverb law is the same at EVERY period, not just one.

Run: python3 tmp/dwell_1d.py   (writes tmp/dwell_1d_results.txt; seconds, not minutes)
"""
import math, os
import numpy as np

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "dwell_1d_results.txt")
N = 4000

def amps(cut_squares=False):
    n = np.arange(1, N + 1, dtype=float)
    chi = np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))
    u = n / N
    w = np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None))     # smooth-entry growth window
    a = chi * w * n ** -0.5
    if cut_squares:
        m = 1
        while m * m <= N:
            a[m * m - 1] = 0.0                                     # delete the dwell (Altug skip)
            m += 1
    return n, a

def closure_curve(ys, n, a):
    P = (a > 0)                       # chi=+1 lane
    M = (a < 0)                       # chi=-1 lane
    E = np.exp(-1j * np.outer(ys, n))
    Fp = E[:, P] @ a[P]
    Fm = E[:, M] @ a[M]               # a[M] is negative; -Fm is the M-lane resultant
    num = np.abs(Fp + Fm)            # P - |M| = Fp + Fm (since a[M]<0)
    den = np.maximum(np.abs(Fp), np.abs(Fm))
    return num / np.maximum(den, 1e-300)

def find_min(ys, c, cut=0.15):
    loc = np.where((c[1:-1] < c[:-2]) & (c[1:-1] <= c[2:]))[0] + 1
    return [(ys[i], c[i], i) for i in loc if c[i] < cut]

def reopen_k(ys, c, i0):
    j = np.arange(i0 + 2, min(i0 + 40, len(ys) - 1))
    x = np.log(ys[j] - ys[i0]); yv = np.log(np.maximum(c[j], 1e-300))
    return float(np.polyfit(x, yv, 1)[0]) if len(j) >= 5 else float('nan')

def main():
    f = open(OUT, "w")
    def emit(s=""): print(s, flush=True); f.write(s + "\n"); f.flush()
    emit(f"1D scaled pitch-1 lane-balance (N={N}); many crossings; complete(dwells in) vs cut(out)")
    emit("=" * 82)
    ys = np.linspace(0.02, 3.0, 60000)
    n, a_full = amps(False)
    n, a_cut = amps(True)
    c_full = closure_curve(ys, n, a_full)
    c_cut = closure_curve(ys, n, a_cut)
    xs = find_min(ys, c_full, cut=0.06)
    emit(f"[complete] {len(xs)} crossings in y in [0.02,3.0]")
    emit(f"\n{'#':>3} {'y0':>8} {'c_complete':>12} {'c_cut@y0':>12} {'ratio':>9} {'k_reopen':>9}")
    ks = []
    for j, (y0, c0, i0) in enumerate(xs, 1):
        cc = c_cut[i0]
        k = reopen_k(ys, c_full, i0)
        ks.append(k)
        emit(f"{j:>3} {y0:>8.4f} {c0:>12.2e} {cc:>12.2e} {cc/c0:>9.1e} {k:>9.2f}")
    ks = np.array([k for k in ks if np.isfinite(k)])
    emit(f"\n[reverb] reopening exponent k over ALL crossings: mean {ks.mean():.3f}, std {ks.std():.3f}")
    emit(f"[read] complete closes EVERY crossing; cut is shallow at each (dwell deleted => displaced);")
    emit(f"       if k is flat across crossings, the reverb law is periodic and unchanged by the dwell.")
    f.close()

if __name__ == "__main__":
    main()
