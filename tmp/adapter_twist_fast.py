#!/usr/bin/env python3
"""Fast trend variant of the converse-requirement curve (float64, coarse floor).

r=5 (odd): no zero channel, so one kernel grid serves every twist channel.
Kernel tabulated once with mpmath on a log grid, linear-in-log interpolation
(~1e-6 relative), numpy SVDs.  Floors reported at 1e-3/1e-4/1e-5 -- the TREND
instrument; the running mpmath job is the deep-floor confirmation.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import mpmath as mp
from adapter_sym_probe import gammaR_params, kernel_factory

mp.mp.dps = 20

CHARS = {
    3: [0, 1, -1],
    4: [0, 1, 0, -1],
    5: [0, 1, -1, -1, 1],
    7: [0, 1, 1, -1, 1, -1, -1],
    8: [0, 1, 0, -1, 0, -1, 0, 1],
}

def tab_kernel(r, ymin, ymax, pts=3000):
    K = kernel_factory(gammaR_params(r))
    ys = np.exp(np.linspace(np.log(ymin), np.log(ymax), pts))
    vals = []
    for y in ys:
        v = K(mp.mpf(float(y)))
        vals.append(float(v) if v != 0 else 0.0)
    vals = np.array(vals)
    # find last positive index for log-interp domain
    pos = vals > 0
    logv = np.full(len(ys), -1e30)
    logv[pos] = np.log(vals[pos])
    return np.log(ys), logv

def make_K(logys, logv):
    def K(y):
        ly = np.log(y)
        out = np.interp(ly, logys, logv, left=-1e30, right=-1e30)
        return np.where(out < -600, 0.0, np.exp(out))
    return K

def channel_matrix(K, r, N, M, q):
    C = float(q) ** ((r + 1) / 2) if q else 1.0
    xs = np.linspace(1.0, 1.8, M)
    n = np.arange(1, N + 1)
    if q:
        tab = CHARS[q]
        ch = np.array([tab[i % q] for i in n], dtype=float)
    else:
        ch = np.ones(N)
    A = np.zeros((M, N))
    for i, x in enumerate(xs):
        A[i] = ch * (K(n / (C * x)) - x * K(n * x / C))
    return A

def curve(r, N, qs):
    M = 2 * N
    # grid range: smallest arg 1/(C_max*1.8), largest N*1.8
    Cmax = max(qs) ** ((r + 1) / 2)
    logys, logv = tab_kernel(r, 1.0 / (Cmax * 2.0), N * 2.0)
    K = make_K(logys, logv)
    mats = [channel_matrix(K, r, N, M, None)]
    labels = ['FE']
    def report():
        B = np.vstack(mats)
        s = np.linalg.svd(B, compute_uv=False)
        smax = s.max()
        nul = {t: int((s / smax < t).sum()) for t in (1e-3, 1e-4, 1e-5)}
        print(f"#  {labels}: nullity {nul[1e-3]}/{nul[1e-4]}/{nul[1e-5]} of {N}  (rel<1e-3/-4/-5)")
    print(f"# FAST trend curve Sym^{r}, N={N}, M={M}/channel (coarse floor)")
    report()
    for q in qs:
        mats.append(channel_matrix(K, r, N, M, q))
        labels.append(f"q{q}")
        report()

if __name__ == '__main__':
    r = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 120
    qs = [int(t) for t in (sys.argv[3].split(',') if len(sys.argv) > 3 else ['3', '4', '5', '7', '8'])]
    curve(r, N, qs)
