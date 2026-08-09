#!/usr/bin/env python3
"""Light-channel probe: burial rate vs mock GL(2) twist weight.

Tensor stack of Sym^5 (weight-12 seed) with a mock GL(2) twist of weight w:
GammaC parameters {(55+v)/2, (55-v)/2, (33+v)/2, (33-v)/2, (11+v)/2, |11-v|/2},
v = w-1; lightest parameter lambda_1(w) = |12-w|/2.  Mechanism prediction
(capacity note, Thm 2 + light-channel interpretation): channel amplitude
suppression log10(sigma1(C)/sigma1(1)) = -lambda_1(w) * log10(C), and shallow
yields resurrect as w -> 12.  C = 27 (= conductor scale of q=3 at rank 6) for
comparability with the measured GL(1) burial.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import mpmath as mp
from adapter_sym_probe import kernel_factory, gammaR_params

mp.mp.dps = 20

def tensor_params(w):
    v = mp.mpf(w) - 1
    nus = [(55 + v) / 2, (55 - v) / 2, (33 + v) / 2, (33 - v) / 2,
           (11 + v) / 2, abs(11 - v) / 2]
    lams = []
    for nu in nus:
        lams += [nu, nu + 1]
    return lams

def tab_kernel(lams, ymin, ymax, pts=1200):
    K = kernel_factory(lams)
    ys = np.exp(np.linspace(np.log(ymin), np.log(ymax), pts))
    vals = []
    for y in ys:
        v = K(mp.mpf(float(y)))
        vals.append(float(v) if v != 0 else 0.0)
    vals = np.array(vals)
    logv = np.full(len(ys), -1e30)
    pos = vals > 0
    logv[pos] = np.log(vals[pos])
    def KK(y):
        out = np.interp(np.log(y), np.log(ys), logv, left=-1e30, right=-1e30)
        return np.where(out < -600, 0.0, np.exp(out))
    return KK

def channel(K, N, M, C):
    xs = np.linspace(1.0, 1.8, M)
    n = np.arange(1, N + 1)
    A = np.zeros((M, N))
    for i, x in enumerate(xs):
        A[i] = K(n / (C * x)) - x * K(n * x / C)
    return A

def run(N=120, C=27.0, weights=(11.7, 10.0, 8.0, 6.0, 4.0)):
    M = 2 * N
    # base: the untwisted Sym^5 FE rows
    Kbase = tab_kernel(gammaR_params(5), 1.0 / (2.0 * 1.8), N * 2.0)
    B = channel(Kbase, N, M, 1.0)
    sB = np.linalg.svd(B, compute_uv=False)
    print(f"# light-channel probe: Sym^5 x mock-GL2(w), N={N}, C={C}")
    print(f"# base FE sigma1 = {sB.max():.3e}")
    lc = float(mp.log(C, 10))
    for w in weights:
        lam1 = abs(12.0 - w) / 2.0
        lams = tensor_params(w)
        K = tab_kernel(lams, 1.0 / (C * 2.0), N * 2.0)
        A1 = channel(K, N, M, 1.0)
        AC = channel(K, N, M, C)
        s1 = np.linalg.svd(A1, compute_uv=False).max()
        sC = np.linalg.svd(AC, compute_uv=False).max()
        ratio = np.log10(sC / s1)
        pred = -lam1 * lc
        # shallow yields: channel stacked on base
        s0 = np.linalg.svd(B, compute_uv=False)
        sJ = np.linalg.svd(np.vstack([B, AC / sC * s0.max()]), compute_uv=False)
        def nul(s, t):
            return int((s / s.max() < t).sum())
        y3 = nul(s0, 1e-3) - nul(sJ, 1e-3)
        y4 = nul(s0, 1e-4) - nul(sJ, 1e-4)
        y5 = nul(s0, 1e-5) - nul(sJ, 1e-5)
        print(f"# w={w:5.1f}  lam1={lam1:4.2f}  log10(s1C/s11)={ratio:7.2f}  "
              f"pred={pred:7.2f}  yields(1e-3/-4/-5)={y3}/{y4}/{y5}")

if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    C = float(sys.argv[2]) if len(sys.argv) > 2 else 27.0
    run(N=N, C=C)
