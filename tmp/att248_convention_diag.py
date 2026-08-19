#!/usr/bin/env python3
"""
att248 — convention diagnostics for the att247b discrepancy (+6-9%).

(i)  -g''(u) vs OUR validated even kernel k(u) = 2cosh(u/2) - 2e^{-u/2}/(1-e^{-2u})
     on prime-free 0 < u < log 2  (ours validated vs zeros at 2e-10; if Suzuki's
     g matches, the g-transcription is right).
(ii) P_t(z) vs its zero expansion  sum_gamma m_gamma (e^{-i gamma t}-1)/(gamma(z-gamma))
     over +-gamma pairs from the 35,673-zero cache (checks the P-transcription).
"""
import mpmath as mp
import numpy as np
import math
import att247b_identity_fast as F

mp.mp.dps = 20

def kernel_ours(u):
    return 2 * mp.cosh(u / 2) - 2 * mp.e ** (-u / 2) / (1 - mp.e ** (-2 * u))

def diag_g():
    print("== (i) -g'' vs our validated kernel ==")
    h = mp.mpf(1e-4)
    for u in [0.3, 0.45, 0.6]:
        um = mp.mpf(u)
        d2 = (F.g_screw_exact(um + h) - 2 * F.g_screw_exact(um) + F.g_screw_exact(um - h)) / h ** 2
        ko = kernel_ours(um)
        print(f"  u = {u}: -g'' = {mp.nstr(-d2, 8)}   ours k(u) = {mp.nstr(ko, 8)}"
              f"   ratio = {mp.nstr(-d2 / ko, 6)}")

def diag_P():
    print("== (ii) P_t(z) vs zero expansion ==")
    zeros = np.load("att015_zeros_to_30000.npy")
    for (t, zv) in [(1.0, 3.7), (1.0, 7.3), (1.5, 11.2)]:
        tm, z = mp.mpf(t), mp.mpf(zv)
        # transcription value: strip the prefactor from S_all
        zl_psih_theta = F.specials(z)
        Sd = F.S_all([t], z)
        pref = 1j * (1 + zl_psih_theta[2]) / 2
        P_mine = Sd[t] / pref
        # zero-expansion: sum over +-gamma
        acc = mp.mpc(0)
        for g in zeros[:20000]:
            gm = mp.mpf(float(g))
            for gg in (gm, -gm):
                acc += (mp.e ** (-1j * gg * tm) - 1) / (gg * (z - gg))
        # tail estimate order: pairs beyond 30000: ~ 2*(cos-1 avg)/g^2 * density -> print raw
        print(f"  t={t}, z={zv}:  P(transcribed) = {mp.nstr(P_mine, 8)}")
        print(f"              zero-sum(20k pairs) = {mp.nstr(acc, 8)}"
              f"   diff = {mp.nstr(P_mine - acc, 4)}")

if __name__ == "__main__":
    diag_g()
    diag_P()
