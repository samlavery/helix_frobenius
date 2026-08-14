"""RUN M3 -- the AVERAGED (unconditional) singular-series model.

zeta23_hl.py defines four weights; the reported run covered only three.  M3 is the one that
matters: weight 1 - 1/(2h), i.e. density PLUS the Montgomery-Soundararajan secondary term,
which is what you get from knowing ONLY the AVERAGED singular series
    sum_{h<=H} S(h) = H - (1/2) log H + O(...)     [MS04 Theorem 2, UNCONDITIONAL]
rather than S(h) pointwise (which is Hardy-Littlewood, conjectural).

    EXACT : cn = Lambda(n)/sqrt(n), weight 1        -- VALIDATION GATE, must match measured O_1
    M1    : cn = 1/sqrt(n),        weight 1         -- density only
    M2    : cn = 1/sqrt(n),        weight S(h)      -- full HL (conjectural)
    M3    : cn = 1/sqrt(n),        weight 1-1/(2h)  -- AVERAGED, unconditional

If M3 tracks M2/measured, the main term needs no conjecture.  If it does not, the gap to full
Hardy-Littlewood is real and quantified.  Reported as ratios to the measured O_1: model and
measurement share a normalization, the raw tables do not.
"""
import sys
import time

import numpy as np

from zeta23_prime import prime_powers
from zeta23_o1 import split
from zeta23_hl import singular_series, R_all_integers, O1_model


def run(T, ETA, lams, Hmax):
    l = np.log(T / (2 * np.pi))
    l1 = l + 2 * np.log(2) - 1
    print(f"T={T}  l={l:.5f}  l1={l1:.5f}  eta={ETA}  Hmax={Hmax}")
    print(f"{'lam':>5} {'L':>7} {'X':>7} {'d':>5} {'measured':>13} {'EXACT':>13} "
          f"{'gate':>7} {'M1/meas':>8} {'M2/meas':>8} {'M3/meas':>8}  [s]")
    for lam in lams:
        t0 = time.time()
        L = lam * l
        w = ETA * L / 2
        if ETA * L > 2 * np.log(2):
            print(f"{lam:5.2f}  SKIP: eta*L={ETA*L:.3f} > 2log2")
            continue
        X = int(np.exp(L))
        h = 2 * np.pi / L
        d = int(np.floor(T / h))

        # --- the measurement, from the reference splitter ---
        lamv, u = prime_powers(float(X))
        _, _, _, O1_meas, _, _ = split(T, L, w, lamv, u)

        # --- the model apparatus, shared by all four weights ---
        Rt = R_all_integers(X, L, w, d, h)
        n = np.arange(1, X + 1)
        inv_sqrt = 1.0 / np.sqrt(n)

        cn_exact = np.zeros(X)
        keep = u < np.log(X + 1)
        idx = np.rint(np.exp(u[keep])).astype(int)
        ok = (idx >= 1) & (idx <= X)
        cn_exact[idx[ok] - 1] = lamv[keep][ok] / np.sqrt(idx[ok])

        S = singular_series(Hmax)
        one = lambda hh: 1.0
        sing = lambda hh: float(S[hh])
        aver = lambda hh: 1.0 - 1.0 / (2.0 * hh)

        gate, _ = O1_model(T, L, w, one, cn_exact, X, d, Rt, Hmax)
        m1, _ = O1_model(T, L, w, one, inv_sqrt, X, d, Rt, Hmax)
        m2, _ = O1_model(T, L, w, sing, inv_sqrt, X, d, Rt, Hmax)
        m3, _ = O1_model(T, L, w, aver, inv_sqrt, X, d, Rt, Hmax)

        r = lambda v: v / O1_meas if O1_meas != 0 else float('nan')
        print(f"{lam:5.2f} {L:7.3f} {X:7d} {d:5d} {O1_meas:13.1f} {gate:13.1f} "
              f"{r(gate):7.3f} {r(m1):8.3f} {r(m2):8.3f} {r(m3):8.3f}  "
              f"[{time.time()-t0:.0f}]")
        sys.stdout.flush()


if __name__ == "__main__":
    T = float(sys.argv[1]) if len(sys.argv) > 1 else 600.0
    ETA = float(sys.argv[2]) if len(sys.argv) > 2 else 0.01
    HMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 60
    run(T, ETA, [1.75, 2.0, 2.25], HMAX)
