"""
High-gamma window for the harmonic-chart bench: zeros near gamma = 10^6.

Purpose: the log-scaling confound check.  The prime-clock DC decays like
1/log(T/2pi), so moving from gamma ~ 5.5e3 to gamma ~ 1e6 should shrink the
positive control by a factor log(5540/2pi)/log(1e6/2pi) = 6.78/11.98 = 0.566
while leaving the harmonic scales at zero.  An effect that behaves otherwise is
a small-height artifact.

Zeros are located as sign changes of the Riemann-Siegel Z function.
COMPLETENESS IS VALIDATED against N(T2) - N(T1), not assumed.
"""

import numpy as np
from mpmath import mp, siegelz

mp.dps = 15
TWOPI = 2.0 * np.pi
OUT = "/Users/samuellavery/work/helix_frobenius/tmp/zeta_zeros_1e6.txt"


def rvm(t):
    return (t / TWOPI) * (np.log(t / TWOPI) - 1.0) + 0.875


def find_zeros(t0, t1, step=0.1):
    zs = []
    t = t0
    z = float(siegelz(t))
    n = 0
    while t < t1:
        tn = t + step
        zn = float(siegelz(tn))
        n += 1
        if z == 0.0:
            zs.append(t)
        elif z * zn < 0.0:
            a, b, fa = t, tn, z
            for _ in range(60):
                m = 0.5 * (a + b)
                fm = float(siegelz(m))
                if fa * fm <= 0.0:
                    b = m
                else:
                    a, fa = m, fm
                if b - a < 1e-11:
                    break
            zs.append(0.5 * (a + b))
        t, z = tn, zn
    return np.array(zs), n


def main():
    t0, t1 = 1.0e6, 1.0e6 + 1200.0
    print(f"scanning Z(t) on [{t0:.0f}, {t1:.0f}] ...", flush=True)
    zs, nev = find_zeros(t0, t1)
    expected = rvm(t1) - rvm(t0)
    print(f"found   {zs.size} zeros in {nev} Z-evaluations")
    print(f"expected N(T2)-N(T1) = {expected:.1f}")
    print(f"COMPLETENESS: found/expected = {zs.size/expected:.5f}")
    np.savetxt(OUT, zs, fmt="%.10f")
    print(f"written to {OUT}")


if __name__ == "__main__":
    main()
