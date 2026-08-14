#!/usr/bin/env python3
"""
Attempt 027 — the band-limited CGdL constant Z*, by cutting planes.

Minimize   Z = ghat(0) + 2*int_0^1 ghat(x) x dx
over even ghat supported in [0, S], subject to
    g(u) = 2*int_0^S ghat(x) cos(xu) dx  >= 0   for all u >= 0,
    g(0) = 2*int_0^S ghat(x) dx           = 1,
    ghat(x) <= 0 on [dip_from, S].

Anchors: S=1 -> Montgomery-Taylor 1.3274992 (positive control);
         S large -> CGdL 1.3208; Fejér feasible point 4/3.

Algorithm: cutting-plane. Start with a coarse u-constraint set; solve; scan g on a
fine grid; add the most-violated u's; repeat until min g >= -tol on the scan grid.
"""
import numpy as np
from scipy.optimize import linprog
import sys, time

def solve(S=2.0, M=None, dip_from=1.0, Umax=300.0, tol=1e-9, maxrounds=60, verbose=True):
    if M is None:
        M = int(round(300 * S))
    x = np.linspace(0.0, S, M + 1)
    dx = x[1] - x[0]
    w = np.full(M + 1, dx); w[0] *= 0.5; w[-1] *= 0.5

    # objective
    c = np.zeros(M + 1)
    c[0] += 1.0
    c += 2.0 * w * np.where(x <= 1.0, x, 0.0)

    Aeq = (2.0 * w)[None, :]; beq = np.array([1.0])

    B = 6.0   # inactive box; audit at convergence that |ghat| < B strictly
    bounds = [(-B, 0.0) if (xj >= dip_from - 1e-12 and S > dip_from) else (-B, B)
              for xj in x]

    # scan grid for violations (incommensurate step; dense near 0)
    Uscan = np.concatenate([np.arange(0.0, 30.0, 0.004),
                            np.arange(30.0, Umax, 0.0173)])
    Cscan = np.cos(np.outer(Uscan, x)) * (2.0 * w)[None, :]   # g(u) = Cscan @ ghat

    # initial constraint u's
    ucons = list(np.arange(0.0, 25.0, 0.5))
    t0 = time.time()
    for rnd in range(maxrounds):
        Ua = np.array(ucons)
        Aub = -(np.cos(np.outer(Ua, x)) * (2.0 * w)[None, :])
        bub = np.zeros(len(Ua))
        res = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
                      bounds=bounds, method="highs")
        if not res.success:
            print(f"  LP failed round {rnd}: {res.message}", flush=True)
            return None, None, None
        gh = res.x
        gs = Cscan @ gh
        gmin = gs.min()
        if gmin >= -tol:
            Z = res.fun
            boxhit = np.max(np.abs(gh))
            if verbose:
                print(f"  S={S:4.1f}: Z* = {Z:.7f}  (2-Z = {2-Z:.7f})  rounds={rnd+1} "
                      f"cons={len(ucons)}  min g={gmin:+.1e}  max|ghat|={boxhit:.3f}"
                      f"  [{time.time()-t0:.1f}s]", flush=True)
            return Z, gh, x
        # add worst violations: local minima of gs below -tol
        viol = np.where(gs < -tol)[0]
        # pick up to 40 well-separated worst offenders
        order = viol[np.argsort(gs[viol])]
        added = 0
        taken = []
        for idx in order:
            u = Uscan[idx]
            if all(abs(u - t) > 0.02 for t in taken):
                ucons.append(u); taken.append(u); added += 1
            if added >= 40:
                break
        if verbose and rnd % 10 == 9:
            print(f"    round {rnd+1}: Z={res.fun:.7f} min g={gmin:+.2e} cons={len(ucons)}", flush=True)
    print(f"  S={S}: NOT CONVERGED after {maxrounds} rounds (min g = {gmin:+.2e})", flush=True)
    return None, None, None

if __name__ == "__main__":
    mt = 0.5 + (1.0/np.sqrt(2.0)) / np.tan(1.0/np.sqrt(2.0))
    print(f"controls: Fejér Z=4/3=1.3333333; Montgomery–Taylor 1/c1*={mt:.7f}", flush=True)

    for S in [1.0, 1.5, 2.0, 3.0, 5.0, 8.0]:
        Z, gh, x = solve(S=S)
        if Z is not None and abs(S - 2.0) < 1e-9:
            np.save("/Users/samuellavery/work/helix_frobenius/tmp/att027_ghat_S2.npy",
                    np.vstack([x, gh]))
