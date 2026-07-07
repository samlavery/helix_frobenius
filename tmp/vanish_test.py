#!/usr/bin/env python3
"""
vanish_test.py -- does the REAL Altug GL(2) transform actually VANISH, or only dip?

Standard (the only one that counts): a cancellation is a genuine residue-free VANISHING
iff, when we refine the nu-grid around the deepest dip, |V(nu)| keeps falling toward the
numerical floor -- it SHARPENS to a zero.  A shallow local minimum plateaus at a fixed
depth no matter how fine the grid.  Dip SPACING is irrelevant to this; DEPTH under
refinement is the test.

Object: the actual mb_beat complex profile V(nu) = sum_y c_r(y) e(-y nu/4lf^2) of the
Altug orbital content, ranked by Sym^r/U_r, on the anchor-gated scan meshes.

Method: for each cell+rank, coarse-scan |V|, take the deepest dip nu*, then do 3 rounds
of local golden refinement around nu*, each round on a 100x-finer window, and record the
minimum |V|/max|V| after each round.  A true zero drops ~1e1-1e2 per round toward the
mesh's own floor; a shallow minimum stalls.

Run: python3 vanish_test.py  (rebuilds meshes ~50s)
"""
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mb_beat as B
import mb_identify as ID
import mb_elastic as EL


def deepest_min(mesh, cvec, nu_lo, nu_hi, npts=400):
    nus = np.linspace(nu_lo, nu_hi, npts)
    V = np.abs(B.complex_profile(mesh, cvec, nus))
    i = int(np.argmin(V))
    return nus[i], float(V[i]), float(np.max(V))


def refine_vanish(mesh, cvec, rounds=4):
    """coarse deepest dip, then local refinement; return depth (min|V|/max|V|) per round."""
    nus = ID.NU_GRID
    V = np.abs(B.complex_profile(mesh, cvec, nus))
    vmax = float(np.max(V))
    i = int(np.argmin(V[1:-1])) + 1
    nu_star = nus[i]
    half = (nus[1] - nus[0])
    depths = [float(V[i]) / vmax]
    for _ in range(rounds):
        nu_star, vmin, _ = deepest_min(mesh, cvec, nu_star - half, nu_star + half, 400)
        depths.append(vmin / vmax)
        half /= 50.0            # 50x finer window each round
    return depths, nu_star


def main():
    t0 = time.time()
    scan_meshes = {}
    for (l, f) in ((1, 1), (2, 1), (1, 2)):
        for X in (8.0, 16.0):
            scan_meshes[(l, f, X)] = EL.build_mesh_ext(l, f, X, ny=ID.scan_ny(l, f, X))
    cores = {k: ID.class_cores(m) for k, m in scan_meshes.items()}
    print(f"[setup] meshes rebuilt {time.time()-t0:.0f}s")

    # a few event-bearing cells (xi=6, several (l,f,X)); sweep ranks
    cells = [(6, 1, 1, 8.0), (6, 2, 1, 8.0), (6, 1, 2, 8.0), (6, 1, 1, 16.0)]
    print("\n[vanishing under nu-refinement] depth = min|V|/max|V| after each 50x-finer round")
    print("  a TRUE zero keeps dropping toward the mesh floor; a shallow dip STALLS.")
    print(f"  {'cell':>16} {'r':>3}  {'coarse':>9} {'r1':>9} {'r2':>9} {'r3':>9} {'r4':>9}  verdict")
    for cell in cells:
        key = (cell[1], cell[2], cell[3])
        mesh = scan_meshes[key]
        for r in (0, 2, 5, 8, 13):
            cvec = B.ranked_y_content(mesh, cell[0], cores[key]["T"], rank=r)
            depths, _ = refine_vanish(mesh, cvec, rounds=4)
            drop = depths[0] / max(depths[-1], 1e-300)
            verdict = ("VANISHES (sharpens)" if depths[-1] < 1e-6
                       else "deepens" if drop > 5 else "STALLS (shallow)")
            print(f"  {str(cell):>16} {r:>3}  " +
                  " ".join(f"{d:9.2e}" for d in depths) + f"  {verdict}")
    print(f"\n[done] {time.time()-t0:.0f}s")


if __name__ == "__main__":
    main()
