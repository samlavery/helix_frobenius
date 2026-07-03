"""The pi/3-scaled version of the lane reading, using the CANONICAL model
(phasor_explorer/model.py — house rule: use it, don't re-derive).

Two faces of the pi/3 scaling at a cancellation:
 (1) WINDING face (geometric, no log, no L anywhere): phasors at carrier points
     x_n=(pi/3)n, equal magnitude -> the mu6 six-cell closure is EXACT (|B|=0),
     and the six cell-lanes carry equal weight. Height-blind by design.
 (2) FOCUS face (growth + log spin): the growth window breaks the blind closure
     and selects the eigenheight — the zero's address (|B| dips at gamma, not off).
"""
import sys
sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius/phasor_explorer")
import numpy as np
import model as M

print("(1) WINDING face — pi/3 carrier, equal magnitude, N=1200 (complete cells)")
for char in ("trivial", "chi5"):
    n = np.arange(1, 1201, dtype=float)
    chi = M.CHARS[char]["chi"](n.astype(int))
    ph = M.phase(n, "winding", 1200, 0.0)
    z = chi * np.exp(1j * ph)                      # equal magnitude
    B = z.sum()
    # six mu6 cell-lanes: bucket by phase root exp(i*pi/3*k), k=0..5
    root = (np.rint(ph / M.PI3).astype(int)) % 6
    lanes = [abs(z[root == k].sum()) for k in range(6)]
    print(f"    {char:8s} |B| = {abs(B):.3e}   six cell-lane magnitudes: "
          + " ".join(f"{L:7.2f}" for L in lanes))

print()
print("(2) FOCUS face — growth window + log spin at the eigenheight (canonical locator channel)")
for char, g in (("trivial", 14.1347251417), ("chi5", 6.6484533447)):
    N = M.eigenheight(g)
    A, B = M.fast_focal_channels(char, "log_entry", N, g, mag_mode="grow")
    Aoff, Boff = M.fast_focal_channels(char, "log_entry", N, g + 0.35, mag_mode="grow")
    print(f"    {char:8s} gamma={g:<14.10f} N=e^g={N:>9d}   |B|(at zero) = {abs(B):.3e}"
          f"   |B|(off, +0.35) = {abs(Boff):.3e}   contrast x{abs(Boff)/abs(B):,.0f}")
    print(f"             unsigned mass A = {abs(A):.2f}  (the state never approaches 0)")
