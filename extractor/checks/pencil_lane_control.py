"""THE BUILT-IN POSITIVE CONTROL: does the pencil place the lane factor's own zeros?

G(y) = F_Delta(1/2+iy) = Delta^{-s}(1-2^{1-s}) zeta(s),  s = 1/2+iy.
Zeros of G are:
  (a) zeta's zeros:  y = gamma - i(beta-1/2)   -> REAL y iff beta = 1/2
  (b) lane factor:   1-2^{1-s}=0 <=> s = 1-2pi i k/log2
                     -> y = -2 pi k / log 2 - i/2,  i.e. Im y = -1/2 EXACTLY,
                        spaced 2pi/log2 = 9.06472 in Re y.
(b) is a KNOWN set of genuinely OFF-LINE nodes carried by the object itself.  A pencil that
claims to read the abscissa must put them at Im y = -1/2.

PRE-REGISTERED: at an anchor placed away from any zeta zero, the pencil must return nodes
within 0.05 of the predicted lane positions in BOTH Re and Im.  Failure to place them, or
placing them at Im = +1/2, REFUTES the claim that the pencil reads the abscissa.
"""
import sys, os, math
sys.path.insert(0, 'extractor')
import numpy as np, mpmath as mp
from helix_extractor import Bank, jets
from harmonic_pencil import pencil as _pencil, nodes_to_y

mp.mp.dps = 30
LANE = 2*math.pi/math.log(2.0)
print(f"lane spacing 2pi/log2 = {LANE:.6f}, predicted Im y = -0.5\n")

bank = Bank(delta=math.pi/3, tol=1e-16)

def probe(y0, K, scale, label):
    MM = 2*K+2
    M = bank.moments(y0, mmax=MM)
    A = jets(M, MM)
    ev, S = _pencil(A, K, scale=scale, m0=1)
    ys = sorted(nodes_to_y(ev, y0), key=lambda z: abs(z-y0))
    print(f"--- {label}: y0={y0:.5f}, K={K}, scale={scale}")
    sv = S/S[0]
    print("    singular values (normalised): " + " ".join(f"{v:.2e}" for v in sv[:K+1]))
    for z in ys[:K]:
        # nearest predicted lane node
        k = round(z.real/LANE)
        lane_re = k*LANE
        d_lane = math.hypot(z.real-lane_re, z.imag+0.5)
        tag = ""
        if d_lane < 0.05: tag = f"  <-- LANE k={k} (pred {lane_re:.4f}-0.5i, err {d_lane:.2e})"
        elif abs(z.imag) < 1e-3: tag = "  <-- on-line (real node)"
        print(f"      y = {z.real:+13.6f} {z.imag:+.6f}i{tag}")
    print()
    return ys

# anchor deliberately BETWEEN zeta zeros so no single node dominates
probe(17.5, 6, 1.0, "between gamma_1=14.13 and gamma_2=21.02")
probe(17.5, 8, 1.0, "same, K=8")
probe(12.0, 6, 1.0, "below gamma_1")
