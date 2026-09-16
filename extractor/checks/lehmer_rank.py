"""Does the pencil RESOLVE Lehmer's pair as two distinct nodes?

gamma_6709 = 7005.062866174921, gamma_6710 = 7005.100564672656; separation 0.0377,
which is 0.042 of the local mean spacing 0.8955.  This is the hardest resolvable case
in the low range.  PRE-REGISTERED: the pencil must return two REAL nodes matching both
ordinates to better than 1e-6, with sigma_2/sigma_1 well above the noise floor.  If it
returns one node, the pair is below the instrument's resolution and that is the result.
"""
import sys, math
sys.path.insert(0, 'extractor')
import numpy as np, mpmath as mp
from helix_extractor import Bank, jets
from harmonic_pencil import pencil as _pencil, nodes_to_y
mp.mp.dps = 30

G1, G2 = 7005.062866174921, 7005.100564672656
y0 = 0.5*(G1+G2) + 0.0134      # anchor slightly off the midpoint (midpoint is a symmetry trap)
bank = Bank(delta=math.pi/3, tol=1e-16)
print(f"gamma_6709 = {G1}\ngamma_6710 = {G2}\nseparation = {G2-G1:.6f}   anchor y0 = {y0:.6f}\n")

for K in (3, 4, 6):
    MM = 2*K+2
    M = bank.moments(y0, mmax=MM)
    A = jets(M, MM)
    ev, S = _pencil(A, K, scale=1.0, m0=1)
    ys = sorted(nodes_to_y(ev, y0), key=lambda z: abs(z-y0))
    print(f"--- K={K}   sv/s1: " + " ".join(f"{v:.2e}" for v in S/S[0]))
    for z in ys[:3]:
        e1, e2 = abs(z.real-G1), abs(z.real-G2)
        tag = ""
        if min(e1,e2) < 1e-4:
            tag = f"  <-- gamma_{6709 if e1<e2 else 6710}, err {min(e1,e2):.2e}, Im={z.imag:+.2e}"
        print(f"      y = {z.real:.9f} {z.imag:+.3e}i{tag}")
    print()
