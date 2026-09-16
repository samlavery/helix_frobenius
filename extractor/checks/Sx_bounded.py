"""O2 asks for |S_x - S| < 1.  But S_x is a FINITE trigonometric polynomial:

    S_x(t) = -(1/pi) sum_{n<=x^3} Lambda(n) w_x(n) / (sqrt(n) log n) * sin(t log n)

so  |S_x(t)| <= B(x) := (1/pi) sum |weights|,  an explicit constant, for ALL t.
S(t), by contrast, is UNBOUNDED (Selberg).  Hence for FIXED x,
    sup_t |S_x(t) - S(t)| >= sup_t |S(t)| - B(x) = infinity.
Compute B(x) for the cutoffs the paper uses.
"""
import sys, os, math
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import numpy as np
from helix_extractor import Clocks

print(f"{'x':>6} {'prime powers':>14} {'B(x) = sum|w|/pi':>20}")
for x in (10, 30, 100, 300, 1000):
    c = Clocks(x)
    B = float(np.abs(c.w).sum())/math.pi
    print(f"{x:>6} {c.terms:>14,} {B:>20.6f}")
print()
print("So |S_x| can never exceed B(x).  If |S(t)| > B(x) + 1 anywhere, O2 is FALSE at that t.")
