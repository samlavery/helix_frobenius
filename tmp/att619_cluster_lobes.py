# Degree-2 seat term of a hypothetical cluster near sigma = 1, in bump units.
# Anchor at a cluster zero; A = a a' (own bump width); neighbours at v_j = j*h, all with a_j a'_j << v_j.
# F(gamma0) * A^2 / 2 = 1 + 2 S(r),  S(r) = sum_{j>=1} (1 - (j r)^2) / (1 + (j r)^2)^2,  r = h / A.
# Contradiction with the (3,4,1) budget needs 1 + 2S(r) > 3/4, i.e. S(r) > -1/8.
import math
def S(r, J=200000):
    return sum((1 - (j*r)**2)/(1 + (j*r)**2)**2 for j in range(1, J))
print(" r = h/A     S(r)     1+2S   verdict")
for r in [0.05, 0.1, 0.2, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.3, 3.6, 3.7, 4.0, 5.0, 8.0]:
    s = S(r)
    print("%6.2f   %8.4f  %7.4f   %s" % (r, s, 1+2*s, "contradiction" if s > -0.125 else "evades"))
print("continuum limit r -> 0: Euler-Maclaurin gives S -> -1/2 (bumps and lobes cancel; total mass conserved)")
