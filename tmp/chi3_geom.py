"""chi3 geometric bank on the growing-radius helix.

Geometry (ClosedForm.lean, verified at source):
  helix p r k = (r k cos 2pi k, r k sin 2pi k, p k)     growing radius = MASS
  numberSite p r n = helix p r n                        integer n at parameter n
  kClimb p y = exp y / p                                height z = e^y
  spinAngle n = n * pi/3                                carrier spin, mu6, NO log
chi3 = the quadratic character mod 3: chi(n)= +1 if n=1 mod 3, -1 if n=2 mod 3, 0 if 3|n.
Conjugate double end: bank + its conjugate.
"""
import mpmath as mp
mp.mp.dps = 25
PI = mp.pi

def chi3(n):
    r = n % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)

def spin(n):          # geometric carrier spin
    return n * PI / 3

# --- geometric bank at height Z: integers n<=Z, mass = r*n (r=1), spin = n*pi/3,
#     double end = term + conjugate  ==>  2*mass*cos(spin)
def geom_bank(N, chifn, mass):
    tot = mp.mpf(0)
    for n in range(1, N + 1):
        c = chifn(n)
        if c:
            tot += c * mass(n) * mp.cos(spin(n))
    return tot

print("=== chi3 geometric bank, double end (2*mass*cos(n pi/3)) ===")
for massname, mass in [("linear r*n", lambda n: mp.mpf(n)),
                       ("readout n^-1/2", lambda n: mp.power(n, -0.5)),
                       ("unit", lambda n: mp.mpf(1))]:
    vals = [geom_bank(N, chi3, mass) for N in (6, 12, 60, 600, 6000)]
    print(f"  {massname:16s}", "  ".join(f"N={N}:{float(v):+.6g}" for N, v in zip((6,12,60,600,6000), vals)))

# the pure mu6 x chi3 pattern over one 6-cycle
print("\n=== per-cell pattern: n mod 6 -> chi3(n), cos(n pi/3), product ===")
for n in range(1, 13):
    print(f"  n={n:2d}  n%6={n%6}  chi3={chi3(n):+d}  cos={float(mp.cos(spin(n))):+.4f}  prod={chi3(n)*float(mp.cos(spin(n))):+.4f}")
