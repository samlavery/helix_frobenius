"""The cell reflection R: r -> -r has eigenspaces.  WHAT LIVES IN THEM?
C_r(s) = sum_{n = r mod 6} n^-s = 6^-s zeta(s, r/6).
R-EVEN  (pair sums)        : candidate  zeta(s) * Euler factors
R-ODD   (pair differences) : candidate  L(s, chi_3) * Euler factors
Test as EXACT identities, not fits."""
import mpmath as mp
mp.mp.dps = 25

def C(s, r): return mp.power(6,-s)*mp.zeta(s, mp.mpf(r)/6)
def L3(s):   return mp.power(3,-s)*(mp.zeta(s,mp.mpf(1)/3) - mp.zeta(s,mp.mpf(2)/3))

tests = [mp.mpc(0.5,14.1347251417), mp.mpc(0.5,21.022), mp.mpc(0.8,30.0),
         mp.mpc(1.3,5.0), mp.mpc(0.3,-12.0)]
print("R-EVEN sector (pair sums) vs zeta * Euler factors:")
for s in tests:
    e1 = C(s,1)+C(s,5) - (1-mp.power(2,-s))*(1-mp.power(3,-s))*mp.zeta(s)
    e2 = C(s,2)+C(s,4) - mp.power(2,-s)*(1-mp.power(3,-s))*mp.zeta(s)
    e3 = C(s,3)         - mp.power(3,-s)*(1-mp.power(2,-s))*mp.zeta(s)
    e4 = C(s,6)         - mp.power(6,-s)*mp.zeta(s)
    print(f"  s={mp.nstr(s,8):>22}  |C1+C5-.|={float(abs(e1)):.1e}  |C2+C4-.|={float(abs(e2)):.1e}"
          f"  |C3-.|={float(abs(e3)):.1e}  |C6-.|={float(abs(e4)):.1e}")
print("\nR-ODD sector (pair differences) vs L(s,chi_3) * Euler factors:")
for s in tests:
    d1 = C(s,1)-C(s,5) - (1+mp.power(2,-s))*L3(s)
    d2 = C(s,2)-C(s,4) - mp.power(2,-s)*(1+mp.power(2,-s))*L3(s)
    print(f"  s={mp.nstr(s,8):>22}  |C1-C5-.|={float(abs(d1)):.1e}   |C2-C4-.|={float(abs(d2)):.1e}")
print("\nTOTAL CONTENT of the 6-cell bank  =  zeta * L(chi_3) ?")
for s in tests:
    zc = mp.zeta(s)*L3(s)
    ded = mp.zeta(s)*L3(s)     # Dedekind zeta of Q(sqrt(-3)) = zeta * L(chi_-3)
    print(f"  s={mp.nstr(s,8):>22}  zeta*L3 = {mp.nstr(zc,10)}")
