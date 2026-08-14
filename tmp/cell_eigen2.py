import mpmath as mp
mp.mp.dps = 25
def C(s,r): return mp.power(6,-s)*mp.zeta(s, mp.mpf(r)/6)
def L3(s):  return mp.power(3,-s)*(mp.zeta(s,mp.mpf(1)/3)-mp.zeta(s,mp.mpf(2)/3))
T=[mp.mpc(0.5,14.1347251417),mp.mpc(0.8,30.0),mp.mpc(1.3,5.0),mp.mpc(0.3,-12.0)]
print("R-ODD sector, corrected:  C2-C4 = 2^-s L(s,chi3)   (no (1+2^-s) -- n=8 is 2 mod 6)")
for s in T:
    d1 = C(s,1)-C(s,5) - (1+mp.power(2,-s))*L3(s)
    d2 = C(s,2)-C(s,4) - mp.power(2,-s)*L3(s)
    print(f"  s={mp.nstr(s,8):>21}  |C1-C5 - (1+2^-s)L3| = {float(abs(d1)):.1e}"
          f"   |C2-C4 - 2^-s L3| = {float(abs(d2)):.1e}")

print("\nSO THE CELL BANK DIAGONALISES AS  {R-even: zeta}  (+)  {R-odd: L(s,chi_3)}.")
print("Then zeta(s)*L(s,chi_3) should be the DEDEKIND ZETA of Q(zeta_6)=Q(sqrt-3),")
print("i.e. the Epstein zeta of the HEXAGONAL form a^2+ab+b^2 divided by its 6 units:\n")
def epstein_hex(s, N=900):
    tot = mp.mpf(0)
    for a in range(-N,N+1):
        for b in range(-N,N+1):
            if a==0 and b==0: continue
            q = a*a+a*b+b*b
            tot += mp.power(q,-s)
    return tot
for s in (mp.mpf(3), mp.mpf(4)):
    lhs = epstein_hex(s)/6
    rhs = mp.zeta(s)*L3(s)
    print(f"  s={s}:  Epstein_hex/6 = {mp.nstr(lhs,12)}   zeta*L3 = {mp.nstr(rhs,12)}"
          f"   rel.diff = {float(abs(lhs-rhs)/abs(rhs)):.2e}")
