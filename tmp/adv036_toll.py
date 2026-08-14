# AV3: the strip TOLL, with positive control.
# NULL (written before running): the sech-weighted functional at W=0 does NOT
# reduce to the classical Montgomery-Taylor constant 1.3274993.  If it does,
# the null is rejected and the W-family is confirmed to interpolate
# [W=0 : Montgomery-Taylor 1.3274993]  ->  [W=1 : BGSTB Thm 2 1.3825162].
import mpmath as mp
mp.mp.dps = 25
r2 = mp.sqrt(2); norm = 1 - mp.cos(r2)
jF = lambda a: mp.mpf(1)-a
def jM(a):
    f = jF(a)
    return (mp.sin(r2*f)/r2 + f*mp.cos(r2*a))/2/norm
def Zw(j, W, jzero):
    sw = (lambda u: mp.mpf(1)) if W==0 else (lambda u: 1/mp.cosh(W*u))
    num = jzero + 2*mp.quad(lambda a: a*j(a)*sw(a), [0,1])
    den = 2*mp.quad(lambda a: j(a)*sw(a), [0,1])
    return num/den

print("POSITIVE CONTROL W=0 (must be Montgomery-Taylor 1.3274992963):")
print("   jM :", mp.nstr(Zw(jM,0,jM(0)),12))
print("   jF :", mp.nstr(Zw(jF,0,mp.mpf(1)),12), " (classical Montgomery/Fejer 4/3 =",mp.nstr(mp.mpf(4)/3,10),")")
print()
print("TOLL CURVE, fixed MT kernel, band S=1  (W = 2A):")
print("   W      A=W/2     Z_MT(W)        toll = Z(W)-Z(0)")
Z0 = Zw(jM,0,jM(0))
for W in [0,0.1,0.2,0.3,0.4,0.416,0.5,0.6,0.8,1.0,1.5,2.0]:
    Z = Zw(jM,mp.mpf(W),jM(0))
    print(f"  {W:5.3f}  {W/2:6.3f}   {mp.nstr(Z,10):>14}   {mp.nstr(Z-Z0,6):>10}")
print()
print("PRIZE available over zeta23 Thm D at W=0, band S=2 (dip):")
print("   2 - 1.3212 - 0.6725007 =", mp.nstr(mp.mpf('1.3274993')-mp.mpf('1.3212'),6))
print("   i.e. the toll budget is 0.0063.  Fixed-MT toll reaches it at W ~",
      mp.nstr(mp.findroot(lambda W: Zw(jM,W,jM(0))-Z0-mp.mpf('0.0063'), 0.3),6))
