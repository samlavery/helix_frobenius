import mpmath as mp, numpy as np
mp.mp.dps = 30
s1 = 1 + 2j*mp.pi/mp.log(2)
print("s1 =", mp.nstr(s1, 12))
print("2^(-s1) =", mp.nstr(mp.power(2, -s1), 15), "   (exactly 1/2)")
print("eta(s1) = ", mp.nstr(mp.altzeta(s1), 15))
print("zeta(s1) =", mp.nstr(mp.zeta(s1), 15))
# finite bank with the smooth window: R_P (odd) and R_M (even) at head Z
for Z in (400, 4000, 40000):
    n = np.arange(1, Z); w = np.exp(1 - 1/(1 - (n/Z)**2)); ph = w * n**(-1.0) * np.exp(-1j*float(s1.imag)*np.log(n))
    RP = ph[0::2].sum(); RM = ph[1::2].sum()
    print("Z=%6d  R_P=%s  R_M=%s  |R_P-R_M|=%.2e   R_M/(R_P+R_M)=%s" % (Z, np.round(RP,6), np.round(RM,6), abs(RP-RM), np.round(RM/(RP+RM),6)))
