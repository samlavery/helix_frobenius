# ADVERSARIAL VERIFICATION, gate AV1 (restatement).
# NULL (written before running): the "strip-repaired" functional is NOT BGSTB's
# printed Tsang functional -- i.e. it does NOT reproduce 0.608612927 (Fejer) and
# 0.617483786 (Montgomery-Taylor) to >= 8 digits.  REJECT the null if it does.
import mpmath as mp
mp.mp.dps = 30

jF = lambda a: mp.mpf(1)-a          # on [0,1]
r2 = mp.sqrt(2)
norm = 1 - mp.cos(r2)
def jM(a):
    f = jF(a)
    return (mp.sin(r2*f)/r2 + f*mp.cos(r2*a)) / 2 / norm

sech = lambda u: 1/mp.cosh(u)

def gates(j, name, jzero):
    I_alpha = 2*mp.quad(lambda a: a*j(a)*sech(a), [0,1])
    I_den   =   mp.quad(lambda a:   j(a)*sech(a), [0,1])
    Z = (jzero + I_alpha)/(2*I_den)
    print(f"{name}:  j(0)={mp.nstr(jzero,12)}  2*int a j sech = {mp.nstr(I_alpha,12)}"
          f"  int j sech = {mp.nstr(I_den,12)}")
    print(f"      Z = {mp.nstr(Z,12)}    2-Z = {mp.nstr(2-Z,12)}")
    return Z

print("=== AV1: BGSTB (7.2) reproduction ===")
ZF = gates(jF, "Fejer      ", mp.mpf(1))
print("      BGSTB printed: 0.2913876354, 0.4640648392, 2-Z = 0.608612927")
ZM = gates(jM, "Mont-Taylor", jM(0))
print("      BGSTB printed: jM(0)=1.0061271908, 0.2832624869, 0.4663199124, 2-Z = 0.617483786")

print()
print("=== AV2: zeta23 Theorem D closed form ===")
c = mp.mpf(1)/2 + mp.cot(1/mp.sqrt(2))/mp.sqrt(2)
print("  1/2 + 2^{-1/2} cot(2^{-1/2}) =", mp.nstr(c,12), "  2 - it =", mp.nstr(2-c,12))
print("  (zeta23 Thm D prints 1.3274993 / 0.6725007)")
