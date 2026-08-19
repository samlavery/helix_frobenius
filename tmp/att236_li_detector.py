"""att236: SEAT SIDE done properly — Li's criterion as a detector that CAN fail.
lambda_n = sum_rho [1 - (1-1/rho)^n].  On-line: |1-1/rho| = |rho-1|/|rho| = 1
exactly, so each conjugate pair gives 2(1 - cos n*theta) >= 0 TERMWISE.
Off-line: the modulus leaves 1 and terms can be negative.  Controls:
 (a) true zeros -> lambda_n > 0, compare to known values;
 (b) FE-respecting off-line QUADRUPLE {beta+-i g, (1-beta)+-i g} -> must break."""
from mpmath import mp, mpf, mpc, nstr
mp.dps = 30
Z = [mpf(l.strip()) for l in open("tmp/zeros150_dps45.txt")]
KNOWN = {1:'0.0230957', 2:'0.0923457', 3:'0.2076389', 4:'0.3687904', 5:'0.5755427'}

def term(rho, n):
    return 1 - (1 - 1/rho)**n

def lam(n, extra=None):
    tot = mpc(0)
    for g in Z:
        for sgn in (1,-1):
            tot += term(mpc(mpf(1)/2, sgn*g), n)
    if extra is not None:
        b, g = extra
        for bb in (b, 1-b):
            for sgn in (1,-1):
                tot += term(mpc(bb, sgn*g), n)
    return tot

print("(a) TRUE zeros (150 pairs; tail truncated, so slight undercount):")
print("  n   computed        known")
for n in range(1,6):
    v = lam(n).real
    print(f"  {n}   {nstr(v,8):>12}   {KNOWN[n]}")

print("\n  modulus check |1-1/rho| for on-line rho (must be exactly 1):")
for g in Z[:3]:
    r = mpc(mpf(1)/2, g)
    print(f"    gamma={float(g):8.4f}:  |1-1/rho| = {nstr(abs(1-1/r),12)}")

print("\n(b) with an FE-respecting off-line quadruple beta=0.8, gamma=18:")
print("    |1-1/rho| at beta=0.8 :", nstr(abs(1-1/mpc(mpf('0.8'),mpf(18))),10))
print("    |1-1/rho| at beta=0.2 :", nstr(abs(1-1/mpc(mpf('0.2'),mpf(18))),10),
      " <- leaves the unit circle")
print("  n   true         planted      delta        planted < 0 ?")
for n in [1,2,3,5,10,20,40,80]:
    a = lam(n).real; b = lam(n, (mpf('0.8'), mpf(18))).real
    print(f"  {n:>3}  {nstr(a,7):>11}  {nstr(b,7):>11}  {nstr(b-a,4):>11}   {'YES' if b < 0 else 'no'}")
