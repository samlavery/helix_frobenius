"""HARMONIZED: the digit indicator is a SQUARE WAVE, and two rails obey a
cotangent addition law.

  c_p(a) = 1[0 <= a <= (p-1)/2] = 1/2 + (1/2) sigma_p(a)      <- common mode + square wave

Put every frequency on the quarter-turn phase  x = pi*alpha/(2p) in (0, pi/4]:

  |chat_p(alpha)| = (1/2p) csc x   alpha ODD    <- the square wave's own harmonics
                  = (1/2p) sec x   alpha EVEN   <- pure (+1/2) registration offset

Then the two-rail product harmonizes:

        csc x csc y  =  ( cot x + cot y ) / sin(x+y)

PRODUCT of amplitudes  ->  SUM of cotangents, over the amplitude at the REGISTERED
phase x+y -- which is exactly the carrier phase theta_alpha that S_N reads.
That identity IS the additive law.
"""
import math, cmath

def chat(alpha, p):
    D = (p + 1) // 2
    if alpha % p == 0: return D / p
    return sum(cmath.exp(-2j * math.pi * a * alpha / p) for a in range(D)) / p

# ---------- 1. the two lanes ----------
print("=" * 78)
print("1. TWO LANES on the quarter-turn  x = pi*alpha/(2p)")
print("=" * 78)
p = 101
print(f"{'alpha':>6} {'x/(pi/4)':>9} {'|chat| exact':>14} {'(1/2p)csc x':>13} {'(1/2p)sec x':>13} {'lane':>6}")
for alpha in [1, 2, 3, 4, 5, 11, 24, 25, 49, 50]:
    x = math.pi * alpha / (2 * p)
    print(f"{alpha:>6} {x/(math.pi/4):>9.4f} {abs(chat(alpha,p)):>14.9f} "
          f"{1/(2*p*math.sin(x)):>13.9f} {1/(2*p*math.cos(x)):>13.9f} "
          f"{'csc' if alpha%2 else 'SEC':>6}")

print("\n  max over EVEN alpha of 2p|chat| (claim: <= sec(pi/4) = 1.41421):")
for p in [11, 31, 101, 307, 1009, 4001]:
    m = max(2 * p * abs(chat(a, p)) for a in range(2, (p - 1) // 2 + 1, 2))
    print(f"    p={p:>5}   {m:.7f}   (sec(pi*alpha_max/2p) = "
          f"{1/math.cos(math.pi*((p-1)//2)/(2*p)):.7f})")

# ---------- 2. the cotangent addition law ----------
print("\n" + "=" * 78)
print("2. THE HARMONIZATION LAW:  csc x csc y = (cot x + cot y)/sin(x+y)")
print("=" * 78)
worst = 0.0
for (a, b) in [(0.3, 0.7), (0.11, 1.4), (0.001, 0.002), (0.5, 0.5), (1.2, 0.05)]:
    lhs = 1 / (math.sin(a) * math.sin(b))
    rhs = (1 / math.tan(a) + 1 / math.tan(b)) / math.sin(a + b)
    worst = max(worst, abs(lhs - rhs) / abs(lhs))
    print(f"  x={a:<6} y={b:<6}  lhs={lhs:>14.8f}  rhs={rhs:>14.8f}  rel={abs(lhs-rhs)/abs(lhs):.2e}")
print(f"  worst relative error: {worst:.3e}   -> identity exact")

print("\n  K-fold telescoping:  prod csc x_i = [prod_{m>=2}(cot(x_1+..+x_{m-1}) + cot x_m)]"
      " / sin(sum x_i)")
xs = [0.21, 0.37, 0.13, 0.44]
lhs = 1.0
for x in xs: lhs /= math.sin(x)
num, run = 1.0, xs[0]
for m in range(1, len(xs)):
    num *= (1 / math.tan(run) + 1 / math.tan(xs[m])); run += xs[m]
rhs = num / math.sin(sum(xs))
print(f"    K=4:  lhs={lhs:.8f}  rhs={rhs:.8f}  rel={abs(lhs-rhs)/lhs:.2e}")

# ---------- 3. lane mass: is the even (sec) lane really additive-cheap? ----------
print("\n" + "=" * 78)
print("3. LANE MASS   L = sum_{alpha != 0}|chat|,  split by parity")
print("=" * 78)
print(f"{'p':>6} {'L_csc':>9} {'L_sec':>9} {'L_sec (claim <=0.3536)':>24} {'L_csc/((log p)/2)':>19}")
for p in [11, 31, 101, 307, 1009, 4001]:
    Lo = sum(abs(chat(a, p)) for a in range(1, p) if a % 2 == 1)
    Le = sum(abs(chat(a, p)) for a in range(1, p) if a % 2 == 0)
    print(f"{p:>6} {Lo:>9.4f} {Le:>9.4f} {Le:>24.4f} {Lo/(math.log(p)/2):>19.4f}")

# ---------- 4. harmonize the measured constant ----------
print("\n" + "=" * 78)
print("4. HARMONIZE the measured constant C = 3.19 (max |err|/sum P_i over 38 configs)")
print("=" * 78)
C = 3.19
cands = {
    "pi^2/3": math.pi**2 / 3, "pi^2/6": math.pi**2 / 6, "pi": math.pi,
    "4/pi": 4 / math.pi, "pi^2/12": math.pi**2 / 12, "2pi/3": 2 * math.pi / 3,
    "pi^2/4": math.pi**2 / 4, "sqrt2*pi/2": math.sqrt(2) * math.pi / 2,
    "pi/3 * pi": math.pi**2 / 3, "3": 3.0,
}
for k, v in sorted(cands.items(), key=lambda kv: abs(kv[1] - C) / C):
    print(f"  {k:<12} {v:>9.5f}   rel err {100*abs(v-C)/C:>7.3f}%")
