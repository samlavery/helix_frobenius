"""Why the resonant pairs stayed clean: the digit kernel is a SQUARE WAVE.

c(a) = 1[0 <= a <= (p-1)/2] = 1/2 + 1/2 sigma(a),  sigma = half-circle sign.
A square wave has only ODD harmonics.  Exactly:

   chat(alpha) = (1/p) sin(pi |D| alpha / p) / sin(pi alpha / p),  |D| = (p+1)/2
              = (1/(2p)) / sin(pi alpha / 2p)    for alpha ODD
              = (1/(2p)) / cos(pi alpha / 2p)    for alpha EVEN

So |chat| <= 1/(2|alpha|) on odd alpha, but <= 1/(sqrt2 p) on EVEN alpha --
uniformly of size 1/p, NOT 1/alpha.  The even harmonics are pure (+1)-defect:
they exist only because p is odd, i.e. |D| = p/2 + 1/2.

Test both formulas exactly, then check the parity mass split.
"""
import math, cmath

def chat(alpha, p):
    D = (p + 1) // 2
    if alpha % p == 0: return D / p
    return sum(cmath.exp(-2j * math.pi * a * alpha / p) for a in range(D)) / p

print("exact kernel vs the two closed forms (p = 101):")
p = 101
print(f"{'alpha':>6} {'|chat| exact':>14} {'closed form':>14} {'1/(2a) bound':>14} {'parity':>7}")
for alpha in [1, 2, 3, 4, 5, 10, 11, 24, 25, 50]:
    ex = abs(chat(alpha, p))
    if alpha % 2 == 1:
        cf = 1 / (2 * p * math.sin(math.pi * alpha / (2 * p)))
    else:
        cf = 1 / (2 * p * math.cos(math.pi * alpha / (2 * p)))
    print(f"{alpha:>6} {ex:>14.8f} {cf:>14.8f} {1/(2*alpha):>14.8f} "
          f"{'odd' if alpha%2 else 'EVEN':>7}")

print("\nparity mass split, L = sum_{alpha != 0} |chat(alpha)|:")
print(f"{'p':>6} {'L_odd':>10} {'L_even':>10} {'L_even*p':>10} {'(log p)/4':>10}")
for p in [11, 31, 101, 307, 1009]:
    Lo = sum(abs(chat(a, p)) for a in range(1, p) if a % 2 == 1)
    Le = sum(abs(chat(a, p)) for a in range(1, p) if a % 2 == 0)
    print(f"{p:>6} {Lo:>10.4f} {Le:>10.4f} {Le*p:>10.2f} {math.log(p)/4:>10.4f}")

print("\nmax_{even alpha, |alpha|<=p/2} p*|chat|  (claim: <= 1/sqrt2 = 0.7071):")
for p in [11, 31, 101, 307, 1009, 4001]:
    m = max(p * abs(chat(a, p)) for a in range(2, p // 2 + 1, 2))
    print(f"  p={p:>5}   {m:.6f}")
