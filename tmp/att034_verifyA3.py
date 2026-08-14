#!/usr/bin/env python3
"""
att034_verifyA3.py -- independent check of the ARITHMETIC of the repair:
  net(A) = 2 - Z(A) - C e^{-cA},  C from Simonic Thm 1 / Bellotti-Wong Cor 1.3.
Also a RIGOROUS analytic lower bound Z(A) >= (2A/pi)(1 - G/A^2) valid for the whole
strip class, so the large-A behaviour needs no SDP at all.
NULL: the reported max_A net = -28.33 at A ~ 44.4 with C = 130630, c = 1/4.
"""
import numpy as np
from scipy.optimize import minimize_scalar, brentq
from scipy.integrate import quad

G = 0.915965594177219015   # Catalan
MT = 0.5 + (1/np.sqrt(2))/np.tan(1/np.sqrt(2))
print("Montgomery-Taylor 1/c*_1 = %.10f ; target proportion 2 - it = %.10f" % (MT, 2-MT))

# ---- Simonic Thm 1 at source:  N(s,2T)-N(s,T) <= a T^{1-(1/4)(s-1/2)} log T + ...
#      a = 10395.2 (Thm 1) / 10395.21 (his Corollary).  Method floor 3.259.
# ---- N(2T)-N(T) ~ (T/2pi) log T  (Bellotti-Wong Cor 1.3 error O(log T)).
for a, tag in [(10395.21, "Simonic Thm1 (his Cor constant)"),
               (10395.2,  "Simonic Thm1 (Thm statement)"),
               (5.357,    "Simonic (5), T>=10^50, s<=0.569"),
               (3.259,    "Simonic's own METHOD FLOOR")]:
    C1 = 2*np.pi*a            # one-sided, after dividing by (T/2pi) log T
    C2 = 2*C1                 # two-sided (beta > 1/2 + A/logT and beta < 1/2 - A/logT)
    print("  a=%-10.4f  one-sided C=%12.2f  two-sided C=%12.2f  charge<1 for A> %.4f"
          % (a, C1, C2, 4*np.log(C2)))

CC = 2*(2*np.pi*10395.21)
print("\nheadline C (two-sided) = %.2f   (report says 130,630)" % CC)

# ---- rigorous lower bound on Z(A) for the whole strip class -------------------
# rhat = hhat * sech(2 A a), hhat positive definite => |hhat(a)| <= hhat(0).
#   rhat(0) = hhat(0);  r(0) = int rhat <= hhat(0) * pi/(2A);
#   int_{-1}^{1}|a| rhat >= -hhat(0) * int |a| sech(2Aa) da = -hhat(0) * G/A^2
# => Z >= (2A/pi) (1 - G/A^2).
def Zlow(A):
    return (2*A/np.pi)*(1 - G/A**2)

# sanity: numerically confirm  int_{-inf}^{inf} |a| sech(2 A a) da = G/A^2
for A in [0.5, 1.0, 3.0]:
    num = 2*quad(lambda t: t/np.cosh(2*A*t), 0, 200/A)[0]
    print("  check int|a|sech(2Aa)da at A=%.1f : numeric %.10f  formula G/A^2 %.10f"
          % (A, num, G/A**2))

print("\n rigorous Z lower bound: A=2 -> %.4f   A=12 -> %.4f   A=44 -> %.4f"
      % (Zlow(2), Zlow(12), Zlow(44)))

# ---- net constant, count-only charge -----------------------------------------
def net_upper(A, C, c=0.25):
    """UPPER bound on 2 - Z(A) - C e^{-cA}, using Z >= Zlow (so -Z <= -Zlow)."""
    return 2 - Zlow(A) - C*np.exp(-c*A)

print("\n" + "="*74)
print("max over A of [2 - Z(A) - C e^{-A/4}]  (UPPER bound, uses rigorous Zlow)")
print("="*74)
for C, tag in [(CC, "Simonic Thm 1, two-sided"),
               (CC/2, "Simonic Thm 1, one-sided only"),
               (2*2*np.pi*3.259, "Simonic method floor, two-sided"),
               (1.0, "fantasy C = 1")]:
    r = minimize_scalar(lambda A: -net_upper(A, C), bounds=(1.5, 400), method='bounded',
                        options={'xatol': 1e-8})
    print("  C=%12.2f  (%-32s)  max = %+10.4f at A = %.3f" % (C, tag, -r.fun, r.x))

print("\n  [note: for A <~ 1.5 the SDP value of Z(A) is ~1.31-1.45, so 2-Z <= 0.69;")
print("   the charge there is C e^{-A/4} >= C e^{-0.375} which for C=130630 is 8.9e4.]")
print("  net at A=0    : 2 - 1.3212 - %.1f = %.1f" % (CC, 2-1.3212-CC))
print("  net at A=0.208: 2 - 1.3275 - %.1f = %.1f" % (CC*np.exp(-0.208/4), 2-1.3275-CC*np.exp(-0.208/4)))

# ---- requirement inversion ---------------------------------------------------
print("\n" + "="*74)
print("REQUIREMENT INVERSION: what density exponent c makes the route work?")
print("="*74)
def best(c, C):
    r = minimize_scalar(lambda A: -(2 - Zlow(A) - C*np.exp(-c*A)),
                        bounds=(1.5, 4000), method='bounded', options={'xatol': 1e-9})
    return -r.fun
for C in [1.0, 2*2*np.pi*3.259, CC]:
    try:
        creq = brentq(lambda c: best(c, C) - (2-MT), 0.2, 4000, xtol=1e-6)
        print("  C=%12.2f  needs c >= %8.3f   (Selberg-Simonic c = 0.25; short by %.0fx)"
              % (C, creq, creq/0.25))
    except Exception as e:
        print("  C=%12.2f  bracket fail %s" % (C, e))

# ---- AMPLIFIED charge --------------------------------------------------------
print("\n" + "="*74)
print("AMPLIFIED charge C e^{(2S-c)A}: monotone increasing whenever c < 2S")
print("="*74)
for S in [1.0, 2.0]:
    print("  S=%.1f : exponent 2S-c = %.2f > 0 for c=0.25 -> min at A=0, value C=%.0f"
          % (S, 2*S-0.25, CC))
    print("         mere convergence needs c > %.0f" % (2*S))
