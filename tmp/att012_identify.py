"""ATTEMPT 012, stage 4 -- RESTATEMENT CHECK against the literature (rule 2 + rule 6).

Source read at source: Chirre & Quesada-Herrera, "The second moment of S_n(t) on the Riemann
hypothesis", arXiv:2006.08503v2, eq. (1.8), which states GOLDSTON's 1987 theorem for n = 0:

    int_0^T |S(t)|^2 dt
        = (T/2pi^2) log log T
        + (T/2pi^2) [ int_1^inf F(alpha)/alpha^2 d alpha  +  gamma_0
                      -  sum_{m=2}^inf sum_p (1/m - 1/m^2) p^{-m} ]   +  o(T),

with F = Montgomery's pair-correlation function and gamma_0 = Euler's constant.
(Selberg 1946, eq (1.4): the same leading term unconditionally, error O(T sqrt(log log T)).)

WHAT THIS ATTEMPT PRODUCED, independently, from the theta-tape form factor:

    Var S = (1/2pi^2) [ log L + M + C_pp + 1 ],    L = log(T/2pi),
    M = Mertens' constant, C_pp = sum_{k>=2} P(k)/k^2, and the "+1" = int_1^inf K(tau)/tau^2 dtau
    with K(tau) = 1 beyond the Heisenberg edge.

CHECKED BELOW, numerically to 15 digits:
    (A)   M + C_pp  ==  gamma_0 - sum_{m>=2} (1/m - 1/m^2) P(m)      [the arithmetic constant]
    (B)   "+1"      ==  int_1^inf F(alpha)/alpha^2 d alpha  under Montgomery's pair correlation
                        conjecture F(alpha) = 1 for alpha > 1.
If (A) holds identically then this attempt's formula IS Goldston (1987) and NOTHING about the
formula is new; the deliverables are only the numbers (verification, calibration, and a direct
measurement of int_1^inf F/alpha^2).
"""
import mpmath as mp
mp.mp.dps = 40
gam0 = mp.euler
M = -mp.nsum(lambda m: mp.primezeta(m)/m, [2, mp.inf]) + gam0        # Mertens: gamma - sum P(m)/m
Cpp = mp.nsum(lambda m: mp.primezeta(m)/m**2, [2, mp.inf])
gold = gam0 - mp.nsum(lambda m: (mp.mpf(1)/m - mp.mpf(1)/m**2)*mp.primezeta(m), [2, mp.inf])
print("Mertens M                                        =", mp.nstr(M, 25))
print("  (literature value 0.2614972128476427837554268)")
print("C_pp = sum_{k>=2} P(k)/k^2                       =", mp.nstr(Cpp, 25))
print("mine:      M + C_pp                              =", mp.nstr(M+Cpp, 25))
print("Goldston:  gamma_0 - sum_m (1/m - 1/m^2) P(m)    =", mp.nstr(gold, 25))
print("difference                                       =", mp.nstr(M+Cpp-gold, 5))
print()
print("=> (A) HOLDS IDENTICALLY.  M + C_pp = gamma - sum_p sum_{m>=2} (1/m - 1/m^2) p^{-m},")
print("   because M = gamma - sum_p sum_{m>=2} 1/(m p^m) and C_pp = sum_p sum_{m>=2} 1/(m^2 p^m).")
print("   The two constants are the same object written two ways.  NO NOVELTY: the formula")
print("   measured in this attempt is Goldston 1987 with int_1^inf F/alpha^2 = 1, i.e. with")
print("   Montgomery's pair correlation conjecture in the range alpha > 1.")
print()
print("MEASURED value of  int_1^inf F(alpha)/alpha^2 d alpha  (= 2 pi^2 * the tau>1 tape band):")
for T, band in (('1e+03', 0.051186), ('1e+04', 0.051269), ('1e+05', 0.051222),
                ('1e+06', 0.051404), ('1e+07', 0.051568)):
    print(f"   T = {T}:   {float(2*mp.pi**2*band):.4f}      (Montgomery PCC predicts exactly 1)")
print()
print("full finite-height formula, exact values:")
print(f"   1/(2 pi^2) = {mp.nstr(1/(2*mp.pi**2), 15)}")
for T in (1e3, 1e4, 1e5, 1e6, 1e7, 1e12, 1e22):
    L = mp.log(T/(2*mp.pi))
    print(f"   T = {T:.0e}:  (1/2pi^2)[log L + M + C_pp + 1] = "
          f"{mp.nstr((mp.log(L)+M+Cpp+1)/(2*mp.pi**2), 8)}   "
          f"(asymptotic loglogT/(2pi^2) = {mp.nstr(mp.log(mp.log(T))/(2*mp.pi**2), 8)})")
