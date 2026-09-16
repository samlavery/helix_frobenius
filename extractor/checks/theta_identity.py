"""arg Gamma_R(1/2+it) == Riemann-Siegel theta(t), to 40 digits, t up to 1e4.

Gamma_R(s) = pi^{-s/2} Gamma(s/2), so
  arg Gamma_R(1/2+it) = arg Gamma(1/4+it/2) - (t/2) log pi = theta(t).
Pre-registered: agreement to <= 1e-38 at every sample REFUTES nothing and
confirms the identity; any sample above 1e-30 refutes the paper's remark.
"""
from mpmath import mp, mpf, mpc, gamma, arg, pi, log, siegeltheta, power

mp.dps = 60

def arg_gammaR(t):
    s = mpc(mpf(1)/2, t)
    return arg(power(pi, -s/2) * gamma(s/2))

ts = [mpf(0), mpf(1)/10, mpf(1), mpf(2), mpf('6.28318'), mpf(10), mpf(14.134725),
      mpf(50), mpf(100), mpf(1000), mpf(5000), mpf(9999), mpf(10000)]

worst = mpf(0)
print("        t            |argGammaR - theta|      branch-corrected")
for t in ts:
    a = arg_gammaR(t)
    th = siegeltheta(t)
    raw = abs(a - th)
    # arg returns principal value in (-pi,pi]; theta is the continuous branch
    k = int(mp.nint((th - a) / (2*pi)))
    corr = abs(a + 2*k*pi - th)
    worst = max(worst, corr)
    print(f"{mp.nstr(t,8):>12}   {mp.nstr(raw,6):>18}   {mp.nstr(corr,6):>18}")

print()
print(f"worst branch-corrected discrepancy over the sample: {mp.nstr(worst,6)}")
print("VERDICT:", "CONFIRMED (<= 1e-38)" if worst <= mpf('1e-38') else "REFUTED")
