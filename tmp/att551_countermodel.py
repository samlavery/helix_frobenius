# Step 4 countermodel (closed form + adversarial numeric check).
# Kernel: Phi*(u) = g(u) + (lam/2)(g(u-a)+g(u+a)),  g = exp(-u^2/2),  0<lam<1.
#   EVEN: yes.  POSITIVE: sum of positive Gaussians.  SCHWARTZ decay: yes.
#   DC split: Phi* = (positive zero mode) + (positive modes): yes.
# Transform: F(z) = int Phi* e^{izu} du = ghat(z)*(1 + lam*cos(a z)),
#   ghat(z) = sqrt(2pi) exp(-z^2/2)  (never zero).
# Zeros: cos(a z) = -1/lam < -1  =>  z = (2k+1)pi/a  +/- i*arccosh(1/lam)/a
#   -- STRICTLY COMPLEX (off the real axis) => in the s-chart, off-line zeros
#   => native-seat/HB/cross-term positivity FAILS for F.
# Pre-registered: |bracket(z0)| < 1e-20 confirms the exact zero; report the
# violated supply statement.
from mpmath import mp, mpf, mpc, cos, cosh, acosh, pi, sqrt, exp, quad, inf, j
mp.dps = 30
lam, a = mpf('0.5'), mpf('2.0')
z0 = pi/a + j*acosh(1/lam)/a
bracket = 1 + lam*cos(a*z0)
print("z0 =", z0, "  Im z0 =", float(z0.imag), "(off-real)")
print("|1 + lam*cos(a z0)| =", float(abs(bracket)))
# direct integral check of F(z0) ~ 0 (adversarial: don't trust the algebra)
Phi = lambda u: exp(-u**2/2) + (lam/2)*(exp(-(u-a)**2/2) + exp(-(u+a)**2/2))
F = quad(lambda u: Phi(u)*exp(j*z0*u), [-inf, inf])
print("|F(z0)| by direct integration =", float(abs(F)))
print("Phi positivity spot checks:", all(Phi(mpf(x)) > 0 for x in [-9,-3,-1,0,1,3,9]))
