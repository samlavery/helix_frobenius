# att637b — correction of att637 P5. A remainder term e^{ρu} in R(u) = ψ(e^u) − e^u is the atom at 1 − ρ
# (e^{bu} du ↦ −1/(s − (1−b)) under ∫ e^{−(1−s)u} · du), so the planted remainder R(u) = −2Re(e^{ρu}/ρ)
# has paired-prime coefficients ω_{1−ρ} w_{1−ρ}^{k+1} + ω_{1−ρ̄} w_{1−ρ̄}^{k+1}. att637 evaluated w(ρ) instead
# of w(1−ρ) and so printed |w| < 1 for β > ½ — contradicting the compiled modulus law (634, `norm_transport_sq`),
# which is how it was caught. Here: the correct atoms, and a direct Laplace-integral check of the coefficients.
from mpmath import mp, mpc, mpf, exp, quad, inf, fabs, log, laguerre, conj
mp.dps = 25
s0 = mpc(-1, 20); c = 1 - conj(s0); d = 2 * s0.real - 1; sp = 1 - s0
def w(a): return (a - c) / (s0 - a)
def om(a): return 1 / ((s0 - a) * (a - c))
def P(k, u): return u / (k + 1) * laguerre(k, 1, 3 * u)
out = []
def pr(*a):
    s = " ".join(str(x) for x in a); print(s); out.append(s)
pr("att637b  planted remainder R(u) = −2Re(e^{ρu}/ρ): atoms at 1−ρ and 1−ρ̄; |w_a|² = 1 + 3(2Re a − 1)... sign: |w_a| > 1 iff Re a < ½")
pr("   β     γ      |w_{1−ρ}|      |w_{1−ρ̄}|     growth base     e-fold k")
for beta, gv in ((0.5, 50.0), (0.51, 50.0), (0.6, 50.0), (0.6, 5000.0), (0.75, 1000.0), (0.4, 50.0)):
    rho = mpc(beta, gv); a1 = 1 - rho; a2 = 1 - conj(rho)
    base = max(fabs(w(a1)), fabs(w(a2)))
    pr("  %.2f  %6.0f   %.10f   %.10f   %.10f   %s" % (beta, gv, fabs(w(a1)), fabs(w(a2)), base,
       "∞" if base <= 1 else "%d" % round(1 / float(log(base)))))
pr("direct check, ρ = 0.6 + 50i: μ_{k+1} = (−1)^{k+1} ∫_0^∞ e^{−s'u} P_k(u) dR(u), dR = −(e^{ρu} + e^{ρ̄u}) du, vs the atom formula")
rho = mpc(0.6, 50); a1 = 1 - rho; a2 = 1 - conj(rho)
pr("      k     |integral|          |atoms|            |diff|")
for k in (0, 1, 5, 20, 60):
    # the integrand is a degree-(k+1) polynomial times e^{−(1.4 ∓ 70i)u}: size up to ~10^3 at k = 20 cancelling to 10^{−3};
    # first pass at dps 25 with 7 panels failed at k = 20, 60 (0.75, 1.0e2 against 9e−4) — quadrature, not the identity
    f = lambda u: exp(-sp * u) * P(k, u) * (-(exp(rho * u) + exp(conj(rho) * u)))
    with mp.workdps(60):
        pts = [mpf(j) / 4 for j in range(0, 4 * (4 * k + 60) + 1)] + [inf]
        val = (-1) ** (k + 1) * quad(f, pts)
    atoms = om(a1) * w(a1) ** (k + 1) + om(a2) * w(a2) ** (k + 1)
    pr("     %2d   %.12e   %.12e   %.1e" % (k, fabs(val), fabs(atoms), fabs(val - atoms)))
pr("atom growth at k = 10^3, 10^4, 10^5 for ρ = 0.6+50i: %s" % ["%.3e" % float(fabs(om(a1)) * fabs(w(a1)) ** kk) for kk in (10 ** 3, 10 ** 4, 10 ** 5)])
open("tmp/att637b_results.txt", "w").write("\n".join(out) + "\n")
