import RequestProject.LambdaGramIdentity
import RequestProject.RSPoleStructure

/-!
# The pointwise pole structure of the Eisenstein coset sum

Item (3) integrates a pointwise statement, so the pointwise statement has to be isolated first.

`lambda_eq_zeta_mul_cosetSum` gives `Λ = π^{-s}Γ(s)·ζ(2s)·(2·E(z,s))` and `lambda_pole_split` gives
`Λ = Λ₀ − 1/s − 1/(1−s)` with `Λ₀` entire.  Dividing:

  **`2·E(z,s) = (Λ₀(z,s) − 1/s − 1/(1−s)) / (π^{-s}Γ(s)ζ(2s))`.**

Every factor of the denominator is nonvanishing on `Re s > 1` for its own reason — `π^{-s}` because
a `cpow` of a nonzero base never vanishes, `Γ` because the Gamma function has no zeros at all, and
`ζ(2s)` because `Re(2s) > 2 > 1` puts it in the Euler-product region, where it is an exponential.
None of these is an estimate.

What remains for item (3) is `z`-uniform control of `Λ₀` so that the quotient can be integrated
against `‖u‖²` over `𝒟`; that is not done here.
-/

open Complex UpperHalfPlane
open scoped Real

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta

/-- The completed archimedean-times-zeta factor does not vanish on `Re s > 1`. -/
lemma archimedean_zeta_factor_ne_zero {s : ℂ} (hs : 1 < s.re) :
    ((Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s * riemannZeta (2 * s) ≠ 0 := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsne : -s ≠ 0 := by
    intro h
    have : s = 0 := by linear_combination -h
    rw [this] at hs; simp at hs; linarith
  have h1 : ((Real.pi : ℝ) : ℂ) ^ (-s) ≠ 0 :=
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero hsne).mpr hpi
  have h2 : Complex.Gamma s ≠ 0 := by
    refine Complex.Gamma_ne_zero fun n => ?_
    intro hcon
    rw [hcon] at hs
    simp at hs
    linarith [hs]
  have h3 : riemannZeta (2 * s) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    have : (2 * s).re = 2 * s.re := by simp
    rw [this]; linarith
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

/-- **The Eisenstein coset sum, solved for.**  Its pole structure in `s` is entirely the Epstein
kernel's, divided by a nonvanishing completed factor. -/
theorem cosetSum_eq_lambda_quotient (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    2 * ∑' q : CosetQ, ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s) =
      ((generalFEPair z).Λ₀ s - 1 / s - 1 / (1 - s)) /
        (((Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s * riemannZeta (2 * s)) := by
  have hne := archimedean_zeta_factor_ne_zero hs
  have hid := lambda_eq_zeta_mul_cosetSum z hs
  rw [lambda_pole_split z s] at hid
  rw [eq_div_iff hne]
  linear_combination -hid

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.archimedean_zeta_factor_ne_zero
#print axioms CriticalLinePhasor.Unfolding.cosetSum_eq_lambda_quotient
