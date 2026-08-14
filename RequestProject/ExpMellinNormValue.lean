import RequestProject.ExpMellinConvergent

/-!
# The integrated norm of the Gamma integrand

Step (ii) of the lattice-theta interchange: the summability hypothesis of `mellin_tsum_countable`
asks for the *integrated norms* to be summable, so those norms have to be evaluated.

They are the Gamma integral at the real exponent:

  `∫₀^∞ ‖t^{s-1}·e^{-at}‖ dt = Γ(σ)·a^{-σ}`,  `σ = Re s`.

Only the real part of `s` survives the norm — the imaginary part rotates the integrand without
changing its modulus.  That is why the summability question is governed by `σ` alone, and hence by
`summable_gram_rpow`, which is stated at a real exponent.
-/

open Complex MeasureTheory
open scoped Real

namespace CriticalLinePhasor.ThreeDConverse

/-- **The integrated norm of the Gamma integrand is `Γ(σ)·a^{-σ}`.** -/
theorem integral_norm_mellin_exp {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    (∫ t in Set.Ioi (0:ℝ), ‖(t : ℂ) ^ (s - 1) • ((Real.exp (-(a * t)) : ℝ) : ℂ)‖) =
      Real.Gamma s.re * a ^ (-s.re) := by
  have hsre : (0:ℝ) < ((s.re : ℝ) : ℂ).re := by simpa using hs
  have hmel := CriticalLinePhasor.Unfolding.mellin_exp_neg_mul ha (s := ((s.re : ℝ) : ℂ)) hsre
  -- the Mellin transform at the real exponent is the coercion of a real integral
  have hre : mellin (fun t : ℝ => ((Real.exp (-(a * t)) : ℝ) : ℂ)) ((s.re : ℝ) : ℂ) =
      ((∫ t in Set.Ioi (0:ℝ), t ^ (s.re - 1) * Real.exp (-(a * t)) : ℝ) : ℂ) := by
    rw [mellin, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0:ℝ) < t := ht
    rw [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_cpow ht0.le]
    congr 2
    push_cast
    ring
  -- the norm of the integrand is the real integrand
  have hnorm : (∫ t in Set.Ioi (0:ℝ),
      ‖(t : ℂ) ^ (s - 1) • ((Real.exp (-(a * t)) : ℝ) : ℂ)‖) =
      ∫ t in Set.Ioi (0:ℝ), t ^ (s.re - 1) * Real.exp (-(a * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0:ℝ) < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    congr 2
  rw [hnorm]
  have hval : ((∫ t in Set.Ioi (0:ℝ), t ^ (s.re - 1) * Real.exp (-(a * t)) : ℝ) : ℂ) =
      ((Real.Gamma s.re * a ^ (-s.re) : ℝ) : ℂ) := by
    rw [← hre, hmel, Complex.ofReal_mul, Complex.ofReal_cpow ha.le,
      ← Complex.Gamma_ofReal]
    push_cast
    ring
  exact_mod_cast hval

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.integral_norm_mellin_exp
