import RequestProject.RSStripSide

/-!
# Bounds and regularity for the Rankin–Selberg integrand

Slice five (d), first half: the analytic inputs for discharging the integrability of the RS
integrand.  Compiled here: the cusp form and the Petersson density are continuous
(`continuous_P`), the density is globally bounded (`P_bounded`, the compiled Hecke pointwise
bound read invariantly), the RS integrand's norm is the density times the real height power
(`norm_rsIntegrand`), the smoothed second moment decays exponentially at the cusp
(`rankin_series_exp_bound`, from the vanishing DC term — no new decay input needed), and the
`ofComplex` chart is measurable (`measurable_ofComplex`, through the coercion embedding).
No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups Pointwise NNReal

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- Cusp forms are continuous. -/
lemma continuous_cuspForm (f : CuspForm 𝒮ℒ k) : Continuous ⇑f :=
  (ModularFormClass.holo f).continuous

/-- The Petersson density is continuous. -/
lemma continuous_P (f : CuspForm 𝒮ℒ k) : Continuous (P k f) := by
  rw [show P k f = fun z : ℍ => z.im ^ k * Complex.normSq (f z) from rfl]
  apply Continuous.mul
  · exact UpperHalfPlane.continuous_im.zpow₀ k fun z => Or.inl z.im_ne_zero
  · exact Complex.continuous_normSq.comp (continuous_cuspForm f)

/-- The Petersson density is nonnegative. -/
lemma P_nonneg (f : CuspForm 𝒮ℒ k) (z : ℍ) : 0 ≤ P k f z := by
  rw [P]
  exact mul_nonneg (zpow_nonneg z.im_pos.le k) (Complex.normSq_nonneg _)

/-- **The Petersson density is globally bounded** — the compiled Hecke pointwise bound, read
invariantly. -/
lemma P_bounded (f : CuspForm 𝒮ℒ k) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℍ, P k f z ≤ M := by
  obtain ⟨M, hM⟩ := hecke_pointwise f
  refine ⟨M, hecke_pointwise_const_nonneg f hM, fun z => ?_⟩
  have h := hM z
  have him : (0 : ℝ) < z.im ^ k := zpow_pos z.im_pos k
  rw [P]
  calc z.im ^ k * Complex.normSq (f z) ≤ z.im ^ k * (M * z.im ^ (-k)) :=
        mul_le_mul_of_nonneg_left h him.le
    _ = M * (z.im ^ k * z.im ^ (-k)) := by ring
    _ = M := by
        rw [← zpow_add₀ z.im_pos.ne', add_neg_cancel, zpow_zero, mul_one]

/-- The RS integrand's norm is the density times the real height power. -/
lemma norm_rsIntegrand (f : CuspForm 𝒮ℒ k) (s : ℂ) (z : ℍ) :
    ‖rsIntegrand f s z‖ = P k f z * z.im ^ s.re := by
  rw [rsIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (P_nonneg f z), Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos]

/-- **Cusp decay of the smoothed second moment**: exponential decay above height one, from
the vanishing DC coefficient alone. -/
lemma rankin_series_exp_bound (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {y : ℝ} (hy : 1 ≤ y) :
    ∑' n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y)) ≤
      (Real.exp (4 * π) *
        ∑' n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * 1))) *
        Real.exp (-(4 * π) * y) := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
  have hterm : ∀ n : ℕ,
      ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y)) ≤
        Real.exp (4 * π) * Real.exp (-(4 * π) * y) *
          (‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * 1))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [qExpansion_coeff_zero_cusp f]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        zero_mul, mul_zero]
      positivity
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [show Real.exp (4 * π) * Real.exp (-(4 * π) * y) *
          (‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * 1))) =
          ‖(qExpansion 1 f).coeff n‖ ^ 2 *
            (Real.exp (4 * π) * Real.exp (-(4 * π) * y) * Real.exp (-(4 * π * n * 1)))
          by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr hy), Real.pi_pos]
  calc ∑' n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y))
      ≤ ∑' n : ℕ, Real.exp (4 * π) * Real.exp (-(4 * π) * y) *
          (‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * 1))) :=
        Summable.tsum_le_tsum hterm (summable_rankin_terms f hk hy0)
          ((summable_rankin_terms f hk one_pos).mul_left _)
    _ = (Real.exp (4 * π) *
          ∑' n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * 1))) *
          Real.exp (-(4 * π) * y) := by
        rw [tsum_mul_left]
        ring

/-- The `ofComplex` chart is measurable (through the coercion embedding). -/
lemma measurable_ofComplex : Measurable (UpperHalfPlane.ofComplex : ℂ → ℍ) := by
  rw [← UpperHalfPlane.measurableEmbedding_coe.measurable_comp_iff]
  have hfun : (UpperHalfPlane.coe ∘ UpperHalfPlane.ofComplex) = fun w : ℂ =>
      if 0 < w.im then w else ↑(Classical.choice (inferInstance : Nonempty ℍ)) := by
    funext w
    rcases lt_or_ge 0 w.im with h | h
    · rw [Function.comp_apply, ofComplex_apply_of_im_pos h, if_pos h]
    · rw [Function.comp_apply, ofComplex_apply_of_im_nonpos h,
        if_neg (not_lt.mpr h)]
  rw [hfun]
  exact Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im)
    measurable_id measurable_const

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.P_bounded
#print axioms CriticalLinePhasor.Unfolding.rankin_series_exp_bound
#print axioms CriticalLinePhasor.Unfolding.measurable_ofComplex
