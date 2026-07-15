import RequestProject.SupBoundDischarge

/-!
# Hecke's coefficient bound, unconditional

The pointwise bound of `SupBoundDischarge` converts, through the `q`-expansion coefficient
integral at height `t = 1/n`, into Hecke's classical coefficient bound
`‖a_n‖² ≤ M·n^k` — compiled from pure modularity.  This is the summability workhorse of the
cancellation program: it discharges the convergence side conditions of the ladder transfer and
the theta constructions for the actual cusp-form banks.  No RH/GRH.
-/

open UpperHalfPlane Complex Filter Matrix.SpecialLinearGroup Function
open scoped MatrixGroups Real

namespace CriticalLinePhasor.HeckeSupBound

/-- The pointwise constant is nonnegative. -/
lemma hecke_pointwise_const_nonneg {k : ℤ} (f : CuspForm 𝒮ℒ k) {M : ℝ}
    (hM : ∀ z : ℍ, Complex.normSq (f z) ≤ M * z.im ^ (-k)) : 0 ≤ M := by
  have hz : (⟨Complex.I, by simp⟩ : ℍ).im = 1 := by
    simp [UpperHalfPlane.im]
  have h := hM ⟨Complex.I, by simp⟩
  rw [hz, one_zpow] at h
  exact le_trans (Complex.normSq_nonneg _) (by simpa using h)

/-- **Hecke's coefficient bound**: `‖a_n‖² ≤ M·n^k` for the `q`-expansion coefficients of a
level-one cusp form, from the pointwise bound at height `1/n`. -/
theorem hecke_coeff_sq_bound {k : ℤ} (f : CuspForm 𝒮ℒ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, 1 ≤ n →
      ‖(qExpansion 1 f).coeff n‖ ^ 2 ≤ M * (n : ℝ) ^ k := by
  obtain ⟨M₀, hM₀⟩ := hecke_pointwise f
  have hM₀nn : 0 ≤ M₀ := hecke_pointwise_const_nonneg f hM₀
  refine ⟨Real.exp (4 * π) * M₀, by positivity, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set t : ℝ := 1 / n with ht_def
  have ht : 0 < t := by positivity
  have hcoeff := ModularFormClass.qExpansion_coeff_eq_intervalIntegral (f := f) one_pos
    one_mem_strictPeriods_SL n ht
  have htk : t ^ (-k) = (n : ℝ) ^ k := by
    rw [ht_def, one_div, inv_zpow, ← zpow_neg, neg_neg]
  -- pointwise bound of the integrand
  have hint : ∀ u : ℝ,
      ‖1 / Periodic.qParam 1 (u + t * Complex.I) ^ n *
        f (⟨u + t * Complex.I, by simpa using ht⟩ : ℍ)‖ ≤
      Real.exp (2 * π) * Real.sqrt (M₀ * (n : ℝ) ^ k) := by
    intro u
    have hq : ‖Periodic.qParam 1 (u + t * Complex.I)‖ = Real.exp (-2 * π * t) := by
      rw [Periodic.norm_qParam]
      congr 1
      simp
    have hfz : ‖f (⟨u + t * Complex.I, by simpa using ht⟩ : ℍ)‖ ≤
        Real.sqrt (M₀ * (n : ℝ) ^ k) := by
      have hn2 := hM₀ (⟨u + t * Complex.I, by simpa using ht⟩ : ℍ)
      rw [Complex.normSq_eq_norm_sq] at hn2
      have himz : (⟨u + t * Complex.I, by simpa using ht⟩ : ℍ).im = t := by
        simp [UpperHalfPlane.im]
      rw [himz, htk] at hn2
      calc ‖f (⟨u + t * Complex.I, by simpa using ht⟩ : ℍ)‖
          = Real.sqrt (‖f (⟨u + t * Complex.I, by simpa using ht⟩ : ℍ)‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (M₀ * (n : ℝ) ^ k) := Real.sqrt_le_sqrt hn2
    rw [norm_mul, norm_div, norm_one, norm_pow, hq, ← Real.exp_nat_mul]
    have hexp : (1 : ℝ) / Real.exp (n * (-2 * π * t)) = Real.exp (2 * π) := by
      rw [one_div, ← Real.exp_neg]
      congr 1
      rw [ht_def]
      field_simp
    rw [hexp]
    exact mul_le_mul_of_nonneg_left hfz (Real.exp_pos _).le
  -- integrate
  have hbound : ‖(qExpansion 1 f).coeff n‖ ≤
      Real.exp (2 * π) * Real.sqrt (M₀ * (n : ℝ) ^ k) := by
    rw [hcoeff]
    calc ‖(1 : ℂ) / 1 * ∫ u in (0:ℝ)..1, 1 / Periodic.qParam 1 (u + t * Complex.I) ^ n *
          f (⟨u + t * Complex.I, by simpa using ht⟩ : ℍ)‖
        = ‖∫ u in (0:ℝ)..1, 1 / Periodic.qParam 1 (u + t * Complex.I) ^ n *
          f (⟨u + t * Complex.I, by simpa using ht⟩ : ℍ)‖ := by
          norm_num
      _ ≤ Real.exp (2 * π) * Real.sqrt (M₀ * (n : ℝ) ^ k) * |1 - 0| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro u _
          exact hint u
      _ = Real.exp (2 * π) * Real.sqrt (M₀ * (n : ℝ) ^ k) := by
          norm_num
  calc ‖(qExpansion 1 f).coeff n‖ ^ 2
      ≤ (Real.exp (2 * π) * Real.sqrt (M₀ * (n : ℝ) ^ k)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = Real.exp (2 * π) ^ 2 * Real.sqrt (M₀ * (n : ℝ) ^ k) ^ 2 := by ring
    _ = Real.exp (4 * π) * (M₀ * (n : ℝ) ^ k) := by
        rw [Real.sq_sqrt (mul_nonneg hM₀nn (zpow_nonneg hnpos.le k)), sq, ← Real.exp_add,
          show 2 * π + 2 * π = 4 * π by ring]
    _ = Real.exp (4 * π) * M₀ * (n : ℝ) ^ k := by ring

end CriticalLinePhasor.HeckeSupBound

#print axioms CriticalLinePhasor.HeckeSupBound.hecke_coeff_sq_bound
