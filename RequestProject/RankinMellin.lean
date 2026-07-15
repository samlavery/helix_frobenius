import RequestProject.RankinBound
import RequestProject.HeckeCoeffBound
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

/-!
# The Rankin–Selberg Dirichlet series as the Mellin readout of the smoothed second moment

The identification step: the compiled smoothed second moment
`R(y) = ∑' n, ‖a_n‖²·e^{-4πny}` (bounded by `M·y^{-k}` in `rankin_smoothed_bound`) has Mellin
transform exactly the completed Rankin–Selberg Dirichlet series,

  `mellin R s = Γ(s) · ∑' n, ‖a_n‖² / (4πn)^s`,   for `Re s > k + 1`,

with the sum converging there (`summable_rankin_dirichlet`, from the compiled Hecke bound
`‖a_n‖² ≤ M·n^k`).  In the three-dimensional register: `R` is the height-`y` energy readout of
the cusp-form bank, and its Mellin projection is the degree-`2×2` L-readout — the DC channel
(`n = 0`) drops out exactly because the cusp form has no DC component
(`qExpansion_coeff_zero`).  This is the analytic half of the `r = 2` Dirichlet series on its
convergence half-plane, compiled end to end from modularity; the continuation past `Re s = k`
is the named next step (Rankin–Selberg unfolding against the compiled `E(z,s)` continuation).
No RH/GRH.
-/

open UpperHalfPlane Complex Filter MeasureTheory Set Function
open scoped MatrixGroups Real

namespace CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- The cusp-form bank has no DC component. -/
lemma qExpansion_coeff_zero_cusp (f : CuspForm 𝒮ℒ k) : (qExpansion 1 f).coeff 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos one_mem_strictPeriods_SL

/-- The smoothed second-moment series is summable at every positive height. -/
lemma summable_rankin_terms (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℕ =>
      ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * t)) := by
  obtain ⟨M, hM0, hM⟩ := hecke_coeff_sq_bound f
  have hr : ‖Real.exp (-(4 * π * t))‖ < 1 := by
    rw [Real.norm_eq_abs, Real.abs_exp]
    apply Real.exp_lt_one_iff.mpr
    have := Real.pi_pos
    nlinarith
  have hgeo : Summable fun n : ℕ => (n : ℝ) ^ k.toNat * Real.exp (-(4 * π * t)) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one k.toNat hr
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hgeo.mul_left M)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [qExpansion_coeff_zero_cusp f]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    exact mul_nonneg hM0 (by positivity)
  · have hb := hM n hn
    have hzk : (n : ℝ) ^ k = (n : ℝ) ^ k.toNat := by
      conv_lhs => rw [← Int.toNat_of_nonneg hk]
      rw [zpow_natCast]
    have hexp : Real.exp (-(4 * π * n * t)) = Real.exp (-(4 * π * t)) ^ n := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * t))
        ≤ M * (n : ℝ) ^ k * Real.exp (-(4 * π * n * t)) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
      _ = M * ((n : ℝ) ^ k.toNat * Real.exp (-(4 * π * t)) ^ n) := by
          rw [hzk, hexp]
          ring

/-- **Convergence of the Rankin–Selberg Dirichlet series** on `Re s > k + 1`, from the
compiled Hecke coefficient bound. -/
lemma summable_rankin_dirichlet (f : CuspForm 𝒮ℒ k) {σ : ℝ} (hσ : (k : ℝ) + 1 < σ) :
    Summable fun n : ℕ =>
      ‖(qExpansion 1 f).coeff n‖ ^ 2 / (4 * π * n) ^ σ := by
  obtain ⟨M, hM0, hM⟩ := hecke_coeff_sq_bound f
  have hsum : Summable fun n : ℕ => (n : ℝ) ^ ((k : ℝ) - σ) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hsum.mul_left (M * ((4 * π) ^ σ)⁻¹))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [qExpansion_coeff_zero_cusp f]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
    exact mul_nonneg (mul_nonneg hM0 (by positivity)) (Real.rpow_nonneg (by norm_num) _)
  · have hb := hM n hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn
    have hden : (0 : ℝ) < (4 * π * n) ^ σ :=
      Real.rpow_pos_of_pos (by positivity) σ
    have h4π : ((4 : ℝ) * π) ^ σ ≠ 0 :=
      (Real.rpow_pos_of_pos (by positivity) σ).ne'
    have hnσ : (n : ℝ) ^ σ ≠ 0 := (Real.rpow_pos_of_pos hnp σ).ne'
    calc ‖(qExpansion 1 f).coeff n‖ ^ 2 / (4 * π * n) ^ σ
        ≤ M * (n : ℝ) ^ k / (4 * π * n) ^ σ := by gcongr
      _ = M * ((4 * π) ^ σ)⁻¹ * (n : ℝ) ^ ((k : ℝ) - σ) := by
          rw [← Real.rpow_intCast (n : ℝ) k,
            Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * π) hnp.le,
            Real.rpow_sub hnp]
          field_simp

/-- **The Mellin identification**: the Mellin transform of the smoothed second moment is the
completed Rankin–Selberg Dirichlet series, `Γ(s)·∑' ‖a_n‖²/(4πn)^s`, for `Re s > k + 1`. -/
theorem rankin_mellin_hasSum (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : (k : ℝ) + 1 < s.re) :
    HasSum (fun n : ℕ => Complex.Gamma s * ((‖(qExpansion 1 f).coeff n‖ ^ 2 : ℝ) : ℂ) /
        ((4 * π * n : ℝ) : ℂ) ^ s)
      (mellin (fun y : ℝ => ((∑' n : ℕ,
        ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y)) : ℝ) : ℂ)) s) := by
  have hk' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hs0 : 0 < s.re := by linarith
  refine hasSum_mellin (fun n => ?_) hs0 (fun t ht => ?_) ?_
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · refine Or.inl ?_
      subst hn
      rw [qExpansion_coeff_zero_cusp f]
      simp
    · refine Or.inr ?_
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
  · have hreal := (summable_rankin_terms f hk (mem_Ioi.mp ht)).hasSum
    have hcast := Complex.hasSum_ofReal.mpr hreal
    convert hcast using 1
    funext n
    rw [← Complex.ofReal_mul]
    norm_cast
    rw [show -(4 * π * (n : ℝ)) * t = -(4 * π * (n : ℝ) * t) by ring]
  · refine ((summable_rankin_dirichlet f hs).congr fun n => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- The tsum form: `mellin R s = Γ(s)·D(s)` on the convergence half-plane. -/
theorem rankin_mellin_eq (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : (k : ℝ) + 1 < s.re) :
    mellin (fun y : ℝ => ((∑' n : ℕ,
        ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y)) : ℝ) : ℂ)) s =
      Complex.Gamma s * ∑' n : ℕ, ((‖(qExpansion 1 f).coeff n‖ ^ 2 : ℝ) : ℂ) /
        ((4 * π * n : ℝ) : ℂ) ^ s := by
  rw [← (rankin_mellin_hasSum f hk hs).tsum_eq]
  simp_rw [mul_div_assoc]
  rw [tsum_mul_left]

end CriticalLinePhasor.HeckeSupBound

#print axioms CriticalLinePhasor.HeckeSupBound.rankin_mellin_hasSum
#print axioms CriticalLinePhasor.HeckeSupBound.rankin_mellin_eq
