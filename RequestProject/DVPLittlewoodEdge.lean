import RequestProject.DVPEulerMaclaurin
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.PSeriesComplex

/-!
# Littlewood box: the right/tail edge control

For `σ = Re s ≥ 2` the fiber is within `3·2^{−σ} ≤ 3/4` of its DC value `1`,
so `log‖ζ‖` is two-sided controlled by `12·2^{−σ}`.  This single pointwise
bound serves BOTH tail edges of Littlewood's box: the right vertical edge
(`∫₀ᵀ log|ζ(σ₀+it)| dt ≤ 12T·2^{−σ₀} → 0` as `σ₀ → ∞`) and the top edge's
`σ ≥ 2` tail (`∫₂^∞ 12·2^{−σ} dσ = O(1)`).
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The fiber tail at the edge**: `‖ζ(z) − 1‖ ≤ 2^{−σ} + 2^{1−σ}/(σ−1)`
for `σ = Re z > 1` — the AC content beyond the DC term `1`, bounded by the
compiled Hurwitz bracket. -/
theorem zeta_sub_one_norm_le {z : ℂ} (hz : 1 < z.re) :
    ‖riemannZeta z - 1‖
      ≤ (2:ℝ) ^ (-z.re) + (2:ℝ) ^ (1 - z.re) / (z.re - 1) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
    linarith
  have hsum : Summable (fun n : ℕ => 1 / ((n:ℂ)) ^ z) :=
    Complex.summable_one_div_nat_cpow.mpr hz
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hval : (∑ i ∈ Finset.range 2, 1 / ((i:ℂ)) ^ z) = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    rw [Nat.cast_zero, zero_cpow hz0, Nat.cast_one, one_cpow]
    norm_num
  have hζ : riemannZeta z - 1 = ∑' n : ℕ, 1 / (((n + 2 : ℕ)):ℂ) ^ z := by
    rw [zeta_eq_tsum_one_div_nat_cpow hz, ← hsplit, hval]
    ring
  have hnorm_eq : ∀ n : ℕ,
      ‖1 / (((n + 2 : ℕ)):ℂ) ^ z‖ = (((n + 2 : ℕ)):ℝ) ^ (-z.re) := by
    intro n
    rw [norm_div, norm_one,
      Complex.norm_natCast_cpow_of_pos (by omega : 0 < n + 2)]
    rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ ((n + 2 : ℕ):ℝ)), one_div]
  have hnorms : Summable (fun n : ℕ => (((n + 2 : ℕ)):ℝ) ^ (-z.re)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-z.re)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact hbase.comp_injective (fun a b hab => by omega)
  have hsummable_norm :
      Summable (fun n : ℕ => ‖1 / (((n + 2 : ℕ)):ℂ) ^ z‖) :=
    hnorms.congr (fun n => (hnorm_eq n).symm)
  have htail : (∑' n : ℕ, (((n + 2 : ℕ)):ℝ) ^ (-z.re))
      ≤ (2:ℝ) ^ (-z.re) + (2:ℝ) ^ (1 - z.re) / (z.re - 1) := by
    have hpeel := hnorms.tsum_eq_zero_add
    have hbr := (tsum_rpow_tail_bracket (c := 0) (N := 3) (p := z.re) hz
      (by norm_num)).2
    have hshift : (∑' n : ℕ, (((n + 1 + 2 : ℕ)):ℝ) ^ (-z.re))
        = ∑' k : ℕ, ((((3:ℕ)):ℝ) + (k:ℝ) + 0) ^ (-z.re) := by
      apply tsum_congr
      intro k
      congr 1
      push_cast
      ring
    have hzero : (((0 + 2 : ℕ)):ℝ) ^ (-z.re) = (2:ℝ) ^ (-z.re) := by
      norm_num
    have hrhs : (((3:ℕ)):ℝ) + (0:ℝ) - 1 = 2 := by norm_num
    rw [hrhs] at hbr
    rw [hpeel, hzero, hshift]
    linarith [hbr]
  calc ‖riemannZeta z - 1‖
      = ‖∑' n : ℕ, 1 / (((n + 2 : ℕ)):ℂ) ^ z‖ := by rw [hζ]
    _ ≤ ∑' n : ℕ, ‖1 / (((n + 2 : ℕ)):ℂ) ^ z‖ :=
        norm_tsum_le_tsum_norm hsummable_norm
    _ = ∑' n : ℕ, (((n + 2 : ℕ)):ℝ) ^ (-z.re) := tsum_congr hnorm_eq
    _ ≤ (2:ℝ) ^ (-z.re) + (2:ℝ) ^ (1 - z.re) / (z.re - 1) := htail

/-- **The edge log control, two-sided**: `|log‖ζ(z)‖| ≤ 12·2^{−σ}` for
`σ = Re z ≥ 2`.  The single instrument for both tail edges of the box. -/
theorem abs_log_norm_zeta_edge {z : ℂ} (hz : 2 ≤ z.re) :
    |Real.log ‖riemannZeta z‖| ≤ 12 * (2:ℝ) ^ (-z.re) := by
  have hz1 : 1 < z.re := by linarith
  have hε := zeta_sub_one_norm_le hz1
  set ε : ℝ := (2:ℝ) ^ (-z.re) + (2:ℝ) ^ (1 - z.re) / (z.re - 1) with hεdef
  have hrp : (0:ℝ) < (2:ℝ) ^ (-z.re) := by positivity
  have hε0 : (0:ℝ) ≤ ε := by
    rw [hεdef]
    have h2 : (0:ℝ) ≤ (2:ℝ) ^ (1 - z.re) / (z.re - 1) :=
      div_nonneg (by positivity) (by linarith)
    linarith
  have h2σ' : (2:ℝ) ^ (1 - z.re) = 2 * (2:ℝ) ^ (-z.re) := by
    rw [show (1 - z.re) = 1 + (-z.re) by ring,
      Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]
  have hεle : ε ≤ 3 * (2:ℝ) ^ (-z.re) := by
    rw [hεdef, h2σ']
    have hfrac : 2 * (2:ℝ) ^ (-z.re) / (z.re - 1) ≤ 2 * (2:ℝ) ^ (-z.re) :=
      div_le_self (by positivity) (by linarith)
    linarith
  have hquarter : (2:ℝ) ^ (-z.re) ≤ 1/4 := by
    have hmono : (2:ℝ) ^ (-z.re) ≤ (2:ℝ) ^ (-(2:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h4 : (2:ℝ) ^ (-(2:ℝ)) = 1/4 := by
      rw [show (-(2:ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    exact hmono.trans h4.le
  have hε34 : ε ≤ 3/4 := by
    have h3 := mul_le_mul_of_nonneg_left hquarter (by norm_num : (0:ℝ) ≤ 3)
    linarith
  have hζlow : 1 - ε ≤ ‖riemannZeta z‖ := by
    have h := norm_sub_norm_le (1:ℂ) (1 - riemannZeta z)
    have heq : (1:ℂ) - (1 - riemannZeta z) = riemannZeta z := by ring
    rw [heq, norm_one, norm_sub_rev] at h
    linarith
  have hζpos : (0:ℝ) < ‖riemannZeta z‖ := by linarith
  have hζup : ‖riemannZeta z‖ ≤ 1 + ε := by
    have heq : riemannZeta z = 1 + (riemannZeta z - 1) := by ring
    calc ‖riemannZeta z‖ = ‖(1:ℂ) + (riemannZeta z - 1)‖ := by rw [← heq]
      _ ≤ ‖(1:ℂ)‖ + ‖riemannZeta z - 1‖ := norm_add_le _ _
      _ ≤ 1 + ε := by
          rw [norm_one]
          linarith
  have hup : Real.log ‖riemannZeta z‖ ≤ ε := by
    have h := Real.log_le_sub_one_of_pos hζpos
    linarith
  have hlow : -Real.log ‖riemannZeta z‖ ≤ 4 * ε := by
    have hinvpos : (0:ℝ) < ‖riemannZeta z‖⁻¹ := by positivity
    have hloginv := Real.log_le_sub_one_of_pos hinvpos
    rw [Real.log_inv] at hloginv
    have hkey : ‖riemannZeta z‖⁻¹ - 1 ≤ 4 * ε := by
      by_contra hcon
      push_neg at hcon
      have hgt : 1 + 4 * ε < ‖riemannZeta z‖⁻¹ := by linarith
      have hmul := mul_lt_mul_of_pos_left hgt hζpos
      rw [mul_inv_cancel₀ (ne_of_gt hζpos)] at hmul
      nlinarith [mul_le_mul_of_nonneg_right hζlow
        (by linarith : (0:ℝ) ≤ 1 + 4 * ε)]
    linarith
  have habs : |Real.log ‖riemannZeta z‖| ≤ 4 * ε := by
    rw [abs_le]
    constructor
    · linarith
    · linarith
  calc |Real.log ‖riemannZeta z‖| ≤ 4 * ε := habs
    _ ≤ 4 * (3 * (2:ℝ) ^ (-z.re)) :=
        mul_le_mul_of_nonneg_left hεle (by norm_num)
    _ = 12 * (2:ℝ) ^ (-z.re) := by ring

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.zeta_sub_one_norm_le
#print axioms CriticalLinePhasor.DVP.abs_log_norm_zeta_edge
end AxiomAudit
