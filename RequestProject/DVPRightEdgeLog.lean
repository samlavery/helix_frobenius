import RequestProject.DVPBoxCollapse
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The right edge at `σ ≥ 2`: full complex log bounded by 2

The contour's right edge sits at `σ = 2`, where `‖ζ − 1‖ ≤ 3/4` (394 chain)
— inside the unit disk about `1`, so the principal log is defined and
`‖Log ζ‖ ≤ ‖w‖²(1−‖w‖)⁻¹/2 + ‖w‖ ≤ 15/8 ≤ 2`.  This is the modulus AND
argument control the right-edge box and the lift-principality argument
consume (the 395-era bound reached only `σ ≥ 3`).
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The `σ ≥ 2` complex-log bound**: `‖Log ζ(z)‖ ≤ 2` for `Re z ≥ 2`. -/
theorem norm_log_zeta_ge_two {z : ℂ} (hz : 2 ≤ z.re) :
    ‖Complex.log (riemannZeta z)‖ ≤ 2 := by
  have hw := zeta_sub_one_norm_le (by linarith : 1 < z.re)
  have h1 : (2:ℝ)^(-z.re) ≤ 1/4 := by
    have hmono : (2:ℝ)^(-z.re) ≤ (2:ℝ)^(-(2:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h4 : (2:ℝ)^(-(2:ℝ)) = 1/4 := by
      rw [show (-(2:ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    exact hmono.trans h4.le
  have h2 : (2:ℝ)^(1 - z.re) / (z.re - 1) ≤ 1/2 := by
    have h2σ : (2:ℝ)^(1-z.re) ≤ 1/2 := by
      have hmono : (2:ℝ)^(1-z.re) ≤ (2:ℝ)^(-(1:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have hhalf : (2:ℝ)^(-(1:ℝ)) = 1/2 := by
        rw [show (-(1:ℝ)) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        norm_num
      exact hmono.trans hhalf.le
    calc (2:ℝ)^(1 - z.re) / (z.re - 1) ≤ (2:ℝ)^(1 - z.re) :=
          div_le_self (by positivity) (by linarith)
      _ ≤ 1/2 := h2σ
  have hε : ‖riemannZeta z - 1‖ ≤ 3/4 := by linarith [hw]
  have hlt : ‖riemannZeta z - 1‖ < 1 := by linarith
  have heq : riemannZeta z = 1 + (riemannZeta z - 1) := by ring
  have hbound := Complex.norm_log_one_add_le hlt
  have hnn : (0:ℝ) ≤ ‖riemannZeta z - 1‖ := norm_nonneg _
  have hinv : (1 - ‖riemannZeta z - 1‖)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc ‖Complex.log (riemannZeta z)‖
      = ‖Complex.log (1 + (riemannZeta z - 1))‖ := by rw [← heq]
    _ ≤ ‖riemannZeta z - 1‖ ^ 2 * (1 - ‖riemannZeta z - 1‖)⁻¹ / 2
        + ‖riemannZeta z - 1‖ := hbound
    _ ≤ 2 := by nlinarith [hε, hnn, hinv, sq_nonneg ‖riemannZeta z - 1‖]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.norm_log_zeta_ge_two
end AxiomAudit
