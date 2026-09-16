import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The identity behind "the averaged seat is a zero-density statement"

RH_LEDGER 759–760.  The seat, after the two-point form collapses, is

  `Re[ξ'/ξ](σ + i t) = Σ_ρ (σ − β_ρ) / |σ + i t − ρ|²`,

so integrating in `t` one zero at a time needs exactly

  **`∫_ℝ a / (a² + x²) dx = π · sign a`.**

Summing that over a window of ordinates turns the averaged seat into
`π [ N(T,2T) − 2 N(σ; T,2T) ]`, i.e. **the averaged seat IS the statement that at most half the
zeros in the window lie to the right of `σ`** — a zero-density statement, unconditionally true for
every fixed `σ > ½` by Ingham.  The pointwise statement is RH.  This file compiles the calculus
step; the number-theoretic content around it is not compiled.

The `sign` is the whole point: a zero to the LEFT of the anchor contributes `+π`, one to the RIGHT
contributes `−π`, and the average is positive exactly when the left ones outnumber the right ones.
-/

namespace CriticalLinePhasor.SeatAverage

open MeasureTheory intervalIntegral

/-- The Poisson mass of a single zero, as a function of its offset from the anchor abscissa. -/
noncomputable def poissonTerm (a x : ℝ) : ℝ := a / (a ^ 2 + x ^ 2)

theorem poissonTerm_nonneg_of_pos {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 ≤ poissonTerm a x := by
  unfold poissonTerm
  have : 0 < a ^ 2 + x ^ 2 := by positivity
  positivity

theorem poissonTerm_nonpos_of_neg {a : ℝ} (ha : a < 0) (x : ℝ) : poissonTerm a x ≤ 0 := by
  unfold poissonTerm
  have h : 0 < a ^ 2 + x ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg a]
  exact div_nonpos_of_nonpos_of_nonneg ha.le h.le

/-- **The averaging identity, one zero at a time.**  A zero at offset `a` from the anchor
abscissa contributes `+π` when it lies to the left (`a > 0`) and `−π` when it lies to the right. -/
theorem integral_poissonTerm {a : ℝ} (ha : a ≠ 0) :
    (∫ x : ℝ, poissonTerm a x) = Real.pi * (a / |a|) := by
  have habs : (0 : ℝ) < |a| := abs_pos.mpr ha
  have key : ∀ x : ℝ, poissonTerm a x = (a / a ^ 2) * (1 + (x / |a|) ^ 2)⁻¹ := by
    intro x
    unfold poissonTerm
    rw [div_pow, sq_abs]
    have h2 : (a : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 ha
    field_simp
  simp_rw [key]
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.Measure.integral_comp_div (fun u : ℝ => (1 + u ^ 2)⁻¹) |a|,
    integral_univ_inv_one_add_sq, smul_eq_mul, abs_abs]
  have h2 : (a : ℝ) ^ 2 = |a| * |a| := by rw [sq, abs_mul_abs_self]
  rw [h2]
  field_simp

/-- Positive when the zero is to the LEFT of the anchor. -/
theorem integral_poissonTerm_pos {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, poissonTerm a x) = Real.pi := by
  rw [integral_poissonTerm (ne_of_gt ha), abs_of_pos ha, div_self (ne_of_gt ha), mul_one]

/-- Negative when the zero is to the RIGHT of the anchor: this is the only way the seat's average
can be pulled down, and it is why the average is a counting statement. -/
theorem integral_poissonTerm_neg {a : ℝ} (ha : a < 0) :
    (∫ x : ℝ, poissonTerm a x) = -Real.pi := by
  rw [integral_poissonTerm (ne_of_lt ha), abs_of_neg ha, div_neg, div_self (ne_of_lt ha)]
  ring

end CriticalLinePhasor.SeatAverage

#print axioms CriticalLinePhasor.SeatAverage.integral_poissonTerm
#print axioms CriticalLinePhasor.SeatAverage.integral_poissonTerm_pos
#print axioms CriticalLinePhasor.SeatAverage.integral_poissonTerm_neg
