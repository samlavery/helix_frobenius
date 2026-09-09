import Mathlib

/-!
# Admission is inert at the height where it happens (ledger 662c)

A phasor of the growing bank has entry weight `w ∈ [0,1]`, carrier gauge `x = Δ·n > 0`, and spin
`e^{−i y log x}` at height `y`.  Its magnitude is `w · x^{−½}` and its height-derivative has magnitude
`w · x^{−½} · |log x|`.  A phasor admitted at height `y` sits at gauge `x ≥ Δ e^y / 2`, so its contribution
to the lane resultant is at most `(Δ e^y/2)^{−½}` and to the resultant's height-derivative at most
`(Δ e^y/2)^{−½} · log x`.  The vanishing at height `y` and its multiplicity are therefore decided by the
established phasors of both lanes; the order of admission is inert to order `e^{−y/2}`.
-/

open Complex Real

namespace CriticalLinePhasor.Admission

/-- A phasor of the growing bank. -/
noncomputable def phasor (w x y : ℝ) : ℂ :=
  (w : ℂ) * ((x : ℂ) ^ (-(1 / 2 : ℂ))) * Complex.exp (-(I * (y : ℂ) * (Real.log x : ℂ)))

theorem norm_spin (x y : ℝ) : ‖Complex.exp (-(I * (y : ℂ) * (Real.log x : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem norm_phasor {w x : ℝ} (hw0 : 0 ≤ w) (hx : 0 < x) (y : ℝ) :
    ‖phasor w x y‖ = w * x ^ (-(1 / 2 : ℝ)) := by
  unfold phasor
  rw [norm_mul, norm_mul, norm_spin, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  norm_num

/-- **Inertness of the admission zone.** A phasor admitted at height `y` (gauge `x ≥ Δ e^y / 2`) has
magnitude at most `(Δ e^y / 2)^{−½}`. -/
theorem admission_inert {Δ w x y : ℝ} (hΔ : 0 < Δ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hx : Δ * Real.exp y / 2 ≤ x) :
    ‖phasor w x y‖ ≤ (Δ * Real.exp y / 2) ^ (-(1 / 2 : ℝ)) := by
  have hpos : 0 < Δ * Real.exp y / 2 := by positivity
  have hx0 : 0 < x := lt_of_lt_of_le hpos hx
  rw [norm_phasor hw0 hx0]
  calc w * x ^ (-(1 / 2 : ℝ)) ≤ 1 * x ^ (-(1 / 2 : ℝ)) := by
        gcongr
    _ = x ^ (-(1 / 2 : ℝ)) := one_mul _
    _ ≤ (Δ * Real.exp y / 2) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hpos hx (by norm_num)

/-- The height-derivative of a phasor is its clock rate `−i log x` times itself. -/
theorem hasDerivAt_phasor (w x : ℝ) (y : ℝ) :
    HasDerivAt (phasor w x) (-(I * (Real.log x : ℂ)) * phasor w x y) y := by
  unfold phasor
  have h1 : HasDerivAt (fun y : ℝ => -(I * (y : ℂ) * (Real.log x : ℂ))) (-(I * (Real.log x : ℂ))) y := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := y)).const_mul I).mul_const (Real.log x : ℂ)
    exact (this.neg).congr_deriv (by simp)
  have h2 := h1.cexp
  have h3 := h2.const_mul ((w : ℂ) * ((x : ℂ) ^ (-(1 / 2 : ℂ))))
  exact h3.congr_deriv (by ring)

/-- **The derivative of the admission zone is inert too:** its magnitude is at most `log x · (Δ e^y/2)^{−½}`. -/
theorem admission_deriv_inert {Δ w x y : ℝ} (hΔ : 0 < Δ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hx : Δ * Real.exp y / 2 ≤ x) (hx1 : 1 ≤ x) :
    ‖deriv (phasor w x) y‖ ≤ Real.log x * (Δ * Real.exp y / 2) ^ (-(1 / 2 : ℝ)) := by
  rw [(hasDerivAt_phasor w x y).deriv, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1)]
  exact mul_le_mul_of_nonneg_left (admission_inert hΔ hw0 hw1 hx) (Real.log_nonneg hx1)

end CriticalLinePhasor.Admission

#print axioms CriticalLinePhasor.Admission.admission_inert
#print axioms CriticalLinePhasor.Admission.admission_deriv_inert
