import RequestProject.DVPExhaustion58

/-!
# The station sign transfer

Because the Hardy detector is a REAL rotation of `ζ` on the line, its
sign at a station is readable through ANY rational proxy phase `φ` with
`|φ − θ(t)| < π/2`:

`sign hardyG t = sign (cos φ·Re ζ − sin φ·Im ζ)`.

The tolerance is `π/2` — over a radian of slack — so the compiled
`θ(30)` anchor plus the `10(1/T₁ − 1/T)` increment window covers every
station in `[11, 58]` with room to spare.  No `|Γ|` value and no tight
`θ` decimal is ever needed.
-/

open Complex
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The imaginary-part companion of the phase identity. -/
theorem hardyG_im_phase (t : ℝ) :
    (completedRiemannZeta (line t)).im
      = Real.exp ((gammaLog (line t)).re)
        * (Real.sin (theta t) * (riemannZeta (line t)).re
          + Real.cos (theta t) * (riemannZeta (line t)).im) := by
  have hline0 : line t ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [line_re] at this
    simp at this
  have hrhp : line t ∈ rightHalfPlane := by
    simp [rightHalfPlane, line_re]
  have hprod : completedRiemannZeta (line t)
      = Gammaℝ (line t) * riemannZeta (line t) := by
    rw [riemannZeta_def_of_ne_zero hline0]
    have hΓne : Gammaℝ (line t) ≠ 0 :=
      Gammaℝ_ne_zero_of_re_pos (by rw [line_re]; norm_num)
    field_simp
  have hexp : Gammaℝ (line t) = Complex.exp (gammaLog (line t)) :=
    (exp_gammaLog hrhp).symm
  have hgl : gammaLog (line t)
      = ((gammaLog (line t)).re : ℂ) + (theta t : ℝ) * Complex.I := by
    rw [← gammaLog_line_im t]
    exact (Complex.re_add_im _).symm
  rw [hprod, hexp, hgl, Complex.exp_add, ← Complex.ofReal_exp,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_re,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  ring

/-- **The proxy-phase sign transfer.** -/
theorem hardyG_sign_of_proxy {t φ : ℝ}
    (hθ : |φ - theta t| < Real.pi / 2) :
    (0 < Real.cos φ * (riemannZeta (line t)).re
        - Real.sin φ * (riemannZeta (line t)).im → 0 < hardyG t)
    ∧ (Real.cos φ * (riemannZeta (line t)).re
        - Real.sin φ * (riemannZeta (line t)).im < 0 → hardyG t < 0) := by
  set w := riemannZeta (line t) with hwdef
  set θ := theta t with hθdef
  set A : ℝ := Real.cos θ * w.re - Real.sin θ * w.im with hAdef
  set B : ℝ := Real.sin θ * w.re + Real.cos θ * w.im with hBdef
  -- realness kills B
  have hB : B = 0 := by
    have h1 := completedZeta_line_real t
    have h2 := hardyG_im_phase t
    rw [h1] at h2
    have hexp_pos : (0:ℝ) < Real.exp ((gammaLog (line t)).re) :=
      Real.exp_pos _
    have := h2.symm
    rw [hBdef]
    nlinarith [this, hexp_pos]
  -- the rotation identity
  have hrot : Real.cos φ * w.re - Real.sin φ * w.im
      = Real.cos (φ - θ) * A - Real.sin (φ - θ) * B := by
    rw [hAdef, hBdef, Real.cos_sub, Real.sin_sub]
    first
    | linear_combination
        (Real.cos φ * w.re - Real.sin φ * w.im)
          * Real.sin_sq_add_cos_sq θ
    | linear_combination
        (-(Real.cos φ * w.re) + Real.sin φ * w.im)
          * Real.sin_sq_add_cos_sq θ
  have hcos_pos : 0 < Real.cos (φ - θ) := by
    rcases abs_lt.mp hθ with ⟨h1, h2⟩
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> [linarith; linarith]
  have hG : hardyG t = Real.exp ((gammaLog (line t)).re) * A := by
    rw [hardyG_eq_phase, hAdef]
  have hexp_pos : (0:ℝ) < Real.exp ((gammaLog (line t)).re) :=
    Real.exp_pos _
  constructor
  · intro hP
    rw [hrot, hB, mul_zero, sub_zero] at hP
    have hA : 0 < A := by nlinarith [hcos_pos]
    rw [hG]
    exact mul_pos hexp_pos hA
  · intro hP
    rw [hrot, hB, mul_zero, sub_zero] at hP
    have hA : A < 0 := by nlinarith [hcos_pos]
    rw [hG]
    exact mul_neg_of_pos_of_neg hexp_pos hA

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.hardyG_sign_of_proxy
end AxiomAudit
