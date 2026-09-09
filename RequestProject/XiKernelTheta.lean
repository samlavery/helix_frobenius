import RequestProject.XiKernelMellin

/-!
# T1a, scaffolding for steps 3–4: the theta functional equation for `Ψ`, and `Ψ` as a holomorphic
# restriction (ledger 668)

* `theta_functional_equation`: `θ(x) = x^{−½} θ(1/x)` for `x > 0` (Mathlib's `evenKernel_functional_equation`
  at `a = 0`).
* `Psi_reflect`: `Ψ(u) = e^{−u} Ψ(−u) + (e^{−u} − 1)/2` — the reflection that gives the `u → −∞` behaviour
  from the `u → +∞` one, and makes the kernel `K = e^{u/2}(Ψ″ + Ψ′)` even.
* `thetaExp w = jacobiTheta₂ 0 (I e^{2w})`, holomorphic on the strip `|Im w| < π/4`, with
  `thetaExp u = θ(e^{2u})` on the real axis; hence `PsiC w = (thetaExp w − 1)/2` is holomorphic there,
  `PsiC u = Ψ(u)` for real `u`, and `Ψ` has derivatives of every order as the restriction of `PsiC`
  (`hasDerivAt_PsiC_ofReal`, `differentiableOn_deriv_PsiC`).
-/

open Complex HurwitzZeta Set

namespace CriticalLinePhasor.XiKernel

/-- `θ(x) = x^{−½} θ(1/x)` for `x > 0`. -/
theorem theta_functional_equation {x : ℝ} (hx : 0 < x) :
    evenKernel 0 x = x ^ (-(1 / 2 : ℝ)) * evenKernel 0 (1 / x) := by
  rw [evenKernel_functional_equation 0 x, Real.rpow_neg hx.le, one_div,
    congrFun evenKernel_eq_cosKernel_of_zero (1 / x)]

/-- `(e^{2u})^{−½} = e^{−u}`. -/
theorem exp_two_mul_rpow_neg_half (u : ℝ) :
    Real.exp (2 * u) ^ (-(1 / 2 : ℝ)) = Real.exp (-u) := by
  rw [← Real.exp_mul]; congr 1; ring

/-- **Reflection of `Ψ`:** `Ψ(u) = e^{−u} Ψ(−u) + (e^{−u} − 1)/2`. -/
theorem Psi_reflect (u : ℝ) :
    Psi u = Real.exp (-u) * Psi (-u) + (Real.exp (-u) - 1) / 2 := by
  unfold Psi
  rw [theta_functional_equation (Real.exp_pos (2 * u)), exp_two_mul_rpow_neg_half,
    one_div, ← Real.exp_neg, show -(2 * u) = 2 * (-u) by ring]
  ring

/-- The holomorphic extension `thetaExp w = jacobiTheta₂ 0 (I e^{2w})`. -/
noncomputable def thetaExp (w : ℂ) : ℂ := jacobiTheta₂ 0 (I * Complex.exp (2 * w))

/-- On the real axis, `thetaExp u = θ(e^{2u})`. -/
theorem thetaExp_ofReal (u : ℝ) :
    thetaExp u = ((evenKernel 0 (Real.exp (2 * u)) : ℝ) : ℂ) := by
  have h := evenKernel_def 0 (Real.exp (2 * u))
  simp only [QuotientAddGroup.mk_zero, Complex.ofReal_zero, zero_pow two_ne_zero, mul_zero,
    zero_mul, Complex.exp_zero, one_mul] at h
  rw [h, thetaExp, Complex.ofReal_exp]
  push_cast
  ring_nf

/-- The strip of holomorphy `|Im w| < π/4`. -/
def strip : Set ℂ := {w | |w.im| < Real.pi / 4}

theorem strip_isOpen : IsOpen strip := by
  have : strip = (fun w : ℂ => |w.im|) ⁻¹' Iio (Real.pi / 4) := rfl
  rw [this]
  exact isOpen_Iio.preimage (continuous_abs.comp Complex.continuous_im)

theorem ofReal_mem_strip (u : ℝ) : (u : ℂ) ∈ strip := by
  simp [strip, Real.pi_pos]

/-- On the strip, `Im (I e^{2w}) = e^{2 Re w} cos (2 Im w) > 0`. -/
theorem im_I_mul_exp_pos {w : ℂ} (hw : w ∈ strip) : 0 < (I * Complex.exp (2 * w)).im := by
  rw [Complex.I_mul_im, Complex.exp_re]
  have hcos : 0 < Real.cos (2 * w).im := by
    apply Real.cos_pos_of_mem_Ioo
    have h := hw
    change |w.im| < Real.pi / 4 at h
    rw [abs_lt] at h
    simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero]
    constructor <;> linarith
  exact mul_pos (Real.exp_pos _) hcos

theorem differentiableOn_thetaExp : DifferentiableOn ℂ thetaExp strip := by
  intro w hw
  have hτ := im_I_mul_exp_pos hw
  have h1 : DifferentiableAt ℂ (fun w : ℂ => I * Complex.exp (2 * w)) w :=
    ((differentiableAt_const _).mul differentiableAt_id).cexp.const_mul _
  exact ((differentiableAt_jacobiTheta₂_snd 0 hτ).comp w h1).differentiableWithinAt

/-- `PsiC w = (thetaExp w − 1)/2`, with `PsiC u = Ψ(u)` on the axis. -/
noncomputable def PsiC (w : ℂ) : ℂ := (thetaExp w - 1) / 2

theorem PsiC_ofReal (u : ℝ) : PsiC u = (Psi u : ℂ) := by
  rw [PsiC, thetaExp_ofReal, Psi]; push_cast; ring

theorem differentiableOn_PsiC : DifferentiableOn ℂ PsiC strip :=
  (differentiableOn_thetaExp.sub (differentiableOn_const _)).div_const _

theorem analyticOnNhd_PsiC : AnalyticOnNhd ℂ PsiC strip :=
  differentiableOn_PsiC.analyticOnNhd strip_isOpen

/-- Every derivative of `PsiC` is again analytic, hence holomorphic, on the strip. -/
theorem analyticOnNhd_iteratedDeriv_PsiC (n : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv n PsiC) strip := by
  induction n with
  | zero => simpa [iteratedDeriv_zero] using analyticOnNhd_PsiC
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem differentiableOn_iteratedDeriv_PsiC (n : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv n PsiC) strip :=
  (analyticOnNhd_iteratedDeriv_PsiC n).differentiableOn

theorem differentiableOn_deriv_PsiC : DifferentiableOn ℂ (deriv PsiC) strip :=
  analyticOnNhd_PsiC.deriv.differentiableOn

/-- `Ψ` as a function on the real axis is differentiable, with derivative the restriction of `deriv PsiC`. -/
theorem hasDerivAt_PsiC_ofReal (u : ℝ) :
    HasDerivAt (fun y : ℝ => PsiC y) (deriv PsiC u) u :=
  ((differentiableOn_PsiC.differentiableAt (strip_isOpen.mem_nhds (ofReal_mem_strip u))).hasDerivAt).comp_ofReal

theorem hasDerivAt_deriv_PsiC_ofReal (u : ℝ) :
    HasDerivAt (fun y : ℝ => deriv PsiC y) (deriv (deriv PsiC) u) u :=
  ((differentiableOn_deriv_PsiC.differentiableAt
    (strip_isOpen.mem_nhds (ofReal_mem_strip u))).hasDerivAt).comp_ofReal

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.Psi_reflect
#print axioms CriticalLinePhasor.XiKernel.thetaExp_ofReal
#print axioms CriticalLinePhasor.XiKernel.hasDerivAt_deriv_PsiC_ofReal
