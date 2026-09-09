import RequestProject.XiKernelEven

/-!
# T1a, bounds for step 3: super-exponential decay of `Ψ, Ψ′, Ψ″` at `+∞` (ledger 670)

On the sub-strip `|Im w| ≤ π/16` with `Re w ≥ 0`, `Im(I e^{2w}) = e^{2 Re w} cos(2 Im w) ≥ (9/10) e^{2 Re w}`, and
Mathlib's tail bound `‖θ(τ) − 1‖ ≤ 2 e^{−π Im τ}/(1 − e^{−π Im τ})` gives
  `‖Ψ(w)‖ ≤ 2 · exp(−(5/2) · e^{2 Re w})`                                        (`PsiC_bound`).
Cauchy's estimate on discs of radius `R = π/32` transfers this to `Ψ′` on `{|Im w| ≤ R, Re w ≥ R}` and to `Ψ″`
on the axis for `y ≥ 2R` (`Psi1_bound`, `Psi2_bound`), with the same super-exponential rate shifted by `R`.
These are the decay inputs of the two integrations by parts and of the entire-ness of the flow stages.
-/

open Complex HurwitzZeta Set Metric

namespace CriticalLinePhasor.XiKernel

/-- `cos(2 Im w) ≥ 9/10` when `|Im w| ≤ π/16`. -/
theorem cos_two_im_ge {w : ℂ} (hw : |w.im| ≤ Real.pi / 16) :
    9 / 10 ≤ Real.cos (2 * w.im) := by
  have h1 := Real.one_sub_sq_div_two_le_cos (x := 2 * w.im)
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hsq : (2 * w.im) ^ 2 ≤ (Real.pi / 8) ^ 2 := by
    rw [← sq_abs (2 * w.im), abs_mul, abs_two]
    have : 2 * |w.im| ≤ Real.pi / 8 := by linarith
    exact pow_le_pow_left₀ (by positivity) this 2
  nlinarith [Real.pi_pos]

/-- `Im (I e^{2w}) ≥ (9/10) e^{2 Re w}` on the sub-strip. -/
theorem im_I_mul_exp_ge {w : ℂ} (hw : |w.im| ≤ Real.pi / 16) :
    9 / 10 * Real.exp (2 * w.re) ≤ (I * Complex.exp (2 * w)).im := by
  rw [Complex.I_mul_im, Complex.exp_re]
  have h2re : (2 * w).re = 2 * w.re := by simp
  have h2im : (2 * w).im = 2 * w.im := by simp
  rw [h2re, h2im]
  have := cos_two_im_ge hw
  have := Real.exp_pos (2 * w.re)
  nlinarith

/-- **The bound on `Ψ`:** `‖Ψ(w)‖ ≤ 2 exp(−(5/2) e^{2 Re w})` for `|Im w| ≤ π/16`, `Re w ≥ 0`. -/
theorem PsiC_bound {w : ℂ} (hw : |w.im| ≤ Real.pi / 16) (hre : 0 ≤ w.re) :
    ‖PsiC w‖ ≤ 2 * Real.exp (-(5 / 2) * Real.exp (2 * w.re)) := by
  set τ := I * Complex.exp (2 * w) with hτ
  have hT : 9 / 10 * Real.exp (2 * w.re) ≤ τ.im := im_I_mul_exp_ge hw
  have hX : 1 ≤ Real.exp (2 * w.re) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have hTpos : 0 < τ.im := by linarith
  have hθ := norm_jacobiTheta_sub_one_le hTpos
  rw [jacobiTheta_eq_jacobiTheta₂] at hθ
  -- e^{−π τ.im} ≤ e^{−2.7 e^{2 Re w}} ≤ e^{−2.7} ≤ 1/3.7
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hexp_small : Real.exp (-Real.pi * τ.im) ≤ 1 / 4 := by
    have h1 : Real.pi * τ.im ≥ 2.7 := by nlinarith
    have h2 : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-2.7) := Real.exp_le_exp.mpr (by linarith)
    have h3 : 1 + 2.7 + (2.7 : ℝ) ^ 2 / 2 ≤ Real.exp 2.7 :=
      Real.quadratic_le_exp_of_nonneg (by norm_num)
    have h4 : Real.exp (-2.7) = (Real.exp 2.7)⁻¹ := by rw [Real.exp_neg]
    rw [h4] at h2
    calc Real.exp (-Real.pi * τ.im) ≤ (Real.exp 2.7)⁻¹ := h2
      _ ≤ 1 / 4 := by
          rw [one_div]; exact inv_anti₀ (by norm_num) (by norm_num at h3; linarith)
  have hden : 1 - Real.exp (-Real.pi * τ.im) ≥ 3 / 4 := by linarith
  have hθ' : ‖jacobiTheta₂ 0 τ - 1‖ ≤ 3 * Real.exp (-Real.pi * τ.im) := by
    calc ‖jacobiTheta₂ 0 τ - 1‖ ≤ 2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) := hθ
      _ ≤ 3 * Real.exp (-Real.pi * τ.im) := by
          gcongr
          rw [div_le_iff₀ (by linarith)]; linarith
  have hrate : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-(5 / 2) * Real.exp (2 * w.re)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.exp_pos (2 * w.re)]
  have hPsi : ‖PsiC w‖ = ‖jacobiTheta₂ 0 τ - 1‖ / 2 := by
    rw [PsiC, thetaExp, norm_div, Complex.norm_ofNat]
  rw [hPsi]
  calc ‖jacobiTheta₂ 0 τ - 1‖ / 2 ≤ 3 * Real.exp (-Real.pi * τ.im) / 2 := by gcongr
    _ ≤ 3 * Real.exp (-(5 / 2) * Real.exp (2 * w.re)) / 2 := by gcongr
    _ ≤ 2 * Real.exp (-(5 / 2) * Real.exp (2 * w.re)) := by
        have := Real.exp_pos (-(5 / 2) * Real.exp (2 * w.re)); linarith

/-- The Cauchy radius `R = π/32`. -/
noncomputable def Rc : ℝ := Real.pi / 32

theorem Rc_pos : 0 < Rc := by unfold Rc; positivity

/-- Closed discs of radius `R` around points with `|Im| ≤ R` stay in the sub-strip `|Im| ≤ π/16 ⊂ strip`. -/
theorem closedBall_subset_strip {c : ℂ} (hc : |c.im| ≤ Rc) : closedBall c Rc ⊆ strip := by
  intro w hw
  rw [mem_closedBall, Complex.dist_eq] at hw
  have him : |w.im - c.im| ≤ ‖w - c‖ := by
    have := Complex.abs_im_le_norm (w - c); simpa using this
  change |w.im| < Real.pi / 4
  have hpi : 0 < Real.pi := Real.pi_pos
  calc |w.im| = |(w.im - c.im) + c.im| := by ring_nf
    _ ≤ |w.im - c.im| + |c.im| := abs_add_le _ _
    _ ≤ Rc + Rc := by gcongr; exact him.trans hw
    _ < Real.pi / 4 := by unfold Rc; linarith

theorem sphere_im_le {c w : ℂ} (hc : |c.im| ≤ Rc) (hw : w ∈ sphere c Rc) : |w.im| ≤ Real.pi / 16 := by
  rw [mem_sphere, Complex.dist_eq] at hw
  have him : |w.im - c.im| ≤ ‖w - c‖ := by
    have := Complex.abs_im_le_norm (w - c); simpa using this
  calc |w.im| = |(w.im - c.im) + c.im| := by ring_nf
    _ ≤ |w.im - c.im| + |c.im| := abs_add_le _ _
    _ ≤ Rc + Rc := by gcongr; exact him.trans hw.le
    _ = Real.pi / 16 := by unfold Rc; ring

theorem sphere_re_ge {c w : ℂ} (hw : w ∈ sphere c Rc) : c.re - Rc ≤ w.re := by
  rw [mem_sphere, Complex.dist_eq] at hw
  have := Complex.abs_re_le_norm (w - c)
  rw [Complex.sub_re] at this
  have := (abs_le.mp (this.trans hw.le)).1
  linarith

/-- **Cauchy transfer to `Ψ′`:** on `{|Im w| ≤ R, Re w ≥ R}`, `‖Ψ′(w)‖ ≤ (2/R) exp(−(5/2) e^{2(Re w − R)})`. -/
theorem Psi1_bound_strip {w : ℂ} (hw : |w.im| ≤ Rc) (hre : Rc ≤ w.re) :
    ‖deriv PsiC w‖ ≤ 2 / Rc * Real.exp (-(5 / 2) * Real.exp (2 * (w.re - Rc))) := by
  have hd : DiffContOnCl ℂ PsiC (ball w Rc) :=
    differentiableOn_PsiC.diffContOnCl_ball (closedBall_subset_strip hw)
  have hC : ∀ z ∈ sphere w Rc, ‖PsiC z‖ ≤ 2 * Real.exp (-(5 / 2) * Real.exp (2 * (w.re - Rc))) := by
    intro z hz
    have h1 := PsiC_bound (sphere_im_le hw hz) (by linarith [sphere_re_ge hz])
    have hre' : Real.exp (2 * (w.re - Rc)) ≤ Real.exp (2 * z.re) :=
      Real.exp_le_exp.mpr (by linarith [sphere_re_ge hz])
    have h2 : Real.exp (-(5 / 2) * Real.exp (2 * z.re))
        ≤ Real.exp (-(5 / 2) * Real.exp (2 * (w.re - Rc))) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le Rc_pos hd hC
  calc ‖deriv PsiC w‖ ≤ 2 * Real.exp (-(5 / 2) * Real.exp (2 * (w.re - Rc))) / Rc := this
    _ = 2 / Rc * Real.exp (-(5 / 2) * Real.exp (2 * (w.re - Rc))) := by ring

/-- **Cauchy transfer to `Ψ″` on the axis:** for `y ≥ 2R`, `‖Ψ″(y)‖ ≤ (2/R²) exp(−(5/2) e^{2(y − 2R)})`. -/
theorem Psi2_bound {y : ℝ} (hy : 2 * Rc ≤ y) :
    ‖deriv (deriv PsiC) y‖ ≤ 2 / Rc ^ 2 * Real.exp (-(5 / 2) * Real.exp (2 * (y - 2 * Rc))) := by
  have hc : |(y : ℂ).im| ≤ Rc := by simp [Rc_pos.le]
  have hd : DiffContOnCl ℂ (deriv PsiC) (ball (y : ℂ) Rc) :=
    differentiableOn_deriv_PsiC.diffContOnCl_ball (closedBall_subset_strip hc)
  have hC : ∀ z ∈ sphere (y : ℂ) Rc,
      ‖deriv PsiC z‖ ≤ 2 / Rc * Real.exp (-(5 / 2) * Real.exp (2 * (y - 2 * Rc))) := by
    intro z hz
    have hzim : |z.im| ≤ Rc := by
      rw [mem_sphere, Complex.dist_eq] at hz
      have := Complex.abs_im_le_norm (z - y)
      simpa [hz] using this
    have hzre : Rc ≤ z.re := by
      have := sphere_re_ge hz; simp at this; linarith
    have h1 := Psi1_bound_strip hzim hzre
    have hre' : Real.exp (2 * (y - 2 * Rc)) ≤ Real.exp (2 * (z.re - Rc)) := by
      apply Real.exp_le_exp.mpr
      have := sphere_re_ge hz; simp at this; linarith
    have h2 : Real.exp (-(5 / 2) * Real.exp (2 * (z.re - Rc)))
        ≤ Real.exp (-(5 / 2) * Real.exp (2 * (y - 2 * Rc))) :=
      Real.exp_le_exp.mpr (by linarith)
    have hR : 0 < 2 / Rc := by have := Rc_pos; positivity
    calc ‖deriv PsiC z‖ ≤ 2 / Rc * Real.exp (-(5 / 2) * Real.exp (2 * (z.re - Rc))) := h1
      _ ≤ 2 / Rc * Real.exp (-(5 / 2) * Real.exp (2 * (y - 2 * Rc))) :=
          mul_le_mul_of_nonneg_left h2 hR.le
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le Rc_pos hd hC
  calc ‖deriv (deriv PsiC) y‖
      ≤ 2 / Rc * Real.exp (-(5 / 2) * Real.exp (2 * (y - 2 * Rc))) / Rc := this
    _ = 2 / Rc ^ 2 * Real.exp (-(5 / 2) * Real.exp (2 * (y - 2 * Rc))) := by
        field_simp

/-- `Ψ′` on the axis for `y ≥ R`. -/
theorem Psi1_bound {y : ℝ} (hy : Rc ≤ y) :
    ‖deriv PsiC y‖ ≤ 2 / Rc * Real.exp (-(5 / 2) * Real.exp (2 * (y - Rc))) := by
  have := Psi1_bound_strip (w := (y : ℂ)) (by simp [Rc_pos.le]) (by simpa using hy)
  simpa using this

/-- `Ψ` on the axis for `y ≥ 0`. -/
theorem Psi0_bound {y : ℝ} (hy : 0 ≤ y) :
    ‖PsiC y‖ ≤ 2 * Real.exp (-(5 / 2) * Real.exp (2 * y)) := by
  have := PsiC_bound (w := (y : ℂ)) (by rw [Complex.ofReal_im, abs_zero]; positivity)
    (by simpa using hy)
  simpa using this

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.PsiC_bound
#print axioms CriticalLinePhasor.XiKernel.Psi2_bound
