import RequestProject.FlowLamDerivCont

/-!
# The warped fiber on the axis, as a real function of `(λ, x)`

`xiR s x = Re Ξ_s(x)` for real `x`.  By Schwarz reflection (`flowStage_conj`) `Ξ_s` is real there, so
`xiR` loses nothing.  Its `λ`-derivative is `Re J`, and `J` is Lipschitz in `λ` uniformly on the axis,
so the sign of `∂_λ xiR` near a point propagates to a rectangle — which is all the merger argument
needs (`strictAntiOn_of_deriv_neg`, no FTC required).
-/

open Complex MeasureTheory Filter Topology

namespace CriticalLinePhasor.XiKernel

/-- The stages are real on the axis. -/
theorem flowStage_im_ofReal (s : ℝ) (x : ℝ) : (flowStage s (x : ℂ)).im = 0 := by
  have h := flowStage_conj s (x : ℂ)
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith

/-- The real section of the warped fiber. -/
noncomputable def xiR (s : ℝ) (x : ℝ) : ℝ := (flowStage s (x : ℂ)).re

theorem flowStage_eq_xiR (s : ℝ) (x : ℝ) : flowStage s (x : ℂ) = ((xiR s x : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [xiR]
  · rw [Complex.ofReal_im]; exact flowStage_im_ofReal s x

theorem xiR_eq_zero_iff (s : ℝ) (x : ℝ) : xiR s x = 0 ↔ flowStage s (x : ℂ) = 0 := by
  rw [flowStage_eq_xiR]
  simp

/-- The real `λ`-derivative of the section. -/
noncomputable def jR (s : ℝ) (x : ℝ) : ℝ := (flowLamDeriv s (x : ℂ)).re

theorem hasDerivAt_xiR_lam {s lam₁ : ℝ} (h0 : 0 ≤ s) (hlt : s < lam₁) (h1 : lam₁ ≤ 1) (x : ℝ) :
    HasDerivAt (fun t : ℝ => xiR t x) (jR s x) s := by
  have h := hasDerivAt_flowStage_lam h0 hlt h1 (x : ℂ)
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h

/-- `jR` inherits the uniform Lipschitz bound in `λ`. -/
theorem jR_lipschitz {lam₁ : ℝ} (h1 : lam₁ ≤ 1) (h1' : 0 ≤ lam₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s s' : ℝ, 0 ≤ s → 0 ≤ s' → s ≤ lam₁ → s' ≤ lam₁ →
      ∀ x : ℝ, |jR s x - jR s' x| ≤ |s - s'| * C := by
  obtain ⟨C, hC, hbd⟩ := flowLamDeriv_lipschitz_lam h1 h1' (a := 0) le_rfl
  refine ⟨C, hC, ?_⟩
  intro s s' hs hs' hsl hsl' x
  have hz : |((x : ℂ)).im| ≤ 0 := by simp
  have h := hbd s s' hs hs' hsl hsl' (x : ℂ) hz
  calc |jR s x - jR s' x| = |(flowLamDeriv s (x : ℂ) - flowLamDeriv s' (x : ℂ)).re| := by
        unfold jR; rw [Complex.sub_re]
    _ ≤ ‖flowLamDeriv s (x : ℂ) - flowLamDeriv s' (x : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ |s - s'| * C := h

/-- `jR λ₀ ·` is continuous: it is the real part of `−∂_x²Ξ_{λ₀}`, and `Ξ_{λ₀}` is entire. -/
theorem continuous_jR_snd {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Continuous (fun x : ℝ => jR lam x) := by
  have hdiff : Differentiable ℂ (flowStage lam) := differentiable_flowStage h0 h1
  have hA : AnalyticOnNhd ℂ (flowStage lam) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff
  have hd1 : Differentiable ℂ (deriv (flowStage lam)) := fun z =>
    ((hA z (Set.mem_univ z)).deriv).differentiableAt
  have hA2 : AnalyticOnNhd ℂ (deriv (flowStage lam)) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hd1
  have hd2 : Differentiable ℂ (deriv (deriv (flowStage lam))) := fun z =>
    ((hA2 z (Set.mem_univ z)).deriv).differentiableAt
  have hfun : (fun x : ℝ => jR lam x)
      = fun x : ℝ => -((deriv (deriv (flowStage lam)) (x : ℂ)).re) := by
    funext x
    have hd := (hasDerivAt_deriv_flowStage h0 h1 (x : ℂ)).deriv
    unfold jR flowLamDeriv
    rw [hd]
    simp
  rw [hfun]
  exact (Complex.continuous_re.comp (hd2.continuous.comp Complex.continuous_ofReal)).neg

/-- The link between `jR` and the second `x`-derivative, used to read the sign. -/
theorem jR_eq_neg_deriv2 {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (x : ℝ) :
    jR lam x = -((deriv (deriv (flowStage lam)) (x : ℂ)).re) := by
  have hd := (hasDerivAt_deriv_flowStage h0 h1 (x : ℂ)).deriv
  unfold jR flowLamDeriv
  rw [hd]
  simp

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.flowStage_eq_xiR
#print axioms CriticalLinePhasor.XiKernel.hasDerivAt_xiR_lam
#print axioms CriticalLinePhasor.XiKernel.jR_lipschitz
#print axioms CriticalLinePhasor.XiKernel.continuous_jR_snd
