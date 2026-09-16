import RequestProject.FlowDerivRealRooted
import RequestProject.MergerAbstract

/-!
# The real section of the derivative family, and its `λ`-dynamics
-/

open Complex Filter Topology Set

namespace CriticalLinePhasor.XiKernel

noncomputable def xiRD (k : ℕ) (s : ℝ) (x : ℝ) : ℝ := (flowD k s (x : ℂ)).re

noncomputable def jRD (k : ℕ) (s : ℝ) (x : ℝ) : ℝ := -((flowD (k + 2) s (x : ℂ)).re)

theorem flowD_eq_xiRD (k : ℕ) (s : ℝ) (x : ℝ) : flowD k s (x : ℂ) = ((xiRD k s x : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [xiRD]
  · rw [Complex.ofReal_im]; exact flowD_im_ofReal k s x

theorem xiRD_eq_zero_iff (k : ℕ) (s : ℝ) (x : ℝ) :
    xiRD k s x = 0 ↔ flowD k s (x : ℂ) = 0 := by
  rw [flowD_eq_xiRD]; simp

theorem differentiable_flowD (k : ℕ) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Differentiable ℂ (flowD k lam) := fun z => (hasDerivAt_flowD_z k h0 h1 z).differentiableAt

/-- The `λ`-derivative of the real section. -/
theorem hasDerivAt_xiRD_lam (k : ℕ) {s lam₁ : ℝ} (h0 : 0 ≤ s) (hlt : s < lam₁) (h1 : lam₁ ≤ 1)
    (x : ℝ) : HasDerivAt (fun t : ℝ => xiRD k t x) (jRD k s x) s := by
  show HasDerivAt (fun t : ℝ => (flowD k t (x : ℂ)).re)
    (-((flowD (k + 2) s (x : ℂ)).re)) s
  have h := hasDerivAt_flowD_lam k h0 hlt h1 (x : ℂ)
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h

/-- `jRD` inherits the uniform Lipschitz bound in `λ`. -/
theorem jRD_lipschitz (k : ℕ) {lam₁ : ℝ} (h1 : lam₁ ≤ 1) (h1' : 0 ≤ lam₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s s' : ℝ, 0 ≤ s → 0 ≤ s' → s ≤ lam₁ → s' ≤ lam₁ →
      ∀ x : ℝ, |jRD k s x - jRD k s' x| ≤ |s - s'| * C := by
  obtain ⟨C, hC, hbd⟩ := flowD_lipschitz_lam (k + 2) h1 h1' (a := 0) le_rfl
  refine ⟨C, hC, ?_⟩
  intro s s' hs hs' hsl hsl' x
  have hz : |((x : ℂ)).im| ≤ 0 := by simp
  have h := hbd s s' hs hs' hsl hsl' (x : ℂ) hz
  calc |jRD k s x - jRD k s' x|
      = |(flowD (k + 2) s (x : ℂ) - flowD (k + 2) s' (x : ℂ)).re| := by
        unfold jRD; rw [Complex.sub_re]; rw [abs_sub_comm]; ring_nf
    _ ≤ ‖flowD (k + 2) s (x : ℂ) - flowD (k + 2) s' (x : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ |s - s'| * C := h

theorem continuous_jRD (k : ℕ) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Continuous (fun x : ℝ => jRD k lam x) := by
  unfold jRD
  exact ((Complex.continuous_re.comp
    ((differentiable_flowD (k + 2) h0 h1).continuous.comp Complex.continuous_ofReal))).neg

/-- The first two `x`-derivatives of the section are the next two members of the family. -/
theorem hasDerivAt_xiRD_fst (k : ℕ) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (x : ℝ) :
    HasDerivAt (xiRD k lam) ((flowD (k + 1) lam (x : ℂ)).re) x := by
  have h := ((differentiable_flowD k h0 h1 ((x : ℝ) : ℂ)).hasDerivAt).real_of_complex
  rw [(hasDerivAt_flowD_z k h0 h1 ((x : ℝ) : ℂ)).deriv] at h
  exact h

theorem deriv_xiRD_eq (k : ℕ) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    deriv (xiRD k lam) = fun y : ℝ => (flowD (k + 1) lam (y : ℂ)).re :=
  funext fun y => (hasDerivAt_xiRD_fst k h0 h1 y).deriv

theorem hasDerivAt_deriv_xiRD (k : ℕ) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (x : ℝ) :
    HasDerivAt (deriv (xiRD k lam)) ((flowD (k + 2) lam (x : ℂ)).re) x := by
  rw [deriv_xiRD_eq k h0 h1]
  have h := ((differentiable_flowD (k + 1) h0 h1 ((x : ℝ) : ℂ)).hasDerivAt).real_of_complex
  rw [(hasDerivAt_flowD_z (k + 1) h0 h1 ((x : ℝ) : ℂ)).deriv] at h
  exact h

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.hasDerivAt_xiRD_lam
#print axioms CriticalLinePhasor.XiKernel.jRD_lipschitz
#print axioms CriticalLinePhasor.XiKernel.hasDerivAt_deriv_xiRD
