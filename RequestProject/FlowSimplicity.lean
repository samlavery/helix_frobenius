import RequestProject.FlowDerivNoDoubleNeg

/-!
# Simplicity of the warped fiber above the frontier

`flowD_eq_zero_of_double` says a double zero at order `k` forces one at order `k+2`.  Starting from a
double zero of `Ξ_{λ₀}` itself, induction gives `Ξ^{(k)}_{λ₀}(x₀) = 0` for EVERY `k`, so the analytic
order at `x₀` is `⊤`, so `Ξ_{λ₀}` vanishes identically — contradicting `flowStage_ne_zero`.

Hence every zero of `Ξ_λ` is simple for `1/8 < λ < 1`.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.XiKernel

/-- All derivatives vanish at a double zero. -/
theorem flowD_all_eq_zero {lam₀ : ℝ} (h8 : 1 / 8 < lam₀) (h1 : lam₀ < 1) {x₀ : ℝ}
    (hz : flowD 0 lam₀ (x₀ : ℂ) = 0) (hdz : flowD 1 lam₀ (x₀ : ℂ) = 0) :
    ∀ k, flowD k lam₀ (x₀ : ℂ) = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => exact hz
    | 1 => exact hdz
    | (n + 2) =>
      exact flowD_eq_zero_of_double n h8 h1 (ih n (by omega)) (ih (n + 1) (by omega))

/-- **Every zero of the warped fiber is simple, for `1/8 < λ < 1`.** -/
theorem flowStage_zero_simple {lam₀ : ℝ} (h8 : 1 / 8 < lam₀) (h1 : lam₀ < 1) {x₀ : ℝ}
    (hz : flowStage lam₀ (x₀ : ℂ) = 0) : deriv (flowStage lam₀) (x₀ : ℂ) ≠ 0 := by
  intro hdz
  have h0 : (0:ℝ) ≤ lam₀ := by linarith
  have hd0 : flowD 0 lam₀ (x₀ : ℂ) = 0 := by rw [flowD_zero_eq]; exact hz
  have hd1 : flowD 1 lam₀ (x₀ : ℂ) = 0 := by
    have := flowD_eq_iterate_deriv 1 h0 h1.le
    rw [show deriv (flowStage lam₀) ((x₀ : ℝ) : ℂ) = flowD 1 lam₀ ((x₀ : ℝ) : ℂ) by
      rw [this]; simp] at hdz
    exact hdz
  have hall := flowD_all_eq_zero h8 h1 hd0 hd1
  have hder : ∀ i : ℕ, iteratedDeriv i (flowStage lam₀) ((x₀ : ℝ) : ℂ) = 0 := by
    intro i
    rw [iteratedDeriv_eq_iterate, ← flowD_eq_iterate_deriv i h0 h1.le]
    exact hall i
  have hAn : AnalyticOnNhd ℂ (flowStage lam₀) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_flowStage h0 h1.le)
  have hA : AnalyticAt ℂ (flowStage lam₀) ((x₀ : ℝ) : ℂ) := hAn _ (Set.mem_univ _)
  have htop : analyticOrderAt (flowStage lam₀) ((x₀ : ℝ) : ℂ) = ⊤ := by
    by_contra hcon
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hcon
    have hle : ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (flowStage lam₀) ((x₀ : ℝ) : ℂ) :=
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA).mpr fun i _ => hder i
    rw [← hn] at hle
    exact absurd hle (by exact_mod_cast Nat.not_succ_le_self n)
  have hev : flowStage lam₀ =ᶠ[𝓝 ((x₀ : ℝ) : ℂ)] 0 := analyticOrderAt_eq_top.mp htop
  obtain ⟨z₁, hz₁⟩ := flowStage_ne_zero h0 h1.le
  exact hz₁ (hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ _) hev (Set.mem_univ z₁))


/-- **SIMPLICITY OF THE FLOW.**  For `1/8 < λ < 1`, every zero of the amplitude-warped fiber
`Ξ_λ(z) = ∫ e^{λu²}K(u)e^{izu}du` is real AND simple. -/
theorem flowStage_simple {lam₀ : ℝ} (h8 : 1 / 8 < lam₀) (h1 : lam₀ < 1) {z : ℂ}
    (hz : flowStage lam₀ z = 0) :
    z.im = 0 ∧ deriv (flowStage lam₀) z ≠ 0 := by
  have him : z.im = 0 := flowFrontier_one_eighth lam₀ h8.le h1.le z hz
  refine ⟨him, ?_⟩
  have hzre : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
  rw [hzre] at hz ⊢
  exact flowStage_zero_simple h8 h1 hz

/-- The same, as a statement about the analytic order. -/
theorem flowStage_analyticOrderAt_eq_one {lam₀ : ℝ} (h8 : 1 / 8 < lam₀) (h1 : lam₀ < 1) {z : ℂ}
    (hz : flowStage lam₀ z = 0) : analyticOrderAt (flowStage lam₀) z = 1 := by
  have h0 : (0:ℝ) ≤ lam₀ := by linarith
  have hAn : AnalyticOnNhd ℂ (flowStage lam₀) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_flowStage h0 h1.le)
  have hA : AnalyticAt ℂ (flowStage lam₀) z := hAn _ (Set.mem_univ _)
  obtain ⟨-, hd⟩ := flowStage_simple h8 h1 hz
  have hone : ((1 : ℕ) : ℕ∞) ≤ analyticOrderAt (flowStage lam₀) z :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA).mpr (by
      intro i hi
      interval_cases i
      simpa using hz)
  have hnot : ¬ (((2 : ℕ) : ℕ∞) ≤ analyticOrderAt (flowStage lam₀) z) := by
    intro hle
    have := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA).mp hle 1 (by norm_num)
    rw [iteratedDeriv_one] at this
    exact hd this
  rcases eq_or_ne (analyticOrderAt (flowStage lam₀) z) ⊤ with htop | hfin
  · rw [htop] at hnot; exact absurd le_top hnot
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hn] at hone hnot ⊢
    have h1' : 1 ≤ n := by exact_mod_cast hone
    have h2' : ¬ (2 ≤ n) := fun hc => hnot (by exact_mod_cast hc)
    have : n = 1 := by omega
    rw [this]; rfl

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.flowD_all_eq_zero
#print axioms CriticalLinePhasor.XiKernel.flowStage_zero_simple
#print axioms CriticalLinePhasor.XiKernel.flowStage_simple
#print axioms CriticalLinePhasor.XiKernel.flowStage_analyticOrderAt_eq_one
