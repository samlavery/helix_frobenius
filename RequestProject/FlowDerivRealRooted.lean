import RequestProject.FlowDerivProps
import RequestProject.StripClassDeriv
import RequestProject.DeBruijnFlowFrontier

/-!
# Every `z`-derivative of the warped fiber is real-rooted above the frontier

`flowD k lam = deriv^[k](flowStage lam)` and `flowStage lam` is a locally uniform limit of the cosh
stages, which lie in `StripClass 0` for `λ ≥ 1/8`.  `StripClass.iterate_deriv_mem` carries that to
every derivative of every stage, and Hurwitz carries real-rootedness to the limit.
-/

open Complex Filter Topology Polynomial
open CriticalLinePhasor.DeBruijn

namespace CriticalLinePhasor.XiKernel

/-- `StripClass` is closed under multiplication by a nonzero real constant. -/
theorem StripClass.const_mul {σ : ℝ} {f : ℂ → ℂ} (hf : StripClass σ f) {c : ℝ} (hc : c ≠ 0) :
    StripClass σ (fun z => (c : ℂ) * f z) := by
  obtain ⟨P, hP0, hPz, hPlim⟩ := hf
  refine ⟨fun n => Polynomial.C c * P n, ?_, ?_, ?_⟩
  · intro n h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact hc (by simpa using h)
    · exact hP0 n h
  · intro n w hw
    rw [map_mul, Polynomial.aeval_C, mul_eq_zero] at hw
    rcases hw with h | h
    · exact absurd (Complex.ofReal_eq_zero.mp h) hc
    · exact hPz n w h
  · have hg : UniformContinuous (fun w : ℂ => ((c : ℝ) : ℂ) * w) := by
      have h : UniformContinuous (fun w : ℂ => ((c : ℝ) : ℂ) • w) :=
        uniformContinuous_const_smul _
      simpa only [smul_eq_mul] using h
    have hcomp := hg.comp_tendstoLocallyUniformly hPlim
    have hseq : (fun (n : ℕ) (z : ℂ) => Polynomial.aeval z (Polynomial.C c * P n))
        = fun (n : ℕ) (z : ℂ) => ((c : ℝ) : ℂ) * Polynomial.aeval z (P n) := by
      funext n z
      rw [map_mul, Polynomial.aeval_C]
      first | rfl | rw [Complex.coe_algebraMap] | simp
    rw [hseq]
    exact hcomp

/-- The cosh stages lie in `StripClass 0` once the shifts have consumed the strip. -/
theorem coshStage_stripClass {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 1 / 4 ≤ (N : ℝ) * h ^ 2) :
    StripClass 0 (coshStage h N) := by
  have hc := Ktrans_stripClass.shiftIter (by norm_num) hh N
  rw [shiftOp_iterate_Ktrans] at hc
  have h0 : max (1 / 4 - (N : ℝ) * h ^ 2) 0 = 0 := max_eq_right (by linarith)
  rwa [h0] at hc

theorem coshApprox_stripClass {lam : ℝ} (hlam : 1 / 8 ≤ lam) (n : ℕ) :
    StripClass 0 (coshApprox lam n) := by
  have hpos : 0 < flowShift lam n := flowShift_pos (by linarith) n
  have hsq : 1 / 4 ≤ ((n + 1 : ℕ) : ℝ) * (flowShift lam n) ^ 2 := by
    rw [flowShift_sq (by linarith)]
    push_cast
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ hn]
    linarith
  have hmem := StripClass.const_mul (coshStage_stripClass hpos hsq)
    (c := ((2 : ℝ) ^ (n + 1))⁻¹) (by positivity)
  have hfun : coshApprox lam n
      = fun z => ((((2 : ℝ) ^ (n + 1))⁻¹ : ℝ) : ℂ) * coshStage (flowShift lam n) (n + 1) z := by
    funext z
    rw [coshStage_eq_two_pow_mul_coshApprox]
    push_cast
    field_simp
  rw [hfun]
  exact hmem


theorem differentiable_iterate_deriv : ∀ (k : ℕ) {g : ℂ → ℂ}, Differentiable ℂ g →
    Differentiable ℂ (deriv^[k] g) := by
  intro k
  induction k with
  | zero => intro g hg; simpa using hg
  | succ k ih =>
    intro g hg
    rw [Function.iterate_succ_apply']
    have hA : AnalyticOnNhd ℂ (deriv^[k] g) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr (ih hg)
    exact fun z => ((hA z (Set.mem_univ z)).deriv).differentiableAt

theorem tlu_iterate_deriv : ∀ (k : ℕ) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ},
    (∀ n, Differentiable ℂ (F n)) → TendstoLocallyUniformly F f atTop →
    TendstoLocallyUniformly (fun n => deriv^[k] (F n)) (deriv^[k] f) atTop := by
  intro k
  induction k with
  | zero => intro F f _ h; simpa using h
  | succ k ih =>
    intro F f hF h
    have hd := ((ih hF h).tendstoLocallyUniformlyOn (s := Set.univ)).deriv
      (Eventually.of_forall fun n => (differentiable_iterate_deriv k (hF n)).differentiableOn)
      isOpen_univ
    rw [tendstoLocallyUniformlyOn_univ] at hd
    have hfunseq : (deriv ∘ fun n => deriv^[k] (F n)) = fun n => deriv^[k + 1] (F n) := by
      funext n
      rw [Function.iterate_succ_apply']
      rfl
    rw [hfunseq] at hd
    rw [Function.iterate_succ_apply']
    exact hd

/-- **Every `z`-derivative of the warped fiber is real-rooted above the frontier.** -/
theorem flowD_real_rooted (k : ℕ) {lam : ℝ} (h8 : 1 / 8 ≤ lam) (h1 : lam ≤ 1)
    (hne : ∃ z, flowD k lam z ≠ 0) : ∀ z : ℂ, flowD k lam z = 0 → z.im = 0 := by
  rw [flowD_eq_iterate_deriv k (by linarith) h1] at hne ⊢
  have hconv := tlu_iterate_deriv k (fun n => differentiable_coshApprox lam n)
    (tendstoLocallyUniformly_coshApprox (by linarith) h1)
  obtain ⟨z₀, hz₀⟩ := hne
  have hptw : Tendsto (fun n => deriv^[k] (coshApprox lam n) z₀) atTop
      (𝓝 (deriv^[k] (flowStage lam) z₀)) :=
    (tendstoLocallyUniformlyOn_univ.mpr hconv).tendsto_at (Set.mem_univ z₀)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hptw.eventually_ne hz₀)
  refine CriticalLinePhasor.Hurwitz.im_eq_zero_of_tendstoLocallyUniformly
    (fun j => differentiable_iterate_deriv k (differentiable_coshApprox lam (j + N))) ?_
    (tendstoLocallyUniformly_shift hconv N) ⟨z₀, hz₀⟩
  intro j w hw
  have hnz : ∃ z, deriv^[k] (coshApprox lam (j + N)) z ≠ 0 :=
    ⟨z₀, hN (j + N) (Nat.le_add_left _ _)⟩
  exact (StripClass.iterate_deriv_mem k (coshApprox_stripClass h8 (j + N)) hnz).im_eq_zero_of_zero
    hnz w hw

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.coshApprox_stripClass
#print axioms CriticalLinePhasor.XiKernel.flowD_real_rooted
