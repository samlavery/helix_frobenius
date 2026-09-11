import RequestProject.XiStripApproximants
import RequestProject.FlowFrontier

/-!
# De Bruijn's strip narrowing for the flow cascade: `FlowFrontier (1/8)` (T2c)

Assembly of the four pieces:
* `xiSection_stripClass` — `Ξ = Ktrans` is a locally uniform limit of real polynomials with zeros in `(Im)² ≤ ¼`;
* `StripClass.shiftIter` — `N` imaginary shifts by `h` narrow the strip to `max (¼ − N h²) 0`
  (the compiled polynomial step, de Bruijn's `cos(hD)` operator);
* `shiftOp_iterate_Ktrans` — the `N`-fold shift of the transform is the cosh-power stage
  `∫ (2cosh(hu))^N K(u) e^{izu} du`, and `StripClass.im_eq_zero_of_zero` (Hurwitz) makes it real-rooted once
  `N h² ≥ ¼`;
* `tendstoLocallyUniformly_coshApprox` — with `h_n = √(2λ/(n+1))` the normalised stages converge locally uniformly
  to `flowStage λ` (dominated convergence, `cosh(h_n u)^{n+1} → e^{λu²}`), and Hurwitz again gives real zeros.

Hence every stage `flowStage λ`, `1/8 ≤ λ ≤ 1`, has only real zeros: `flowFrontier_one_eighth`.  In the burndown's
cascade `λ_n = 1/(n+1)`, the stages `n ≤ 7` are discharged at every height (`flowCascade_realRooted_of_le_seven`).
-/

open Complex Filter Topology
open CriticalLinePhasor.DeBruijn
open CriticalLinePhasor.XiApprox (xiSection_stripClass)

namespace CriticalLinePhasor.XiKernel

/-- `Ktrans = Ξ` lies in the strip class at `¼`. -/
theorem Ktrans_stripClass : StripClass (1 / 4) Ktrans := by
  have h := xiSection_stripClass
  have hfun : CriticalLinePhasor.XiChannel.xiSection = Ktrans := funext xiSection_eq_Ktrans
  rwa [hfun] at h

/-- **The cosh-power stage is real-rooted once `N h² ≥ ¼`** (de Bruijn's shift theorem for `Ξ`). -/
theorem coshStage_realRooted {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 1 / 4 ≤ (N : ℝ) * h ^ 2) :
    ∀ z : ℂ, coshStage h N z = 0 → z.im = 0 := by
  have hc := Ktrans_stripClass.shiftIter (by norm_num) hh N
  rw [shiftOp_iterate_Ktrans] at hc
  have h0 : max (1 / 4 - (N : ℝ) * h ^ 2) 0 = 0 := max_eq_right (by linarith)
  rw [h0] at hc
  exact hc.im_eq_zero_of_zero (coshStage_ne_zero h N)

theorem flowShift_pos {lam : ℝ} (hlam : 0 < lam) (n : ℕ) : 0 < flowShift lam n := by
  unfold flowShift
  exact Real.sqrt_pos.mpr (by positivity)

/-- The normalised stages are real-rooted for `λ ≥ 1/8`. -/
theorem coshApprox_realRooted {lam : ℝ} (hlam : 1 / 8 ≤ lam) (n : ℕ) :
    ∀ z : ℂ, coshApprox lam n z = 0 → z.im = 0 := by
  intro z hz
  rw [coshApprox_eq_zero_iff] at hz
  refine coshStage_realRooted (flowShift_pos (by linarith) n) ?_ z hz
  rw [flowShift_sq (by linarith)]
  push_cast
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hn]
  linarith

theorem differentiable_coshApprox (lam : ℝ) (n : ℕ) : Differentiable ℂ (coshApprox lam n) := by
  have hfun : coshApprox lam n =
      fun z => ((2 : ℂ) ^ (n + 1))⁻¹ * coshStage (flowShift lam n) (n + 1) z := by
    funext z
    rw [coshStage_eq_two_pow_mul_coshApprox]
    field_simp
  rw [hfun]
  exact (differentiable_coshStage _ _).const_mul _

/-- **De Bruijn's theorem in the frame's normalisation: the flow frontier holds at `1/8`.**
Every stage `Ξ_λ`, `1/8 ≤ λ ≤ 1`, has only real zeros. -/
theorem flowFrontier_one_eighth : FlowFrontier (1 / 8) := by
  intro lam hlam hlam1 z hz
  exact CriticalLinePhasor.Hurwitz.im_eq_zero_of_tendstoLocallyUniformly
    (fun n => differentiable_coshApprox lam n)
    (fun n => coshApprox_realRooted hlam n)
    (tendstoLocallyUniformly_coshApprox (by linarith) hlam1)
    (flowStage_ne_zero (by linarith) hlam1) z hz

/-- The frontier at every `λ₀ ≥ 1/8`. -/
theorem flowFrontier_of_one_eighth_le {lam₀ : ℝ} (h : 1 / 8 ≤ lam₀) : FlowFrontier lam₀ :=
  flowFrontier_one_eighth.mono h

/-- **Stages `n ≤ 7` of the cascade `λ_n = 1/(n+1)` are real-rooted at every height.** -/
theorem flowCascade_realRooted_of_le_seven {n : ℕ} (hn : n ≤ 7) :
    ∀ z : ℂ, flowStage (lamSeq n) z = 0 → z.im = 0 := by
  have h1 : 1 / 8 ≤ lamSeq n := by
    unfold lamSeq
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have : (n : ℝ) ≤ 7 := by exact_mod_cast hn
    linarith
  exact flowFrontier_one_eighth _ h1 (lamSeq_le_one n)

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.coshStage_realRooted
#print axioms CriticalLinePhasor.XiKernel.flowFrontier_one_eighth
#print axioms CriticalLinePhasor.XiKernel.flowCascade_realRooted_of_le_seven
