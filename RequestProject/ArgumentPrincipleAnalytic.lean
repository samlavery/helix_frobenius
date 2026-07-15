import RequestProject.ArgumentPrincipleRectangle
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Analytic argument principle on a rectangle

This file upgrades the explicit finite inverse-coordinate kernel to analytic functions by
factoring their finite divisor on a compact rectangle.  The residual factor is analytic and
nowhere zero, hence its logarithmic derivative has zero boundary integral.
-/

open Complex Set MeasureTheory Filter Topology Function
open scoped Interval Real

noncomputable section

namespace CriticalLinePhasor.ContourArgument

private theorem closedBall_zero_preperfect {R : ℝ} (hR : 0 < R) :
    Preperfect (Metric.closedBall (0 : ℂ) R) := by
  apply IsPreconnected.preperfect_of_nontrivial
  · refine ⟨(0 : ℂ), by simp [hR.le], (R : ℂ), ?_, ?_⟩
    · simp [Metric.mem_closedBall, abs_of_pos hR, hR.le]
    · exact (Complex.ofReal_ne_zero.mpr hR.ne').symm
  · exact Metric.isPreconnected_closedBall

/-- Local divisor extraction on a closed ball, upgraded from codiscrete equality to equality of
logarithmic derivatives at every point outside the divisor support. -/
theorem exists_closedBall_divisor_factorization_logDeriv
    (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (hord : ∀ u : Metric.closedBall (0 : ℂ) R, meromorphicOrderAt f u ≠ ⊤) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) R) ∧
      (∀ u : Metric.closedBall (0 : ℂ) R, g u ≠ 0) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) R,
        MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R) z = 0 →
        logDeriv f z =
          logDeriv
              (∏ᶠ u, (· - u) ^
                MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R) u) z +
            logDeriv g z := by
  let U : Set ℂ := Metric.closedBall (0 : ℂ) R
  let D := MeromorphicOn.divisor f U
  have hmero : MeromorphicOn f U := hf.meromorphicOn
  have hDfin : D.support.Finite := D.finiteSupport (isCompact_closedBall 0 R)
  obtain ⟨g, hg, hgne, hfac⟩ := hmero.extract_zeros_poles hord hDfin
  refine ⟨g, hg, hgne, ?_⟩
  intro z hz hDz
  let P : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
  have hP_analytic : AnalyticAt ℂ P z := by
    exact Function.FactorizedRational.analyticAt (by simpa [D] using hDz.ge)
  have hg_analytic : AnalyticAt ℂ g z := hg z hz
  have hprod_analytic : AnalyticAt ℂ (P * g) z :=
    hP_analytic.mul hg_analytic
  have hpunc : f =ᶠ[𝓝[≠] z] P * g := by
    apply (hmero z hz).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      hprod_analytic.meromorphicAt hz (closedBall_zero_preperfect hR)
    simpa [P, D, U, Pi.smul_apply, smul_eq_mul] using hfac
  have hnhds : f =ᶠ[𝓝 z] P * g :=
    (hf z hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      hprod_analytic.continuousAt |>.mp hpunc
  have hPne : P z ≠ 0 := Function.FactorizedRational.ne_zero (by simpa [D] using hDz)
  have hgne_z : g z ≠ 0 := hgne ⟨z, hz⟩
  calc
    logDeriv f z = logDeriv (P * g) z := by
      unfold logDeriv
      simp only [Pi.div_apply]
      rw [hnhds.deriv_eq, hnhds.eq_of_nhds]
    _ = logDeriv P z + logDeriv g z :=
      logDeriv_mul z hPne hgne_z hP_analytic.differentiableAt hg_analytic.differentiableAt

/-- The logarithmic derivative of a finite factorized rational function has the explicit
multiplicity-weighted inverse-coordinate boundary integral. -/
theorem rectangleBoundaryIntegral_logDeriv_factorizedRational
    (D : ℂ → ℤ) (hD : D.support.Finite) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hoff : ∀ ρ ∈ hD.toFinset,
      ρ.re ≠ a ∧ ρ.re ≠ b ∧ ρ.im ≠ c ∧ ρ.im ≠ d) :
    rectangleBoundaryIntegral
        (logDeriv (∏ᶠ u, (· - u) ^ D u)) a b c d =
      (2 * Real.pi * I) *
        ∑ ρ ∈ hD.toFinset.filter (fun ρ ↦
          a < ρ.re ∧ ρ.re < b ∧ c < ρ.im ∧ ρ.im < d), (D ρ : ℂ) := by
  let S : Finset ℂ := hD.toFinset
  let P : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
  have hP : P = ∏ ρ ∈ S, (· - ρ) ^ D ρ := by
    dsimp [P, S]
    rw [finprod_eq_prod_of_mulSupport_subset]
    simpa [Function.FactorizedRational.mulSupport]
  have hprod_fun : (∏ ρ ∈ S, (· - ρ) ^ D ρ) =
      fun w ↦ ∏ ρ ∈ S, (w - ρ) ^ D ρ := by
    funext w
    simp
  have hlog : ∀ z : ℂ, (∀ ρ ∈ S, z ≠ ρ) →
      logDeriv P z = ∑ ρ ∈ S, (D ρ : ℂ) * (z - ρ)⁻¹ := by
    intro z hz
    rw [hP, hprod_fun]
    rw [logDeriv_prod]
    · apply Finset.sum_congr rfl
      intro ρ hρ
      rw [logDeriv_fun_zpow (f := fun w : ℂ ↦ w - ρ) (by fun_prop)]
      simp [logDeriv_apply, hz ρ hρ]
    · intro ρ hρ
      exact zpow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ))
    · intro ρ hρ
      exact (differentiableAt_id.sub_const ρ).zpow (Or.inl (sub_ne_zero.mpr (hz ρ hρ)))
  have heq :
      rectangleBoundaryIntegral (logDeriv P) a b c d =
        rectangleBoundaryIntegral
          (fun z ↦ ∑ ρ ∈ S, (D ρ : ℂ) * (z - ρ)⁻¹) a b c d := by
    have hbottom :
        (∫ x in a..b, logDeriv P (x + c * I)) =
          ∫ x in a..b, ∑ ρ ∈ S, (D ρ : ℂ) * (x + c * I - ρ)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply hlog
      intro ρ hρ heq
      have him := congrArg Complex.im heq
      simp at him
      exact (hoff ρ (by simpa [S] using hρ)).2.2.1 him.symm
    have htop :
        (∫ x in a..b, logDeriv P (x + d * I)) =
          ∫ x in a..b, ∑ ρ ∈ S, (D ρ : ℂ) * (x + d * I - ρ)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply hlog
      intro ρ hρ heq
      have him := congrArg Complex.im heq
      simp at him
      exact (hoff ρ (by simpa [S] using hρ)).2.2.2 him.symm
    have hright :
        (∫ y in c..d, logDeriv P (b + y * I)) =
          ∫ y in c..d, ∑ ρ ∈ S, (D ρ : ℂ) * (b + y * I - ρ)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro y hy
      apply hlog
      intro ρ hρ heq
      have hre := congrArg Complex.re heq
      simp at hre
      exact (hoff ρ (by simpa [S] using hρ)).2.1 hre.symm
    have hleft :
        (∫ y in c..d, logDeriv P (a + y * I)) =
          ∫ y in c..d, ∑ ρ ∈ S, (D ρ : ℂ) * (a + y * I - ρ)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro y hy
      apply hlog
      intro ρ hρ heq
      have hre := congrArg Complex.re heq
      simp at hre
      exact (hoff ρ (by simpa [S] using hρ)).1 hre.symm
    unfold rectangleBoundaryIntegral
    rw [hbottom, htop, hright, hleft]
  rw [show (∏ᶠ u, (· - u) ^ D u) = P by rfl, heq]
  exact rectangleBoundaryIntegral_weighted_divisor_off_boundary S
    (fun ρ ↦ (D ρ : ℂ)) hab hcd (by simpa [S] using hoff)

/-- **Argument principle on a rectangle.** For an analytic function extracted on a containing
closed ball, its logarithmic-derivative boundary integral is `2πi` times the divisor sum at the
strictly interior zeros.  No zero-count identity is assumed: the count is the analytic divisor. -/
theorem rectangleBoundaryIntegral_logDeriv_eq_divisor_sum
    (f : ℂ → ℂ) {R a b c d : ℝ} (hR : 0 < R) (hab : a ≤ b) (hcd : c ≤ d)
    (hrect : Icc a b ×ℂ Icc c d ⊆ Metric.closedBall (0 : ℂ) R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (hord : ∀ u : Metric.closedBall (0 : ℂ) R, meromorphicOrderAt f u ≠ ⊤)
    (hoff : ∀ ρ : ℂ,
      MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R) ρ ≠ 0 →
        ρ.re ≠ a ∧ ρ.re ≠ b ∧ ρ.im ≠ c ∧ ρ.im ≠ d) :
    let D := MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)
    let S := (D.finiteSupport (isCompact_closedBall 0 R)).toFinset
    rectangleBoundaryIntegral (logDeriv f) a b c d =
      (2 * Real.pi * I) *
        ∑ ρ ∈ S.filter (fun ρ ↦
          a < ρ.re ∧ ρ.re < b ∧ c < ρ.im ∧ ρ.im < d), (D ρ : ℂ) := by
  dsimp only
  let U : Set ℂ := Metric.closedBall (0 : ℂ) R
  let D := MeromorphicOn.divisor f U
  let S : Finset ℂ := (D.finiteSupport (isCompact_closedBall 0 R)).toFinset
  let P : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
  obtain ⟨g, hg, hgne, hfactor⟩ :=
    exists_closedBall_divisor_factorization_logDeriv f hR hf hord
  have hDzero_line : ∀ z : ℂ,
      (z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d) → D z = 0 := by
    intro z hzline
    by_contra hDz
    have hb := hoff z (by simpa [D, U] using hDz)
    rcases hzline with hza | hzb | hzc | hzd
    · exact hb.1 hza
    · exact hb.2.1 hzb
    · exact hb.2.2.1 hzc
    · exact hb.2.2.2 hzd
  have hlogP_analytic : ∀ z : ℂ, D z = 0 → AnalyticAt ℂ (logDeriv P) z := by
    intro z hDz
    have hPa : AnalyticAt ℂ P z :=
      Function.FactorizedRational.analyticAt (by simpa [P] using hDz.ge)
    have hPne : P z ≠ 0 := Function.FactorizedRational.ne_zero (by simpa [P] using hDz)
    simpa [logDeriv] using hPa.deriv.div hPa hPne
  have hlogg_analytic : ∀ z ∈ U, AnalyticAt ℂ (logDeriv g) z := by
    intro z hz
    have hga := hg z hz
    simpa [logDeriv] using hga.deriv.div hga (hgne ⟨z, hz⟩)
  have hmem_bottom (x : ℝ) (hx : x ∈ Icc a b) : x + c * I ∈ Icc a b ×ℂ Icc c d := by
    rw [Complex.mem_reProdIm]
    constructor
    · simpa using hx
    · simpa using (show c ∈ Icc c d from ⟨le_rfl, hcd⟩)
  have hmem_top (x : ℝ) (hx : x ∈ Icc a b) : x + d * I ∈ Icc a b ×ℂ Icc c d := by
    rw [Complex.mem_reProdIm]
    constructor
    · simpa using hx
    · simpa using (show d ∈ Icc c d from ⟨hcd, le_rfl⟩)
  have hmem_right (y : ℝ) (hy : y ∈ Icc c d) : b + y * I ∈ Icc a b ×ℂ Icc c d := by
    rw [Complex.mem_reProdIm]
    constructor
    · simpa using (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
    · simpa using hy
  have hmem_left (y : ℝ) (hy : y ∈ Icc c d) : a + y * I ∈ Icc a b ×ℂ Icc c d := by
    rw [Complex.mem_reProdIm]
    constructor
    · simpa using (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
    · simpa using hy
  have hPbottom : Continuous (fun x : ℝ ↦ logDeriv P (x + c * I)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hlogP_analytic _ (hDzero_line _ (Or.inr (Or.inr (Or.inl (by simp)))))).continuousAt.comp
      (by fun_prop)
  have hPtop : Continuous (fun x : ℝ ↦ logDeriv P (x + d * I)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hlogP_analytic _ (hDzero_line _ (Or.inr (Or.inr (Or.inr (by simp)))))).continuousAt.comp
      (by fun_prop)
  have hPright : Continuous (fun y : ℝ ↦ logDeriv P (b + y * I)) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (hlogP_analytic _ (hDzero_line _ (Or.inr (Or.inl (by simp))))).continuousAt.comp
      (by fun_prop)
  have hPleft : Continuous (fun y : ℝ ↦ logDeriv P (a + y * I)) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (hlogP_analytic _ (hDzero_line _ (Or.inl (by simp)))).continuousAt.comp
      (by fun_prop)
  have hgbottom : IntervalIntegrable (fun x : ℝ ↦ logDeriv g (x + c * I)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply (hlogg_analytic _ ?_).continuousAt.comp (by fun_prop)
    exact hrect (hmem_bottom x hx)
  have hgtop : IntervalIntegrable (fun x : ℝ ↦ logDeriv g (x + d * I)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply (hlogg_analytic _ ?_).continuousAt.comp (by fun_prop)
    exact hrect (hmem_top x hx)
  have hgright : IntervalIntegrable (fun y : ℝ ↦ logDeriv g (b + y * I)) volume c d := by
    apply ContinuousOn.intervalIntegrable_of_Icc hcd
    intro y hy
    apply ContinuousAt.continuousWithinAt
    apply (hlogg_analytic _ ?_).continuousAt.comp (by fun_prop)
    exact hrect (hmem_right y hy)
  have hgleft : IntervalIntegrable (fun y : ℝ ↦ logDeriv g (a + y * I)) volume c d := by
    apply ContinuousOn.intervalIntegrable_of_Icc hcd
    intro y hy
    apply ContinuousAt.continuousWithinAt
    apply (hlogg_analytic _ ?_).continuousAt.comp (by fun_prop)
    exact hrect (hmem_left y hy)
  have hdecomp : rectangleBoundaryIntegral (logDeriv f) a b c d =
      rectangleBoundaryIntegral (fun z ↦ logDeriv P z + logDeriv g z) a b c d := by
    have hbottom :
        (∫ x in a..b, logDeriv f (x + c * I)) =
          ∫ x in a..b, logDeriv P (x + c * I) + logDeriv g (x + c * I) := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply hfactor
      · exact hrect (hmem_bottom x (by simpa [uIcc_of_le hab] using hx))
      · simpa [D, U] using hDzero_line (x + c * I) (Or.inr (Or.inr (Or.inl (by simp))))
    have htop :
        (∫ x in a..b, logDeriv f (x + d * I)) =
          ∫ x in a..b, logDeriv P (x + d * I) + logDeriv g (x + d * I) := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply hfactor
      · exact hrect (hmem_top x (by simpa [uIcc_of_le hab] using hx))
      · simpa [D, U] using hDzero_line (x + d * I) (Or.inr (Or.inr (Or.inr (by simp))))
    have hright :
        (∫ y in c..d, logDeriv f (b + y * I)) =
          ∫ y in c..d, logDeriv P (b + y * I) + logDeriv g (b + y * I) := by
      apply intervalIntegral.integral_congr
      intro y hy
      apply hfactor
      · exact hrect (hmem_right y (by simpa [uIcc_of_le hcd] using hy))
      · simpa [D, U] using hDzero_line (b + y * I) (Or.inr (Or.inl (by simp)))
    have hleft :
        (∫ y in c..d, logDeriv f (a + y * I)) =
          ∫ y in c..d, logDeriv P (a + y * I) + logDeriv g (a + y * I) := by
      apply intervalIntegral.integral_congr
      intro y hy
      apply hfactor
      · exact hrect (hmem_left y (by simpa [uIcc_of_le hcd] using hy))
      · simpa [D, U] using hDzero_line (a + y * I) (Or.inl (by simp))
    unfold rectangleBoundaryIntegral
    rw [hbottom, htop, hright, hleft]
  have hadd := rectangleBoundaryIntegral_add_of_intervalIntegrable
    (logDeriv P) (logDeriv g) a b c d
    (hPbottom.intervalIntegrable _ _) hgbottom
    (hPtop.intervalIntegrable _ _) hgtop
    (hPright.intervalIntegrable _ _) hgright
    (hPleft.intervalIntegrable _ _) hgleft
  have hgzero : rectangleBoundaryIntegral (logDeriv g) a b c d = 0 := by
    apply rectangleBoundaryIntegral_logDeriv_eq_zero g
    · intro z hz
      exact hg z (hrect hz)
    · intro z hz
      exact hgne ⟨z, hrect hz⟩
    · exact hab
    · exact hcd
  have hDfin : D.support.Finite := D.finiteSupport (isCompact_closedBall 0 R)
  have hPcount := rectangleBoundaryIntegral_logDeriv_factorizedRational D hDfin hab hcd
    (by
      intro ρ hρ
      apply hoff ρ
      simpa [D, U, Function.mem_support] using hDfin.mem_toFinset.mp hρ)
  rw [hdecomp, hadd, hgzero, add_zero, hPcount]


end CriticalLinePhasor.ContourArgument
