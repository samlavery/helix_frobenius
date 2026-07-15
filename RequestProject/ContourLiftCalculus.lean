import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Calculus of continuous logarithmic lifts

A continuous lift through the complex exponential is automatically differentiable whenever its
exponential is differentiable.  This supplies the analytic bridge from a covering-space argument
to a logarithmic-derivative contour integral.
-/

open Complex Filter Set Topology

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-- Local form: an eventual continuous logarithmic lift has derivative `F'/F`. -/
theorem hasDerivAt_of_continuousAt_exp_eventuallyEq
    {L F : ℝ → ℂ} {x : ℝ} {F' : ℂ}
    (hL : ContinuousAt L x)
    (hexp : (fun t ↦ Complex.exp (L t)) =ᶠ[𝓝 x] F)
    (hF : HasDerivAt F F' x) :
    HasDerivAt L (F' / F x) x := by
  have hexpx : Complex.exp (L x) = F x := hexp.eq_of_nhds
  have hFx : F x ≠ 0 := by rw [← hexpx]; exact Complex.exp_ne_zero _
  let Q : ℝ → ℂ := fun t ↦ F t / F x
  let G : ℝ → ℂ := fun t ↦ L x + Complex.log (Q t)
  have hQx : Q x = 1 := by simp [Q, hFx]
  have hQ : HasDerivAt Q (F' / F x) x := hF.div_const (F x)
  have hQslit : ∀ᶠ t in 𝓝 x, Q t ∈ Complex.slitPlane := by
    have hmem : (1 : ℂ) ∈ Complex.slitPlane := by simp
    exact hQ.continuousAt.eventually (Complex.isOpen_slitPlane.mem_nhds (hQx ▸ hmem))
  have hG : HasDerivAt G (F' / F x) x := by
    have hlog := hQ.clog_real (by simpa [hQx])
    change HasDerivAt (fun t ↦ L x + Complex.log (Q t)) (F' / F x) x
    have hadd := (hasDerivAt_const x (L x)).add hlog
    have heq : (fun t ↦ L x + Complex.log (Q t)) =
        (fun _ : ℝ ↦ L x) + fun t ↦ Complex.log (Q t) := by
      funext t
      rfl
    rw [heq]
    simpa [hQx] using hadd
  have hGx : G x = L x := by simp [G, hQx]
  have hsmall : ∀ᶠ t in 𝓝 x, ‖L t - G t‖ < 2 * Real.pi := by
    have hcont : ContinuousAt (fun t ↦ L t - G t) x :=
      hL.sub hG.continuousAt
    have hzero : L x - G x = 0 := by rw [hGx, sub_self]
    have hball : Metric.ball (0 : ℂ) (2 * Real.pi) ∈ 𝓝 (L x - G x) := by
      rw [hzero]
      exact Metric.ball_mem_nhds _ (mul_pos (by norm_num) Real.pi_pos)
    filter_upwards [hcont hball] with t ht
    simpa [Metric.mem_ball] using ht
  have hsame : L =ᶠ[𝓝 x] G := by
    filter_upwards [hsmall, hQslit, hexp] with t ht hQt hexpt
    have hQne : Q t ≠ 0 := Complex.slitPlane_ne_zero hQt
    have hexpG : Complex.exp (G t) = F t := by
      dsimp [G]
      rw [Complex.exp_add, Complex.exp_log hQne, hexpx]
      dsimp [Q]
      field_simp
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hexpt.trans hexpG.symm)
    have hdiff : L t - G t = (n : ℂ) * (2 * Real.pi * I) := by rw [hn]; ring
    have hn0 : n = 0 := by
      by_contra hn0
      have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
        have hnat : 1 ≤ n.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hn0)
        have hcast : (1 : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hnat
        simpa using hcast
      have hnorm : ‖L t - G t‖ = |(n : ℝ)| * (2 * Real.pi) := by
        rw [hdiff, norm_mul]
        simp [abs_of_pos Real.pi_pos]
      rw [hnorm] at ht
      nlinarith [Real.pi_pos]
    simpa [hn0] using hn
  exact hG.congr_of_eventuallyEq hsame

/-- A continuous logarithmic lift has derivative `F'/F`. -/
theorem hasDerivAt_of_continuous_exp_eq
    {L F : ℝ → ℂ} {x : ℝ} {F' : ℂ}
    (hL : Continuous L) (hexp : ∀ t, Complex.exp (L t) = F t)
    (hF : HasDerivAt F F' x) :
    HasDerivAt L (F' / F x) x :=
  hasDerivAt_of_continuousAt_exp_eventuallyEq hL.continuousAt
    (Filter.Eventually.of_forall hexp) hF

/-- Fundamental theorem of calculus for a continuous logarithmic lift. -/
theorem intervalIntegral_logDeriv_eq_lift_sub
    {L F F' : ℝ → ℂ} {a b : ℝ}
    (hL : Continuous L) (hexp : ∀ t, Complex.exp (L t) = F t)
    (hF : ∀ t ∈ uIcc a b, HasDerivAt F (F' t) t)
    (hint : IntervalIntegrable (fun t ↦ F' t / F t) MeasureTheory.volume a b) :
    (∫ t in a..b, F' t / F t) = L b - L a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    exact hasDerivAt_of_continuous_exp_eq hL hexp (hF t ht)
  · exact hint

/-- Fundamental theorem on a closed interval when the exponential identity is only known on
that interval.  Endpoint differentiability is unnecessary: the derivative identity is used on
the open interval, while continuity supplies the endpoint values. -/
theorem intervalIntegral_logDeriv_eq_lift_sub_of_le
    {L F F' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hL : Continuous L)
    (hexp : ∀ t ∈ Icc a b, Complex.exp (L t) = F t)
    (hF : ∀ t ∈ Ioo a b, HasDerivAt F (F' t) t)
    (hint : IntervalIntegrable (fun t ↦ F' t / F t) MeasureTheory.volume a b) :
    (∫ t in a..b, F' t / F t) = L b - L a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hL.continuousOn
  · intro t ht
    apply hasDerivAt_of_continuousAt_exp_eventuallyEq hL.continuousAt
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      exact hexp u ⟨hu.1.le, hu.2.le⟩
    · exact hF t ht
  · exact hint

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.hasDerivAt_of_continuous_exp_eq
#print axioms CriticalLinePhasor.ContourArgument.intervalIntegral_logDeriv_eq_lift_sub
#print axioms CriticalLinePhasor.ContourArgument.intervalIntegral_logDeriv_eq_lift_sub_of_le
