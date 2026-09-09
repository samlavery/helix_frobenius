import RequestProject.XiFlowCascade

set_option autoImplicit false

open Complex MeasureTheory Filter Topology

namespace CriticalLinePhasor.XiKernel

/-- The exact Fourier-side multiplier for one symmetric imaginary-shift step. -/
theorem exp_symmetric_shift (h u : ℝ) (z : ℂ) :
    Complex.exp (I * (z + I * h) * u) + Complex.exp (I * (z - I * h) * u) =
      2 * (Real.cosh (h * u) : ℂ) * Complex.exp (I * z * u) := by
  have hp : I * (z + I * h) * u = I * z * u + -((h : ℂ) * u) := by
    linear_combination (h : ℂ) * (u : ℂ) * Complex.I_sq
  have hm : I * (z - I * h) * u = I * z * u + (h : ℂ) * u := by
    linear_combination -(h : ℂ) * (u : ℂ) * Complex.I_sq
  rw [hp, hm, Complex.exp_add, Complex.exp_add, Complex.ofReal_cosh,
    Complex.ofReal_mul, Complex.two_cosh]
  ring

/-- This is an identity for the actual theta-kernel flow, for every complex height. -/
theorem flowStage_symmetric_shift {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (h : ℝ) (z : ℂ) :
    flowStage lam (z + I * h) + flowStage lam (z - I * h) =
      2 * ∫ u : ℝ, (Real.exp (lam * u ^ 2) : ℂ) * Kker u *
        (Real.cosh (h * u) : ℂ) * Complex.exp (I * z * u) := by
  unfold flowStage
  rw [← integral_add (integrable_flow_integrand hlam0 hlam1 (z + I * h))
    (integrable_flow_integrand hlam0 hlam1 (z - I * h)), ← integral_const_mul]
  apply integral_congr_ae (Eventually.of_forall fun u => ?_)
  rw [← mul_add, exp_symmetric_shift]
  ring

/-- Finite products of the exact symmetric-shift multiplier. -/
noncomputable def coshStepWeight (lam : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  Real.cosh (Real.sqrt (2 * lam / ((n : ℝ) + 1)) * u) ^ (n + 1)

theorem quadratic_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have ht := (Real.hasSum_cosh x).summable.sum_le_tsum (Finset.range 2)
    (by
      intro i _
      apply div_nonneg
      · rw [pow_mul]
        exact pow_nonneg (sq_nonneg x) _
      · positivity)
  rw [(Real.hasSum_cosh x).tsum_eq] at ht
  simpa [Finset.sum_range_succ] using ht

theorem coshStepWeight_bounds {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) (u : ℝ) :
    (1 + lam * u ^ 2 / ((n : ℝ) + 1)) ^ (n + 1) ≤ coshStepWeight lam n u ∧
      coshStepWeight lam n u ≤ Real.exp (lam * u ^ 2) := by
  have hs : (Real.sqrt (2 * lam / ((n : ℝ) + 1)) * u) ^ 2 / 2 =
      lam * u ^ 2 / ((n : ℝ) + 1) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  unfold coshStepWeight
  constructor
  · apply pow_le_pow_left₀ (by positivity)
    rw [← hs]
    exact quadratic_le_cosh _
  · calc
      Real.cosh (Real.sqrt (2 * lam / ((n : ℝ) + 1)) * u) ^ (n + 1)
          ≤ Real.exp (lam * u ^ 2 / ((n : ℝ) + 1)) ^ (n + 1) := by
            apply pow_le_pow_left₀ (Real.cosh_pos _).le
            rw [← hs]
            exact Real.cosh_le_exp_half_sq _
      _ = Real.exp (lam * u ^ 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        field_simp

theorem tendsto_coshStepWeight {lam : ℝ} (hlam : 0 ≤ lam) (u : ℝ) :
    Tendsto (fun n => coshStepWeight lam n u) atTop (𝓝 (Real.exp (lam * u ^ 2))) := by
  have hl := (Real.tendsto_one_add_div_pow_exp (lam * u ^ 2)).comp
    (tendsto_add_atTop_nat 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa [Function.comp_def] using hl) tendsto_const_nhds
    (fun n => (coshStepWeight_bounds hlam n u).1)
    (fun n => (coshStepWeight_bounds hlam n u).2)

noncomputable def coshStep (lam : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, (coshStepWeight lam n u : ℂ) * Kker u * Complex.exp (I * z * u)

theorem coshStepWeight_nonneg (lam : ℝ) (n : ℕ) (u : ℝ) :
    0 ≤ coshStepWeight lam n u := by
  unfold coshStepWeight
  exact pow_nonneg (Real.cosh_pos _).le _

theorem continuous_coshStepWeight (lam : ℝ) (n : ℕ) :
    Continuous (coshStepWeight lam n) := by
  unfold coshStepWeight
  fun_prop

private theorem weighted_flow_bound {lam M a : ℝ} (hlam : 0 ≤ lam)
    (hK : ∀ u : ℝ, ‖Kker u‖ ≤ M * Dabs (1 / 2) (2 * Rc) u)
    {z : ℂ} (hz : |z.im| ≤ a) (u w : ℝ)
    (hw0 : 0 ≤ w) (hw : w ≤ Real.exp (lam * u ^ 2)) :
    ‖(w : ℂ) * Kker u * Complex.exp (I * z * u)‖ ≤
      M * Dq lam (1 / 2 + a) (2 * Rc) u := by
  have hb := flow_integrand_bound hlam hK hz u
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at hb
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hw (norm_nonneg _)) (norm_nonneg _)).trans hb

theorem integrable_coshStep_integrand {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (n : ℕ) (z : ℂ) :
    Integrable (fun u : ℝ =>
      (coshStepWeight lam n u : ℂ) * Kker u * Complex.exp (I * z * u)) := by
  obtain ⟨M, _, hK⟩ := Kker_bound
  have hd : Integrable (fun u => M * Dq lam (1 / 2 + |z.im|) (2 * Rc) u) :=
    (integrable_Dq hlam0 hlam1 (by positivity) (by have := Rc_pos; positivity)).const_mul M
  apply hd.mono'
  · exact (((Complex.continuous_ofReal.comp (continuous_coshStepWeight lam n)).mul
      continuous_Kker).mul (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  · exact Eventually.of_forall fun u => weighted_flow_bound hlam0 hK le_rfl u _
      (coshStepWeight_nonneg lam n u) (coshStepWeight_bounds hlam0 n u).2

/-- The finite symmetric-shift kernels converge to the actual heat-warped fiber. -/
theorem tendsto_coshStep {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (z : ℂ) :
    Tendsto (fun n => coshStep lam n z) atTop (𝓝 (flowStage lam z)) := by
  obtain ⟨M, _, hK⟩ := Kker_bound
  apply tendsto_integral_of_dominated_convergence
    (fun u => M * Dq lam (1 / 2 + |z.im|) (2 * Rc) u)
  · intro n
    exact (integrable_coshStep_integrand hlam0 hlam1 n z).aestronglyMeasurable
  · exact (integrable_Dq hlam0 hlam1 (by positivity)
      (by have := Rc_pos; positivity)).const_mul M
  · intro n
    exact Eventually.of_forall fun u => weighted_flow_bound hlam0 hK le_rfl u _
      (coshStepWeight_nonneg lam n u) (coshStepWeight_bounds hlam0 n u).2
  · filter_upwards with u
    exact (((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_coshStepWeight hlam0 u)).mul_const (Kker u)).mul_const _

/-- Convergence is uniform on each compact set of complex heights. -/
theorem tendstoUniformlyOn_coshStep {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (coshStep lam) (flowStage lam) atTop K := by
  obtain ⟨A₀, hA₀⟩ := hK.isBounded.exists_norm_le
  let A : ℝ := max A₀ 0
  have hA0 : 0 ≤ A := le_max_right _ _
  have hA : ∀ z ∈ K, |z.im| ≤ A := fun z hz =>
    (Complex.abs_im_le_norm z).trans ((hA₀ z hz).trans (le_max_left _ _))
  obtain ⟨M, hM, hKb⟩ := Kker_bound
  let J : ℕ → ℝ := fun n => ∫ u : ℝ,
    (Real.exp (lam * u ^ 2) - coshStepWeight lam n u) * ‖Kker u‖ * Real.exp (A * |u|)
  have hc : ∀ n, Continuous (fun u : ℝ =>
      (Real.exp (lam * u ^ 2) - coshStepWeight lam n u) * ‖Kker u‖ *
        Real.exp (A * |u|)) := by
    intro n
    exact ((((Real.continuous_exp.comp (by fun_prop)).sub
      (continuous_coshStepWeight lam n)).mul continuous_Kker.norm).mul
      (Real.continuous_exp.comp (by fun_prop)))
  have hd : Integrable (fun u => M * Dq lam (1 / 2 + A) (2 * Rc) u) :=
    (integrable_Dq hlam0 hlam1 (by positivity) (by have := Rc_pos; positivity)).const_mul M
  have hb : ∀ n u, ‖(Real.exp (lam * u ^ 2) - coshStepWeight lam n u) * ‖Kker u‖ *
      Real.exp (A * |u|)‖ ≤ M * Dq lam (1 / 2 + A) (2 * Rc) u := by
    intro n u
    have hw0 := sub_nonneg.mpr (coshStepWeight_bounds hlam0 n u).2
    have hw1 := coshStepWeight_nonneg lam n u
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      (Real.exp (lam * u ^ 2) - coshStepWeight lam n u) * ‖Kker u‖ * Real.exp (A * |u|)
          ≤ Real.exp (lam * u ^ 2) * (M * Dabs (1 / 2) (2 * Rc) u) *
            Real.exp (A * |u|) := by
              gcongr
              · exact sub_le_self _ hw1
              · exact hKb u
      _ = M * (Real.exp (lam * u ^ 2) *
          (Dabs (1 / 2) (2 * Rc) u * Real.exp (A * |u|))) := by ring
      _ = M * Dq lam (1 / 2 + A) (2 * Rc) u := by rw [Dabs_mul_exp]; rfl
  have hJi : ∀ n, Integrable (fun u : ℝ =>
      (Real.exp (lam * u ^ 2) - coshStepWeight lam n u) * ‖Kker u‖ *
        Real.exp (A * |u|)) := fun n =>
    hd.mono' (hc n).aestronglyMeasurable (Eventually.of_forall (hb n))
  have hJlim : Tendsto J atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence
      (F := fun n u => (Real.exp (lam * u ^ 2) - coshStepWeight lam n u) *
        ‖Kker u‖ * Real.exp (A * |u|)) (f := fun _ => (0 : ℝ))
      (fun u => M * Dq lam (1 / 2 + A) (2 * Rc) u)
      (fun n => (hc n).aestronglyMeasurable) hd
      (fun n => Eventually.of_forall (hb n)) (Eventually.of_forall fun u => ?_)
    · simpa [J] using ht
    · have ht0 : Tendsto (fun _ : ℕ => Real.exp (lam * u ^ 2)) atTop
          (𝓝 (Real.exp (lam * u ^ 2))) := tendsto_const_nhds
      simpa using ((ht0.sub (tendsto_coshStepWeight hlam0 u)).mul_const
        ‖Kker u‖).mul_const (Real.exp (A * |u|))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hJlim) ε hε] with n hn
  intro z hz
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (b := J n)
  · unfold flowStage coshStep
    rw [← integral_sub (integrable_flow_integrand hlam0 hlam1 z)
      (integrable_coshStep_integrand hlam0 hlam1 n z)]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _) (hJi n)
    filter_upwards with u
    have heq : (Real.exp (lam * u ^ 2) : ℂ) * Kker u * Complex.exp (I * z * u) -
        (coshStepWeight lam n u : ℂ) * Kker u * Complex.exp (I * z * u) =
        ((Real.exp (lam * u ^ 2) - coshStepWeight lam n u : ℝ) : ℂ) *
          Kker u * Complex.exp (I * z * u) := by push_cast; ring
    rw [heq, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (coshStepWeight_bounds hlam0 n u).2)]
    exact mul_le_mul_of_nonneg_left (norm_exp_I_mul_le (hA z hz) u)
      (mul_nonneg (sub_nonneg.mpr (coshStepWeight_bounds hlam0 n u).2) (norm_nonneg _))
  · rw [Real.dist_eq, sub_zero] at hn
    exact (le_abs_self _).trans_lt hn

theorem tendstoLocallyUniformly_coshStep {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    TendstoLocallyUniformly (coshStep lam) (flowStage lam) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  exact fun _ hK => tendstoUniformlyOn_coshStep hlam0 hlam1 hK

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.exp_symmetric_shift
#print axioms CriticalLinePhasor.XiKernel.flowStage_symmetric_shift
#print axioms CriticalLinePhasor.XiKernel.coshStepWeight_bounds
#print axioms CriticalLinePhasor.XiKernel.tendsto_coshStepWeight
#print axioms CriticalLinePhasor.XiKernel.tendsto_coshStep
#print axioms CriticalLinePhasor.XiKernel.tendstoLocallyUniformly_coshStep
