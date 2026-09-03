import RequestProject.XiTailStripBound

/-!
# Stage holomorphy and derivative transfer (Track A2 of `HP_SKELETON.md`)

The stage door `riemannHypothesis_of_stage_mass` asks, per channel point, for a stage
family whose values AND derivatives converge to those of `ξ`.  The compiled stages
`xiStage U z = 2∫₀^U Φ(u) cos(zu) du` converge to `xiIntegral` pointwise with a
doubly-exponential rate (`xiIntegral_sub_stage_bound`, `xiStage_tendsto_xiIntegral`).
This file supplies the derivative half:

* `sin_strip_bound` — `‖sin(zu)‖ ≤ e^{Yu}` on `|Im z| ≤ Y`, `u ≥ 0` (mirror of
  `cos_strip_bound`).
* `xiStage_hasDerivAt` / `xiStage_differentiable` — **each stage is entire in the
  frequency**: differentiation under the compact-extent integral, dominated on a unit ball
  by `|Φ(u)|·u·e^{Yu}`.
* `xiStage_sub_xiIntegral_norm_le` — the compiled squeeze made UNIFORM on a strip:
  `‖Ξ_n − Ξ‖ ≤ 16π²e^π·e^{−n}` for `n ≥ ⌈Y⌉₊ + 4` and `|Im z| ≤ Y`.
* `xiStage_tendstoLocallyUniformly` — hence locally uniform convergence on `ℂ`.
* `xiIntegral_differentiable` — the integral object is ENTIRE (Weierstrass).
* `deriv_xiStage_tendsto` — **derivative transfer**: `Ξ_n′(z) → Ξ′(z)` at every `z`.

With A1 (the identification `xiIntegral (spectralCoord s) = ξ(s)`), the family
`G n := xiStage n ∘ spectralCoord` fills clause (ii) of the stage door.  Nothing here
touches the zero set.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology MeasureTheory

noncomputable section

namespace CriticalLinePhasor.ThetaWronskianSuzukiGram

/-- **The strip bound on the sine**: mirror of `cos_strip_bound`. -/
theorem sin_strip_bound {z : ℂ} {u Y : ℝ} (hu : 0 ≤ u) (hz : |z.im| ≤ Y) :
    ‖Complex.sin (z * u)‖ ≤ Real.exp (Y * u) := by
  have hb := abs_le.mp hz
  have hA : ‖Complex.exp (-(z * ↑u * Complex.I))‖ ≤ Real.exp (Y * u) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (-(z * ↑u * Complex.I)).re = z.im * u := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    nlinarith [hb.1, hb.2]
  have hB : ‖Complex.exp (z * ↑u * Complex.I)‖ ≤ Real.exp (Y * u) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (z * ↑u * Complex.I).re = -(z.im * u) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    nlinarith [hb.1, hb.2]
  rw [Complex.sin]
  simp only [neg_mul]
  rw [norm_div, norm_mul, Complex.norm_I, mul_one]
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2n]
  have hsum := norm_sub_le (Complex.exp (-(z * ↑u * Complex.I)))
    (Complex.exp (z * ↑u * Complex.I))
  linarith

/-- The stage integrand differentiated in the frequency. -/
theorem xiStage_integrand_hasDerivAt (u : ℝ) (z : ℂ) :
    HasDerivAt (fun y : ℂ => (riemannXiKernel u : ℂ) * Complex.cos (y * u))
      ((riemannXiKernel u : ℂ) * (-Complex.sin (z * u) * u)) z := by
  have h := (((hasDerivAt_id' z).mul_const (u : ℂ)).ccos).const_mul (riemannXiKernel u : ℂ)
  exact h.congr_deriv (by ring)

theorem xiStage_integrand_continuousOn (U : ℝ) (z : ℂ) :
    ContinuousOn (fun u : ℝ => (riemannXiKernel u : ℂ) * Complex.cos (z * u))
      (Set.Ioc 0 U) := by
  apply ContinuousOn.mul
  · exact Complex.continuous_ofReal.comp_continuousOn
      (riemannXiKernel_continuousOn.mono (fun x hx => hx.1.le))
  · exact (Complex.continuous_cos.comp
      (continuous_const.mul Complex.continuous_ofReal)).continuousOn

theorem xiStage_derivIntegrand_continuousOn (U : ℝ) (z : ℂ) :
    ContinuousOn (fun u : ℝ => (riemannXiKernel u : ℂ) * (-Complex.sin (z * u) * u))
      (Set.Ioc 0 U) := by
  apply ContinuousOn.mul
  · exact Complex.continuous_ofReal.comp_continuousOn
      (riemannXiKernel_continuousOn.mono (fun x hx => hx.1.le))
  · exact ((Complex.continuous_sin.comp
      (continuous_const.mul Complex.continuous_ofReal)).neg.mul
        Complex.continuous_ofReal).continuousOn

/-- **Each stage is entire in the frequency**: differentiation under the compact-extent
integral, dominated on the unit ball about `z₀` by `|Φ(u)|·u·e^{(|Im z₀|+1)u}`. -/
theorem xiStage_hasDerivAt (U : ℝ) (z₀ : ℂ) :
    HasDerivAt (xiStage U)
      (2 * ∫ u in Set.Ioc 0 U, (riemannXiKernel u : ℂ) * (-Complex.sin (z₀ * u) * u)) z₀ := by
  set Y : ℝ := |z₀.im| + 1 with hY
  have hY0 : 0 ≤ Y := by positivity
  have hball : ∀ z ∈ Metric.ball z₀ 1, |z.im| ≤ Y := by
    intro z hz
    have h1 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
      have := Complex.abs_im_le_norm (z - z₀)
      simpa [Complex.sub_im] using this
    have h2 : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
    have h3 := abs_sub_abs_le_abs_sub z.im z₀.im
    linarith
  have hbound_int : Integrable (fun u : ℝ => |riemannXiKernel u| * (Real.exp (Y * u) * u))
      (volume.restrict (Set.Ioc 0 U)) := by
    have hc : ContinuousOn (fun u : ℝ => |riemannXiKernel u| * (Real.exp (Y * u) * u))
        (Set.Icc 0 U) := by
      apply ContinuousOn.mul
      · exact (riemannXiKernel_continuousOn.mono (fun x hx => hx.1)).abs
      · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
          continuous_id).continuousOn
    exact (hc.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hdom : ∀ᵐ u ∂(volume.restrict (Set.Ioc 0 U)), ∀ z ∈ Metric.ball z₀ 1,
      ‖(riemannXiKernel u : ℂ) * (-Complex.sin (z * u) * u)‖
        ≤ |riemannXiKernel u| * (Real.exp (Y * u) * u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu z hz
    have hsin := sin_strip_bound hu.1.le (hball z hz)
    have hK : ‖(riemannXiKernel u : ℂ)‖ = |riemannXiKernel u| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have hu' : ‖(u : ℂ)‖ = u := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
    rw [norm_mul, norm_mul, norm_neg, hK, hu']
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact mul_le_mul_of_nonneg_right hsin hu.1.le
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc 0 U))
    (F := fun z u => (riemannXiKernel u : ℂ) * Complex.cos (z * u))
    (F' := fun z u => (riemannXiKernel u : ℂ) * (-Complex.sin (z * u) * u))
    (bound := fun u : ℝ => |riemannXiKernel u| * (Real.exp (Y * u) * u))
    (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall fun z =>
      (xiStage_integrand_continuousOn U z).aestronglyMeasurable measurableSet_Ioc)
    (xiIntegrand_integrableOn_Ioc U z₀)
    ((xiStage_derivIntegrand_continuousOn U z₀).aestronglyMeasurable measurableSet_Ioc)
    hdom hbound_int
    (Filter.Eventually.of_forall fun u z _ => xiStage_integrand_hasDerivAt u z)
  unfold xiStage
  exact hmain.2.const_mul (2 : ℂ)

theorem xiStage_differentiable (U : ℝ) : Differentiable ℂ (xiStage U) :=
  fun z => (xiStage_hasDerivAt U z).differentiableAt

/-- **The squeeze, uniform on a strip**: for `n ≥ ⌈Y⌉₊ + 4` and `|Im z| ≤ Y`,
`‖Ξ_n(z) − Ξ(z)‖ ≤ 16π²e^π·e^{−n}`.  The body of `xiStage_tendsto_xiIntegral` with the
strip height decoupled from the point. -/
theorem xiStage_sub_xiIntegral_norm_le {Y : ℝ} (hY0 : 0 ≤ Y) {n : ℕ} (hn : ⌈Y⌉₊ + 4 ≤ n)
    {z : ℂ} (hz : |z.im| ≤ Y) :
    ‖xiStage n z - xiIntegral z‖
      ≤ (16 * Real.pi ^ 2 * Real.exp Real.pi) * Real.exp (-(n : ℝ)) := by
  have hYle : Y ≤ (n : ℝ) := by
    have h1 : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil Y
    have h2 : ((⌈Y⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (by omega : ⌈Y⌉₊ ≤ ⌈Y⌉₊ + 4) hn
    linarith
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast le_trans (by omega : 4 ≤ ⌈Y⌉₊ + 4) hn
  have hexp2 : (1 + (n : ℝ)) ^ 2 ≤ Real.exp (2 * (n : ℝ)) := by
    have h1 : 1 + (n : ℝ) ≤ Real.exp (n : ℝ) := by
      have := Real.add_one_le_exp ((n : ℝ))
      linarith
    have h2 : Real.exp (2 * (n : ℝ)) = Real.exp (n : ℝ) * Real.exp (n : ℝ) := by
      rw [← Real.exp_add]
      ring_nf
    nlinarith [Nat.cast_nonneg (α := ℝ) n, Real.exp_pos ((n : ℝ))]
  have hπ := Real.pi_gt_three
  have hcev : 9 / 2 + Y + 1 ≤ 2 * Real.pi * Real.exp (2 * (n : ℝ)) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hAev : Real.exp ((9 / 2 + Y) * (n : ℝ)) * Real.exp (-Real.pi * Real.exp (2 * (n : ℝ)))
      ≤ Real.exp (-(n : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hπ.le (sq_nonneg (1 + (n : ℝ))),
      Nat.cast_nonneg (α := ℝ) n]
  have hc : 9 / 2 + Y < 2 * Real.pi * Real.exp (2 * (n : ℝ)) := by linarith
  have hdiff := xiIntegral_sub_stage_bound (Nat.cast_nonneg n) hY0 hc hz
  have hc1 : (1 : ℝ) ≤ 2 * Real.pi * Real.exp (2 * (n : ℝ)) - 9 / 2 - Y := by linarith
  have hA0 : (0 : ℝ) ≤ 8 * Real.pi ^ 2 * Real.exp Real.pi
      * Real.exp ((9 / 2 + Y) * (n : ℝ))
      * Real.exp (-Real.pi * Real.exp (2 * (n : ℝ))) := by positivity
  have hdivle := div_le_self hA0 hc1
  have hAle : 8 * Real.pi ^ 2 * Real.exp Real.pi
        * Real.exp ((9 / 2 + Y) * (n : ℝ))
        * Real.exp (-Real.pi * Real.exp (2 * (n : ℝ)))
      ≤ 8 * Real.pi ^ 2 * Real.exp Real.pi * Real.exp (-(n : ℝ)) := by
    calc 8 * Real.pi ^ 2 * Real.exp Real.pi
          * Real.exp ((9 / 2 + Y) * (n : ℝ))
          * Real.exp (-Real.pi * Real.exp (2 * (n : ℝ)))
        = (8 * Real.pi ^ 2 * Real.exp Real.pi)
          * (Real.exp ((9 / 2 + Y) * (n : ℝ))
              * Real.exp (-Real.pi * Real.exp (2 * (n : ℝ)))) := by ring
      _ ≤ (8 * Real.pi ^ 2 * Real.exp Real.pi) * Real.exp (-(n : ℝ)) :=
          mul_le_mul_of_nonneg_left hAev (by positivity)
  rw [norm_sub_rev]
  calc ‖xiIntegral z - xiStage n z‖ ≤ _ := hdiff
    _ ≤ 2 * (8 * Real.pi ^ 2 * Real.exp Real.pi * Real.exp (-(n : ℝ))) := by
        linarith [hdivle, hAle]
    _ = (16 * Real.pi ^ 2 * Real.exp Real.pi) * Real.exp (-(n : ℝ)) := by ring

/-- The explicit rate tends to zero. -/
theorem rate_tendsto_zero :
    Tendsto (fun n : ℕ => (16 * Real.pi ^ 2 * Real.exp Real.pi) * Real.exp (-(n : ℝ)))
      atTop (nhds 0) := by
  have hfun' : ∀ n : ℕ, Real.exp (-1 : ℝ) ^ n = Real.exp (-(n : ℝ)) := by
    intro n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hr0 : (0 : ℝ) ≤ Real.exp (-1 : ℝ) := (Real.exp_pos _).le
  have hr1 : Real.exp (-1 : ℝ) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have h1 := h0.const_mul (16 * Real.pi ^ 2 * Real.exp Real.pi)
  rw [mul_zero] at h1
  exact h1.congr fun n => by rw [hfun' n]

/-- **Locally uniform convergence of the stages on `ℂ`.** -/
theorem xiStage_tendstoLocallyUniformly :
    TendstoLocallyUniformly (fun n : ℕ => xiStage n) xiIntegral atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  set Y : ℝ := |x.im| + 1 with hY
  have hY0 : 0 ≤ Y := by positivity
  refine ⟨{y : ℂ | |y.im| < Y}, ?_, ?_⟩
  · have hopen : IsOpen {y : ℂ | |y.im| < Y} :=
      isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
    refine hopen.mem_nhds ?_
    show |x.im| < Y
    rw [hY]
    linarith
  · have hev := rate_tendsto_zero.eventually (gt_mem_nhds hε)
    filter_upwards [hev, Filter.eventually_ge_atTop (⌈Y⌉₊ + 4)] with n hnε hn y hy
    have hy' : |y.im| < Y := hy
    rw [dist_eq_norm, norm_sub_rev]
    calc ‖xiStage n y - xiIntegral y‖
        ≤ (16 * Real.pi ^ 2 * Real.exp Real.pi) * Real.exp (-(n : ℝ)) :=
          xiStage_sub_xiIntegral_norm_le hY0 hn hy'.le
      _ < ε := Set.mem_Iio.mp hnε

theorem xiStage_tendstoLocallyUniformlyOn_univ :
    TendstoLocallyUniformlyOn (fun n : ℕ => xiStage n) xiIntegral atTop Set.univ :=
  tendstoLocallyUniformlyOn_univ.mpr xiStage_tendstoLocallyUniformly

/-- **The integral object is entire** (Weierstrass: a locally uniform limit of entire
stages). -/
theorem xiIntegral_differentiable : Differentiable ℂ xiIntegral := by
  have h := xiStage_tendstoLocallyUniformlyOn_univ.differentiableOn
    (Filter.Eventually.of_forall fun n => (xiStage_differentiable n).differentiableOn)
    isOpen_univ
  exact differentiableOn_univ.mp h

/-- **Derivative transfer**: the stage derivatives converge to the derivative of the
integral object at every frequency. -/
theorem deriv_xiStage_tendsto (z : ℂ) :
    Tendsto (fun n : ℕ => deriv (xiStage n) z) atTop (nhds (deriv xiIntegral z)) := by
  have h := xiStage_tendstoLocallyUniformlyOn_univ.deriv
    (Filter.Eventually.of_forall fun n => (xiStage_differentiable n).differentiableOn)
    isOpen_univ
  exact h.tendsto_at (Set.mem_univ z)

end CriticalLinePhasor.ThetaWronskianSuzukiGram

#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.sin_strip_bound
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiStage_hasDerivAt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiStage_sub_xiIntegral_norm_le
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiStage_tendstoLocallyUniformly
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiIntegral_differentiable
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.deriv_xiStage_tendsto
