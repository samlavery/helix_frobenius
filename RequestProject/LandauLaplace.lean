import Mathlib

/-!
# Laplace integrals: explicit power series, and Landau's theorem for non-negative weights (ledger 917)

* `hasFPowerSeriesOnBall_laplace` — if `w·e^{−σy}` is integrable on `S` for every `σ` within `ρ` of `Re z₁`, the
  Laplace integral `z ↦ ∫_S w(y) e^{−zy} dy` has the power series `Σ_k c_k (z − z₁)^k` on the ball of radius `ρ`,
  `c_k = ((−1)^k/k!) ∫_S w(y) y^k e^{−z₁y} dy`.
* `landau` — a Laplace integral of a weight that is non-negative on `[y₀, ∞)` (`y₀ ≥ 0`) cannot be continued
  analytically across its real abscissa of convergence: if it agrees on `Re z > σ₁` with a function analytic on the
  half-strip `{σ₀ < Re z, |Im z| < r}` together with the half-plane `{σ₁ < Re z}`, then it converges for every real
  abscissa `σ > σ₀`.

No `sorry`, no `axiom`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped Nat NNReal ENNReal

noncomputable section

namespace LandauLaplace

/-- The Laplace integral of a real weight `w` over a set `S`. -/
def laplace (S : Set ℝ) (w : ℝ → ℝ) (z : ℂ) : ℂ := ∫ y in S, (w y : ℂ) * cexp (-z * y)

/-- Its Taylor coefficients at `z₁`. -/
def coeff (S : Set ℝ) (w : ℝ → ℝ) (z₁ : ℂ) (k : ℕ) : ℂ :=
  ((-1 : ℂ) ^ k / k !) * ∫ y in S, (w y : ℂ) * (y : ℂ) ^ k * cexp (-z₁ * y)

lemma exp_mul_abs_le (a y : ℝ) :
    Real.exp (a * |y|) ≤ Real.exp (a * y) + Real.exp (-(a * y)) := by
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h]
    linarith [Real.exp_pos (-(a * y))]
  · rw [abs_of_nonpos h, show a * -y = -(a * y) by ring]
    linarith [Real.exp_pos (a * y)]

lemma norm_cexp_neg_mul_ofReal (z : ℂ) (y : ℝ) : ‖cexp (-z * y)‖ = Real.exp (-z.re * y) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- The real exponential series, as a `HasSum`. -/
lemma hasSum_real_exp (x : ℝ) : HasSum (fun n : ℕ => x ^ n / n !) (Real.exp x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rwa [← Real.exp_eq_exp_ℝ] at h

/-- The complex exponential series, as a `HasSum`. -/
lemma hasSum_complex_exp (x : ℂ) : HasSum (fun n : ℕ => x ^ n / n !) (cexp x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) x
  rwa [← Complex.exp_eq_exp_ℂ] at h

section PowerSeries

variable (S : Set ℝ) (w : ℝ → ℝ) (z₁ : ℂ) {ρ : ℝ}

/-- A weight integrable against some exponential is a.e.-strongly measurable. -/
lemma aestronglyMeasurable_weight (σ : ℝ)
    (h : IntegrableOn (fun y => w y * Real.exp (-σ * y)) S) :
    AEStronglyMeasurable w (volume.restrict S) := by
  have h2 : AEStronglyMeasurable (fun y : ℝ => Real.exp (σ * y)) (volume.restrict S) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  refine (h.aestronglyMeasurable.mul h2).congr (Eventually.of_forall fun y => ?_)
  simp only [Pi.mul_apply]
  rw [mul_assoc, ← Real.exp_add, show -σ * y + σ * y = 0 by ring, Real.exp_zero, mul_one]

/-- The dominating series: `|w| e^{−σy} (a|y|)^k/k!` sums to `|w| e^{−σy} e^{a|y|}`, which is integrable
whenever the weight is integrable at `σ ± a`. -/
lemma integrable_bound_sum (σ a : ℝ)
    (h₁ : IntegrableOn (fun y => w y * Real.exp (-(σ - a) * y)) S)
    (h₂ : IntegrableOn (fun y => w y * Real.exp (-(σ + a) * y)) S) :
    IntegrableOn (fun y => |w y| * Real.exp (-σ * y) * Real.exp (a * |y|)) S := by
  have hsum : IntegrableOn (fun y => |w y * Real.exp (-(σ - a) * y)| + |w y * Real.exp (-(σ + a) * y)|) S :=
    h₁.abs.add h₂.abs
  refine hsum.mono' ?_ ?_
  · have hm := aestronglyMeasurable_weight S w (σ - a) h₁
    have h3 : AEStronglyMeasurable (fun y : ℝ => Real.exp (-σ * y)) (volume.restrict S) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    have h4 : AEStronglyMeasurable (fun y : ℝ => Real.exp (a * |y|)) (volume.restrict S) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable
    refine ((hm.norm.mul h3).mul h4).congr (Eventually.of_forall fun y => ?_)
    simp [Real.norm_eq_abs]
  · refine Eventually.of_forall fun y => ?_
    have hb := exp_mul_abs_le a y
    have hw : 0 ≤ |w y| := abs_nonneg _
    have e1 : |w y * Real.exp (-(σ - a) * y)| = |w y| * (Real.exp (-σ * y) * Real.exp (a * y)) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      congr 2
      ring
    have e2 : |w y * Real.exp (-(σ + a) * y)| = |w y| * (Real.exp (-σ * y) * Real.exp (-(a * y))) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      congr 2
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), e1, e2]
    have hσ : 0 < Real.exp (-σ * y) := Real.exp_pos _
    nlinarith [mul_le_mul_of_nonneg_left hb (mul_nonneg hw hσ.le)]

/-- The series expansion at an offset `v` with `‖v‖ < ρ`, and the summability of the real dominating integrals. -/
lemma laplace_series (hρ : 0 < ρ)
    (hint : ∀ t : ℝ, |t| < ρ → IntegrableOn (fun y => w y * Real.exp (-(z₁.re + t) * y)) S)
    (v : ℂ) (hv : ‖v‖ < ρ) :
    HasSum (fun k : ℕ => coeff S w z₁ k * v ^ k) (laplace S w (z₁ + v)) ∧
    Summable (fun k : ℕ => ∫ y in S, |w y| * Real.exp (-z₁.re * y) * ((‖v‖ * |y|) ^ k / k !)) := by
  set a := ‖v‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg v
  have hm : AEStronglyMeasurable w (volume.restrict S) :=
    aestronglyMeasurable_weight S w (z₁.re + 0) (hint 0 (by simpa using hρ))
  have hbint := integrable_bound_sum S w z₁.re a
    (by simpa [sub_eq_add_neg] using hint (-a) (by rw [abs_neg, abs_of_nonneg ha0]; exact hv))
    (hint a (by rw [abs_of_nonneg ha0]; exact hv))
  set bound : ℕ → ℝ → ℝ := fun k y => |w y| * Real.exp (-z₁.re * y) * ((a * |y|) ^ k / k !)
    with hbound
  have hbsum : ∀ y, HasSum (fun k => bound k y) (|w y| * Real.exp (-z₁.re * y) * Real.exp (a * |y|)) :=
    fun y => (hasSum_real_exp (a * |y|)).mul_left _
  have hbmeas : ∀ k, AEStronglyMeasurable (bound k) (volume.restrict S) := by
    intro k
    have h3 : AEStronglyMeasurable (fun y : ℝ => Real.exp (-z₁.re * y)) (volume.restrict S) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    have h4 : AEStronglyMeasurable (fun y : ℝ => (a * |y|) ^ k / k !) (volume.restrict S) :=
      (((continuous_const.mul continuous_abs).pow k).div_const _).aestronglyMeasurable
    refine ((hm.norm.mul h3).mul h4).congr (Eventually.of_forall fun y => ?_)
    simp [hbound, Real.norm_eq_abs]
  have hbint' : Integrable (fun y => ∑' k, bound k y) (volume.restrict S) := by
    refine hbint.congr (Eventually.of_forall fun y => ?_)
    exact (hbsum y).tsum_eq.symm
  set F : ℕ → ℝ → ℂ := fun k y => (w y : ℂ) * cexp (-z₁ * y) * ((-v * y) ^ k / k !) with hF
  have hFsum : ∀ y, HasSum (fun k => F k y) ((w y : ℂ) * cexp (-(z₁ + v) * y)) := by
    intro y
    have h := (hasSum_complex_exp (-v * y)).mul_left ((w y : ℂ) * cexp (-z₁ * y))
    convert h using 1
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hFbound : ∀ k y, ‖F k y‖ = bound k y := by
    intro k y
    simp only [hF, hbound, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      norm_cexp_neg_mul_ofReal, Complex.norm_natCast, norm_neg, ha]
  have hFmeas : ∀ k, AEStronglyMeasurable (F k) (volume.restrict S) := by
    intro k
    have h1 : AEStronglyMeasurable (fun y : ℝ => (w y : ℂ)) (volume.restrict S) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hm
    have h2 : AEStronglyMeasurable (fun y : ℝ => cexp (-z₁ * y) * ((-v * y) ^ k / k !))
        (volume.restrict S) := by
      apply Continuous.aestronglyMeasurable
      fun_prop
    refine (h1.mul h2).congr (Eventually.of_forall fun y => ?_)
    simp [hF, mul_assoc]
  have hsumI := hasSum_integral_of_dominated_convergence bound hFmeas
    (fun k => Eventually.of_forall fun y => (hFbound k y).le)
    (Eventually.of_forall fun y => (hbsum y).summable) hbint' (Eventually.of_forall hFsum)
  have hsumR := hasSum_integral_of_dominated_convergence bound hbmeas
    (fun k => Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [hbound]; positivity)])
    (Eventually.of_forall fun y => (hbsum y).summable) hbint' (Eventually.of_forall hbsum)
  refine ⟨?_, hsumR.summable⟩
  have hterm : ∀ k, ∫ y in S, F k y = coeff S w z₁ k * v ^ k := by
    intro k
    have : (fun y => F k y) =
        fun y => ((-1 : ℂ) ^ k / k ! * v ^ k) * ((w y : ℂ) * (y : ℂ) ^ k * cexp (-z₁ * y)) := by
      funext y
      simp only [hF]
      rw [neg_mul, neg_pow, mul_pow]
      ring
    rw [this, integral_const_mul, coeff]
    ring
  simp only [hterm] at hsumI
  simpa [laplace] using hsumI

/-- **The Laplace integral has an explicit power series** on the ball of radius `ρ` around `z₁`. -/
theorem hasFPowerSeriesOnBall_laplace (hρ : 0 < ρ)
    (hint : ∀ t : ℝ, |t| < ρ → IntegrableOn (fun y => w y * Real.exp (-(z₁.re + t) * y)) S) :
    HasFPowerSeriesOnBall (laplace S w) (FormalMultilinearSeries.ofScalars ℂ (coeff S w z₁)) z₁
      (ENNReal.ofReal ρ) := by
  refine
    { r_le := ?_
      r_pos := ENNReal.ofReal_pos.mpr hρ
      hasSum := ?_ }
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    have hr' : (r : ℝ) < ρ := by
      rw [← ENNReal.ofReal_coe_nnreal] at hr
      exact (ENNReal.ofReal_lt_ofReal_iff hρ).1 hr
    refine FormalMultilinearSeries.le_radius_of_summable _ ?_
    have hs := (laplace_series S w z₁ hρ hint (r : ℂ) (by simpa using hr')).2
    refine hs.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    rw [FormalMultilinearSeries.ofScalars_norm, coeff, norm_mul, norm_div, norm_pow, norm_neg,
      norm_one, one_pow, Complex.norm_natCast]
    have hnorm : ∀ y : ℝ, ‖(w y : ℂ) * (y : ℂ) ^ n * cexp (-z₁ * y)‖
        = |w y| * |y| ^ n * Real.exp (-z₁.re * y) := by
      intro y
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, norm_cexp_neg_mul_ofReal]
    have hle := norm_integral_le_integral_norm
      (μ := volume.restrict S) (fun y => (w y : ℂ) * (y : ℂ) ^ n * cexp (-z₁ * y))
    simp only [hnorm] at hle
    have hr0 : ‖((r : ℝ) : ℂ)‖ = (r : ℝ) := by simp
    simp only [hr0]
    calc 1 / (n ! : ℝ) * ‖∫ y in S, (w y : ℂ) * (y : ℂ) ^ n * cexp (-z₁ * y)‖ * (r : ℝ) ^ n
        ≤ 1 / (n ! : ℝ) * (∫ y in S, |w y| * |y| ^ n * Real.exp (-z₁.re * y)) * (r : ℝ) ^ n := by
          gcongr
      _ = (∫ y in S, |w y| * |y| ^ n * Real.exp (-z₁.re * y)) * ((r : ℝ) ^ n / n !) := by ring
      _ = ∫ y in S, |w y| * |y| ^ n * Real.exp (-z₁.re * y) * ((r : ℝ) ^ n / n !) :=
          (integral_mul_const _ _).symm
      _ = ∫ y in S, |w y| * Real.exp (-z₁.re * y) * (((r : ℝ) * |y|) ^ n / n !) := by
          congr 1
          funext y
          rw [mul_pow]
          ring
  · intro v hv
    have hv' : ‖v‖ < ρ := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm] at hv
      exact (ENNReal.ofReal_lt_ofReal_iff hρ).1 hv
    rw [FormalMultilinearSeries.ofScalars_apply_eq']
    simpa [smul_eq_mul] using (laplace_series S w z₁ hρ hint v hv').1

/-- **Analyticity on the half-plane of convergence.** -/
theorem differentiableOn_laplace (s : ℝ)
    (h : ∀ σ, s < σ → IntegrableOn (fun y => w y * Real.exp (-σ * y)) S) :
    DifferentiableOn ℂ (laplace S w) {z : ℂ | s < z.re} := by
  intro z hz
  have hρ : 0 < z.re - s := sub_pos.mpr hz
  have hps := hasFPowerSeriesOnBall_laplace S w z hρ fun t ht =>
    h _ (by have := neg_abs_le t; linarith)
  exact hps.analyticAt.differentiableAt.differentiableWithinAt

end PowerSeries

section Landau

variable (g : ℝ → ℝ) (y₀ : ℝ)

/-- Raising the abscissa preserves integrability for a weight that is non-negative on `[y₀, ∞)`, `y₀ ≥ 0`. -/
lemma integrableOn_mono_sigma (hy₀ : 0 ≤ y₀) (hg : ∀ y ∈ Ici y₀, 0 ≤ g y) {σ σ' : ℝ} (h : σ ≤ σ')
    (hi : IntegrableOn (fun y => g y * Real.exp (-σ * y)) (Ici y₀)) :
    IntegrableOn (fun y => g y * Real.exp (-σ' * y)) (Ici y₀) := by
  have hm := aestronglyMeasurable_weight (Ici y₀) g σ hi
  refine hi.mono' ?_ ?_
  · exact hm.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun y hy => ?_)
    have hy' : 0 ≤ y := le_trans hy₀ hy
    have hgy := hg y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hgy (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hgy

/-- The domain `{σ₀ < Re z, |Im z| < r} ∪ {σ₁ < Re z}`. -/
def domain (σ₀ σ₁ r : ℝ) : Set ℂ := {z | σ₀ < z.re ∧ |z.im| < r} ∪ {z | σ₁ < z.re}

lemma isOpen_domain (σ₀ σ₁ r : ℝ) : IsOpen (domain σ₀ σ₁ r) := by
  refine IsOpen.union ?_ ?_
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  · exact isOpen_lt continuous_const Complex.continuous_re

lemma isPreconnected_domain {σ₀ σ₁ r : ℝ} (h01 : σ₀ ≤ σ₁) (hr : 0 < r) :
    IsPreconnected (domain σ₀ σ₁ r) := by
  have hc1 : Convex ℝ {z : ℂ | σ₀ < z.re ∧ |z.im| < r} := by
    have e : {z : ℂ | σ₀ < z.re ∧ |z.im| < r} =
        {z : ℂ | σ₀ < z.re} ∩ ({z : ℂ | -r < z.im} ∩ {z : ℂ | z.im < r}) := by
      ext z
      simp [abs_lt]
    rw [e]
    exact (convex_halfSpace_gt Complex.reLm.isLinear σ₀).inter
      ((convex_halfSpace_gt Complex.imLm.isLinear (-r)).inter
        (convex_halfSpace_lt Complex.imLm.isLinear r))
  have hc2 : Convex ℝ {z : ℂ | σ₁ < z.re} := convex_halfSpace_gt Complex.reLm.isLinear σ₁
  refine hc1.isPreconnected.union ((σ₁ + 1 : ℝ) : ℂ) ?_ ?_ hc2.isPreconnected
  · simp only [mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im, abs_zero]
    exact ⟨by linarith, hr⟩
  · simp only [mem_ofPred_eq, Complex.ofReal_re]
    linarith

/-- **The Tonelli step**: summable non-negative moments give integrability at the shifted abscissa. -/
lemma integrableOn_of_summable_moments (hy₀ : 0 ≤ y₀) (hg : ∀ y ∈ Ici y₀, 0 ≤ g y) (σ b : ℝ)
    (hb : 0 ≤ b) (hm : AEStronglyMeasurable g (volume.restrict (Ici y₀)))
    (hterm : ∀ n : ℕ, IntegrableOn (fun y => g y * Real.exp (-σ * y) * ((b * y) ^ n / n !)) (Ici y₀))
    (hsum : Summable (fun n : ℕ => ∫ y in Ici y₀, g y * Real.exp (-σ * y) * ((b * y) ^ n / n !))) :
    IntegrableOn (fun y => g y * Real.exp (-(σ - b) * y)) (Ici y₀) := by
  have hnn : ∀ n : ℕ, ∀ y ∈ Ici y₀, 0 ≤ g y * Real.exp (-σ * y) * ((b * y) ^ n / n !) := by
    intro n y hy
    have hy' : 0 ≤ y := le_trans hy₀ hy
    have := hg y hy
    positivity
  have hpt : ∀ y, HasSum (fun n : ℕ => g y * Real.exp (-σ * y) * ((b * y) ^ n / n !))
      (g y * Real.exp (-(σ - b) * y)) := by
    intro y
    have h := (hasSum_real_exp (b * y)).mul_left (g y * Real.exp (-σ * y))
    convert h using 1
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hmeas : AEStronglyMeasurable (fun y => g y * Real.exp (-(σ - b) * y)) (volume.restrict (Ici y₀)) :=
    hm.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  have hf0 : 0 ≤ᵐ[volume.restrict (Ici y₀)] fun y => g y * Real.exp (-(σ - b) * y) :=
    (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun y hy =>
      mul_nonneg (hg y hy) (Real.exp_pos _).le)
  refine ⟨hmeas, (hasFiniteIntegral_iff_ofReal hf0).2 ?_⟩
  calc ∫⁻ y in Ici y₀, ENNReal.ofReal (g y * Real.exp (-(σ - b) * y))
      = ∫⁻ y in Ici y₀, ∑' n, ENNReal.ofReal (g y * Real.exp (-σ * y) * ((b * y) ^ n / n !)) := by
        refine setLIntegral_congr_fun measurableSet_Ici (fun y hy => ?_)
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => hnn n y hy) (hpt y).summable, (hpt y).tsum_eq]
    _ = ∑' n, ∫⁻ y in Ici y₀, ENNReal.ofReal (g y * Real.exp (-σ * y) * ((b * y) ^ n / n !)) := by
        rw [lintegral_tsum]
        intro n
        exact (hterm n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    _ = ∑' n, ENNReal.ofReal (∫ y in Ici y₀, g y * Real.exp (-σ * y) * ((b * y) ^ n / n !)) := by
        congr 1
        funext n
        rw [ofReal_integral_eq_lintegral_ofReal (hterm n)]
        exact (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall (hnn n))
    _ = ENNReal.ofReal (∑' n, ∫ y in Ici y₀, g y * Real.exp (-σ * y) * ((b * y) ^ n / n !)) := by
        rw [ENNReal.ofReal_tsum_of_nonneg _ hsum]
        intro n
        exact setIntegral_nonneg measurableSet_Ici (hnn n)
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- **Landau's theorem (half-strip form).**  Let `g ≥ 0` on `[y₀, ∞)` (`y₀ ≥ 0`) with Laplace integral
convergent for every real abscissa `> σ₁`.  If the Laplace integral agrees on `Re z > σ₁` with a function
analytic on `{σ₀ < Re z, |Im z| < r} ∪ {σ₁ < Re z}`, then it converges at every real abscissa `> σ₀`. -/
theorem landau (hy₀ : 0 ≤ y₀) (hg : ∀ y ∈ Ici y₀, 0 ≤ g y) {σ₀ σ₁ r : ℝ} (h01 : σ₀ < σ₁)
    (hr : 0 < r)
    (hconv : ∀ σ, σ₁ < σ → IntegrableOn (fun y => g y * Real.exp (-σ * y)) (Ici y₀))
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (domain σ₀ σ₁ r))
    (hFL : ∀ z : ℂ, σ₁ < z.re → F z = laplace (Ici y₀) g z) :
    ∀ σ, σ₀ < σ → IntegrableOn (fun y => g y * Real.exp (-σ * y)) (Ici y₀) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨σb, hσb, hnot⟩ := hcon
  set T : Set ℝ := {σ | σ₀ < σ ∧ IntegrableOn (fun y => g y * Real.exp (-σ * y)) (Ici y₀)} with hT
  have hTne : (σ₁ + 1) ∈ T := ⟨by linarith, hconv _ (by linarith)⟩
  have hTbdd : BddBelow T := ⟨σ₀, fun σ hσ => hσ.1.le⟩
  set s := sInf T with hs
  have hTgt : ∀ σ ∈ T, σb < σ := by
    intro σ hσ
    by_contra hle
    push Not at hle
    exact hnot (integrableOn_mono_sigma g y₀ hy₀ hg hle hσ.2)
  have hsb : σb ≤ s := le_csInf ⟨_, hTne⟩ (fun σ hσ => (hTgt σ hσ).le)
  have hs0 : σ₀ < s := lt_of_lt_of_le hσb hsb
  have hs1 : s ≤ σ₁ := by
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    have hmem : σ₁ + δ / 2 ∈ T := ⟨by linarith, hconv _ (by linarith)⟩
    exact lt_of_le_of_lt (csInf_le hTbdd hmem) (by linarith)
  have hgood : ∀ σ, s < σ → IntegrableOn (fun y => g y * Real.exp (-σ * y)) (Ici y₀) := by
    intro σ hσ
    obtain ⟨t, ht, hts⟩ := exists_lt_of_csInf_lt ⟨_, hTne⟩ hσ
    exact integrableOn_mono_sigma g y₀ hy₀ hg hts.le ht.2
  have hm : AEStronglyMeasurable g (volume.restrict (Ici y₀)) :=
    aestronglyMeasurable_weight (Ici y₀) g (σ₁ + 1) (hconv _ (by linarith))
  set ε := min ((s - σ₀) / 4) (r / 4) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hε1 : ε ≤ (s - σ₀) / 4 := min_le_left _ _
  have hε2 : ε ≤ r / 4 := min_le_right _ _
  set z₁ : ℂ := ((s + ε : ℝ) : ℂ) with hz₁
  have hz₁re : z₁.re = s + ε := by simp [hz₁]
  -- the Laplace integral is analytic on `{s < Re}` and equals `F` on `domain s σ₁ r`
  have hLd : DifferentiableOn ℂ (laplace (Ici y₀) g) {z : ℂ | s < z.re} :=
    differentiableOn_laplace _ _ s hgood
  have hVsub : domain s σ₁ r ⊆ domain σ₀ σ₁ r := by
    intro z hz
    rcases hz with ⟨h1, h2⟩ | h
    exacts [Or.inl ⟨lt_trans hs0 h1, h2⟩, Or.inr h]
  have hVL : domain s σ₁ r ⊆ {z : ℂ | s < z.re} := by
    intro z hz
    rcases hz with ⟨h1, _⟩ | h
    exacts [h1, lt_of_le_of_lt hs1 h]
  have hFV : AnalyticOnNhd ℂ F (domain s σ₁ r) :=
    (hF.mono hVsub).analyticOnNhd (isOpen_domain _ _ _)
  have hLV : AnalyticOnNhd ℂ (laplace (Ici y₀) g) (domain s σ₁ r) :=
    (hLd.mono hVL).analyticOnNhd (isOpen_domain _ _ _)
  have hzr : (((σ₁ + 1 : ℝ) : ℂ)).re = σ₁ + 1 := by simp
  have heq : EqOn F (laplace (Ici y₀) g) (domain s σ₁ r) := by
    refine hFV.eqOn_of_preconnected_of_eventuallyEq hLV (isPreconnected_domain hs1 hr)
      (Or.inr (by rw [mem_ofPred_eq, hzr]; linarith)) ?_
    have hopen : IsOpen {z : ℂ | σ₁ < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by rw [mem_ofPred_eq, hzr]; linarith)] with z hz
    exact hFL z hz
  -- the Cauchy power series of `F` at `z₁`, radius `2ε`
  set R : ℝ≥0 := ⟨2 * ε, by linarith⟩ with hR
  have hRval : (R : ℝ) = 2 * ε := rfl
  have hball : Metric.closedBall z₁ (R : ℝ) ⊆ domain σ₀ σ₁ r := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, hRval] at hz
    have h1 := Complex.abs_re_le_norm (z - z₁)
    have h2 := Complex.abs_im_le_norm (z - z₁)
    rw [Complex.sub_re, hz₁re] at h1
    rw [Complex.sub_im] at h2
    have hz₁im : z₁.im = 0 := by simp [hz₁]
    rw [hz₁im, sub_zero] at h2
    refine Or.inl ⟨?_, ?_⟩
    · have := neg_abs_le (z.re - (s + ε))
      linarith
    · linarith
  have hRpos : (0 : ℝ≥0) < R := by
    rw [← NNReal.coe_lt_coe, hRval, NNReal.coe_zero]
    linarith
  have hFps := (hF.mono hball).hasFPowerSeriesOnBall hRpos
  -- the Laplace power series at `z₁`, radius `ε`
  have hLps := hasFPowerSeriesOnBall_laplace (Ici y₀) g z₁ hε0 (fun t ht =>
    hgood _ (by rw [hz₁re]; have := neg_abs_le t; linarith))
  have hFeqL : ∀ᶠ z in 𝓝 z₁, F z = laplace (Ici y₀) g z := by
    have hz₁V : z₁ ∈ domain s σ₁ r := by
      refine Or.inl ⟨by rw [hz₁re]; linarith, ?_⟩
      simp [hz₁]
      exact hr
    filter_upwards [(isOpen_domain s σ₁ r).mem_nhds hz₁V] with z hz
    exact heq hz
  have hpeq := hFps.hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    hLps.hasFPowerSeriesAt hFeqL
  -- evaluate at `v = −(3/2)ε`
  set b : ℝ := 3 / 2 * ε with hb
  set v : ℂ := ((-b : ℝ) : ℂ) with hv
  have hvmem : v ∈ Metric.eball (0 : ℂ) R := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    have : ‖v‖ = b := by simp [hv, abs_of_nonneg (show 0 ≤ b by positivity)]
    rw [this, ← ENNReal.ofReal_coe_nnreal, hRval]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hsumF := hFps.hasSum hvmem
  rw [hpeq, FormalMultilinearSeries.ofScalars_apply_eq'] at hsumF
  -- the terms are the real moments
  set a : ℕ → ℝ := fun n => ∫ y in Ici y₀, g y * Real.exp (-(s + ε) * y) * ((b * y) ^ n / n !)
    with ha
  have hterm_eq : ∀ n : ℕ, coeff (Ici y₀) g z₁ n • v ^ n = ((a n : ℝ) : ℂ) := by
    intro n
    have hint : (∫ y in Ici y₀, (g y : ℂ) * (y : ℂ) ^ n * cexp (-z₁ * y))
        = ((∫ y in Ici y₀, g y * y ^ n * Real.exp (-(s + ε) * y) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext y
      rw [hz₁]
      push_cast
      ring
    rw [smul_eq_mul, coeff, hint, ha]
    simp only
    rw [show (fun y => g y * Real.exp (-(s + ε) * y) * ((b * y) ^ n / n !)) =
        fun y => (b ^ n / n !) * (g y * y ^ n * Real.exp (-(s + ε) * y)) by
      funext y
      rw [mul_pow]
      ring, integral_const_mul]
    rw [hv]
    push_cast
    set J : ℂ := ((∫ y in Ici y₀, g y * y ^ n * Real.exp (-(s + ε) * y) : ℝ) : ℂ) with hJ
    rw [neg_pow (b : ℂ) n]
    have h1 : ((-1 : ℂ) ^ n) * (-1 : ℂ) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    linear_combination ((b : ℂ) ^ n / n ! * J) * h1
  simp only [hterm_eq] at hsumF
  have hsumR : Summable a := by
    have h := hsumF.mapL Complex.reCLM
    simpa using h.summable
  -- each moment is integrable
  have hterms : ∀ n : ℕ,
      IntegrableOn (fun y => g y * Real.exp (-(s + ε) * y) * ((b * y) ^ n / n !)) (Ici y₀) := by
    intro n
    have hbase := hgood (s + ε / 2) (by linarith)
    refine (hbase.const_mul ((3 : ℝ) ^ n)).mono' ?_ ?_
    · exact (hm.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mul
        ((((continuous_const.mul continuous_id).pow n).div_const _).aestronglyMeasurable)
    · refine (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun y hy => ?_)
      have hy' : 0 ≤ y := le_trans hy₀ hy
      have hgy := hg y hy
      have hx : 0 ≤ ε / 2 * y := by positivity
      have hexp := Real.pow_div_factorial_le_exp _ hx n
      have hbx : (b * y) ^ n / n ! = (3 : ℝ) ^ n * ((ε / 2 * y) ^ n / n !) := by
        rw [hb, show 3 / 2 * ε * y = 3 * (ε / 2 * y) by ring, mul_pow]
        ring
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hbx]
      have hfinal : g y * Real.exp (-(s + ε) * y) * ((3 : ℝ) ^ n * ((ε / 2 * y) ^ n / n !))
          ≤ g y * Real.exp (-(s + ε) * y) * ((3 : ℝ) ^ n * Real.exp (ε / 2 * y)) := by
        gcongr
      calc g y * Real.exp (-(s + ε) * y) * ((3 : ℝ) ^ n * ((ε / 2 * y) ^ n / n !))
          ≤ g y * Real.exp (-(s + ε) * y) * ((3 : ℝ) ^ n * Real.exp (ε / 2 * y)) := hfinal
        _ = (3 : ℝ) ^ n * (g y * Real.exp (-(s + ε / 2) * y)) := by
          rw [show -(s + ε / 2) * y = -(s + ε) * y + ε / 2 * y by ring, Real.exp_add]
          ring
  have hint := integrableOn_of_summable_moments g y₀ hy₀ hg (s + ε) b (by positivity) hm hterms hsumR
  have hmem : (s + ε - b) ∈ T := ⟨by rw [hb]; linarith, by simpa using hint⟩
  have := csInf_le hTbdd hmem
  rw [← hs, hb] at this
  linarith

end Landau

end LandauLaplace

#print axioms LandauLaplace.hasFPowerSeriesOnBall_laplace
#print axioms LandauLaplace.differentiableOn_laplace
#print axioms LandauLaplace.integrableOn_of_summable_moments
#print axioms LandauLaplace.landau
