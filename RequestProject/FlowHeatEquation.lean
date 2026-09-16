import RequestProject.XiFlowCascade

/-!
# The warped fiber obeys the backward heat equation in the warp parameter

`flowStage λ z = ∫ e^{λu²} K(u) e^{izu} du` is the amplitude-warped fiber (ledger 674).  Differentiating
under the integral in `λ` brings down `u²`; differentiating twice in `z` brings down `(iu)² = −u²`.
Hence

    ∂_λ (flowStage λ z)  =  − ∂_z² (flowStage λ z).

This is the input the merger argument needs: a zero of order `m ≥ 2` of `flowStage λ₀` cannot persist,
because the `λ`-derivative at such a point is forced by the `z`-derivatives, and going DOWN in `λ` the
coincident cancellations separate into a conjugate pair off the axis.

The domination reuses `XiFlowCascade`'s profile `Dq λ c b u = e^{λu²} D_{c,b}(|u|)`: the extra factor
`u²` is absorbed by `u² ≤ 4e^{|u|}` and `Dabs_mul_exp`, and `e^{λu²} ≤ e^{λ₁u²}` for `λ` in a ball
below `λ₁ < 1`.
-/

open Complex MeasureTheory Filter Topology

namespace CriticalLinePhasor.XiKernel

/-- `u² ≤ 4e^{|u|}`, the bound that absorbs the `λ`-derivative's extra factor into the profile. -/
theorem sq_le_four_mul_exp_abs (u : ℝ) : u ^ 2 ≤ 4 * Real.exp |u| := by
  have h := Real.add_one_le_exp (|u| / 2)
  have habs : (0 : ℝ) ≤ |u| := abs_nonneg u
  have hpos : 0 < Real.exp (|u| / 2) := Real.exp_pos _
  have hexp : Real.exp |u| = Real.exp (|u| / 2) * Real.exp (|u| / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hsq : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  rw [hsq, hexp]
  nlinarith [h, habs, hpos]

/-- The `λ`-derivative integrand is continuous. -/
theorem continuous_lam_integrand (lam : ℝ) (z : ℂ) :
    Continuous (fun u : ℝ =>
      (((u ^ 2 * Real.exp (lam * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)) :=
  ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_Kker).mul
    (Complex.continuous_exp.comp (by fun_prop))

/-- Domination of the `λ`-derivative integrand, uniformly for `lam ≤ lam₁`. -/
theorem lam_integrand_bound {lam lam₁ : ℝ} (hle : lam ≤ lam₁) {M : ℝ}
    (hK : ∀ u : ℝ, ‖Kker u‖ ≤ M * Dabs (1 / 2) (2 * Rc) u) {z : ℂ} {a : ℝ} (hz : |z.im| ≤ a)
    (u : ℝ) :
    ‖(((u ^ 2 * Real.exp (lam * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)‖
      ≤ (4 * M) * Dq lam₁ (1 / 2 + (a + 1)) (2 * Rc) u := by
  have hM : 0 ≤ M := by
    have := (norm_nonneg (Kker 0)).trans (hK 0)
    have hD : 0 < Dabs (1 / 2) (2 * Rc) 0 := by unfold Dabs Dprof; positivity
    nlinarith
  have hKu := hK u
  have hexpz := norm_exp_I_mul_le hz u
  have hu2 := sq_le_four_mul_exp_abs u
  have hmono : Real.exp (lam * u ^ 2) ≤ Real.exp (lam₁ * u ^ 2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hle (sq_nonneg u))
  have hDnn := Dabs_nonneg (1 / 2) (2 * Rc) u
  have hnorm : ‖(((u ^ 2 * Real.exp (lam * u ^ 2) : ℝ)) : ℂ)‖ = u ^ 2 * Real.exp (lam * u ^ 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [norm_mul, norm_mul, hnorm]
  have hA : u ^ 2 * Real.exp (lam * u ^ 2)
      ≤ (4 * Real.exp |u|) * Real.exp (lam₁ * u ^ 2) :=
    mul_le_mul hu2 hmono (Real.exp_pos _).le (by positivity)
  have hB : ‖Kker u‖ * ‖Complex.exp (I * z * u)‖
      ≤ (M * Dabs (1 / 2) (2 * Rc) u) * Real.exp (a * |u|) :=
    mul_le_mul hKu hexpz (norm_nonneg _) (mul_nonneg hM hDnn)
  have hstep :
      u ^ 2 * Real.exp (lam * u ^ 2) * ‖Kker u‖ * ‖Complex.exp (I * z * u)‖
        ≤ (4 * Real.exp |u|) * Real.exp (lam₁ * u ^ 2) * (M * Dabs (1 / 2) (2 * Rc) u)
            * Real.exp (a * |u|) := by
    have hL : u ^ 2 * Real.exp (lam * u ^ 2) * ‖Kker u‖ * ‖Complex.exp (I * z * u)‖
        = (u ^ 2 * Real.exp (lam * u ^ 2)) * (‖Kker u‖ * ‖Complex.exp (I * z * u)‖) := by ring
    have hR : (4 * Real.exp |u|) * Real.exp (lam₁ * u ^ 2) * (M * Dabs (1 / 2) (2 * Rc) u)
          * Real.exp (a * |u|)
        = ((4 * Real.exp |u|) * Real.exp (lam₁ * u ^ 2))
            * ((M * Dabs (1 / 2) (2 * Rc) u) * Real.exp (a * |u|)) := by ring
    rw [hL, hR]
    exact mul_le_mul hA hB (by positivity) (by positivity)
  refine hstep.trans ?_
  have hrw : (4 * Real.exp |u|) * Real.exp (lam₁ * u ^ 2) * (M * Dabs (1 / 2) (2 * Rc) u)
      * Real.exp (a * |u|)
      = (4 * M) * (Real.exp (lam₁ * u ^ 2)
          * (Dabs (1 / 2) (2 * Rc) u * Real.exp (a * |u|) * Real.exp (1 * |u|))) := by
    rw [one_mul]; ring
  rw [hrw, Dabs_mul_exp, Dabs_mul_exp]
  unfold Dq
  have : (1 / 2 + a + 1 : ℝ) = 1 / 2 + (a + 1) := by ring
  rw [this]

/-- **The `λ`-derivative of the warped fiber**: differentiating under the integral brings down `u²`. -/
theorem hasDerivAt_flowStage_lam {lam₀ lam₁ : ℝ} (h0 : 0 ≤ lam₀) (hlt : lam₀ < lam₁)
    (h1 : lam₁ ≤ 1) (z : ℂ) :
    HasDerivAt (fun lam : ℝ => flowStage lam z)
      (∫ u : ℝ, (((u ^ 2 * Real.exp (lam₀ * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u))
      lam₀ := by
  obtain ⟨M, hM, hK⟩ := Kker_bound
  set r : ℝ := lam₁ - lam₀ with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hball : Metric.ball lam₀ r ∈ 𝓝 lam₀ := Metric.ball_mem_nhds lam₀ hrpos
  have hmem : ∀ lam ∈ Metric.ball lam₀ r, lam ≤ lam₁ := by
    intro lam hlam
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hlam
    have := hlam.2
    rw [hr] at this
    linarith
  have hF_meas : ∀ᶠ lam in 𝓝 lam₀, AEStronglyMeasurable
      (fun u : ℝ => ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)) volume :=
    Eventually.of_forall fun lam => (continuous_flow_integrand lam z).aestronglyMeasurable
  have hF_int := integrable_flow_integrand h0 (le_trans hlt.le h1) z
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ => (((u ^ 2 * Real.exp (lam₀ * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u))
      volume := (continuous_lam_integrand lam₀ z).aestronglyMeasurable
  have hbound_int : Integrable
      (fun u : ℝ => (4 * M) * Dq lam₁ (1 / 2 + (|z.im| + 1)) (2 * Rc) u) :=
    (integrable_Dq (le_trans h0 hlt.le) h1 (by positivity)
      (by have := Rc_pos; positivity)).const_mul (4 * M)
  have h_bound : ∀ᵐ u ∂volume, ∀ lam ∈ Metric.ball lam₀ r,
      ‖(((u ^ 2 * Real.exp (lam * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)‖
        ≤ (4 * M) * Dq lam₁ (1 / 2 + (|z.im| + 1)) (2 * Rc) u := by
    filter_upwards with u
    intro lam hlam
    exact lam_integrand_bound (hmem lam hlam) hK le_rfl u
  have h_diff : ∀ᵐ u ∂volume, ∀ lam ∈ Metric.ball lam₀ r,
      HasDerivAt (fun lam : ℝ => ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u))
        ((((u ^ 2 * Real.exp (lam * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)) lam := by
    filter_upwards with u
    intro lam _
    have hbase : HasDerivAt (fun lam : ℝ => Real.exp (lam * u ^ 2))
        (Real.exp (lam * u ^ 2) * u ^ 2) lam := by
      simpa using (((hasDerivAt_id lam).mul_const (u ^ 2)).exp)
    have hC : HasDerivAt (fun lam : ℝ => ((Real.exp (lam * u ^ 2) : ℝ) : ℂ))
        (((Real.exp (lam * u ^ 2) * u ^ 2 : ℝ) : ℂ)) lam := hbase.ofReal_comp
    exact (hC.mul_const (Kker u)).mul_const (Complex.exp (I * z * u)) |>.congr_deriv (by push_cast; ring)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hball hF_meas hF_int hF'_meas h_bound
    hbound_int h_diff).2


/-- The second `z`-derivative of the warped fiber, as the same `u²` integral with a minus sign. -/
theorem hasDerivAt_deriv_flowStage {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (z₀ : ℂ) :
    HasDerivAt (deriv (flowStage lam))
      (-∫ u : ℝ, (((u ^ 2 * Real.exp (lam * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z₀ * u))
      z₀ := by
  obtain ⟨M, hM, hK⟩ := Kker_bound
  set a : ℝ := |z₀.im| + 1 with ha
  have hfun : deriv (flowStage lam) = fun z => ∫ u : ℝ,
      ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * (I * u * Complex.exp (I * z * u)) :=
    funext fun z => (hasDerivAt_flowStage h0 h1 z).deriv
  have hball : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ one_pos
  have hbound_int : Integrable (fun u : ℝ => M * Dq lam (1 / 2 + (a + 1)) (2 * Rc) u) :=
    (integrable_Dq h0 h1 (by positivity) (by have := Rc_pos; positivity)).const_mul M
  have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable
      (fun u : ℝ => ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u
        * (I * u * Complex.exp (I * z * u))) volume :=
    Eventually.of_forall fun z => (continuous_flow_integrand' lam z).aestronglyMeasurable
  have hF_int : Integrable (fun u : ℝ => ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u
      * (I * u * Complex.exp (I * z₀ * u))) := by
    refine hbound_int.mono' (continuous_flow_integrand' lam z₀).aestronglyMeasurable ?_
    filter_upwards with u
    exact flow_integrand'_bound h0 hK (by rw [ha]; exact le_of_lt (lt_add_one _)) u
  -- the second derivative's integrand is the `u²` one, negated
  have hpoint2 : ∀ (z : ℂ) (u : ℝ),
      (((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * (I * (u : ℂ)))
            * (I * (u : ℂ) * Complex.exp (I * z * u))
        = -((((u ^ 2 * Real.exp (lam * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)) := by
    intro z u
    have hII : (I : ℂ) * I = -1 := Complex.I_mul_I
    have hcast : (((u ^ 2 * Real.exp (lam * u ^ 2) : ℝ)) : ℂ)
        = (u : ℂ) ^ 2 * ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    linear_combination (((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * (u : ℂ) ^ 2
      * Complex.exp (I * z * u)) * hII
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ => -((((u ^ 2 * Real.exp (lam * u ^ 2) : ℝ)) : ℂ) * Kker u
        * Complex.exp (I * z₀ * u))) volume :=
    (continuous_lam_integrand lam z₀).neg.aestronglyMeasurable
  have h_bound : ∀ᵐ u ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      ‖-((((u ^ 2 * Real.exp (lam * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u))‖
        ≤ (4 * M) * Dq lam (1 / 2 + (a + 1)) (2 * Rc) u := by
    filter_upwards with u
    intro z hz
    rw [norm_neg]
    exact lam_integrand_bound le_rfl hK (by rw [ha]; exact im_le_of_mem_ball hz) u
  have hbound_int' : Integrable (fun u : ℝ => (4 * M) * Dq lam (1 / 2 + (a + 1)) (2 * Rc) u) :=
    (integrable_Dq h0 h1 (by positivity) (by have := Rc_pos; positivity)).const_mul (4 * M)
  have h_diff : ∀ᵐ u ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      HasDerivAt (fun z : ℂ => ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u
          * (I * u * Complex.exp (I * z * u)))
        (-((((u ^ 2 * Real.exp (lam * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u))) z := by
    filter_upwards with u
    intro z _
    have hlin : HasDerivAt (fun z : ℂ => I * z * u) (I * u) z := by
      simpa using ((hasDerivAt_id z).const_mul I).mul_const (u : ℂ)
    have hexp : HasDerivAt (fun z : ℂ => Complex.exp (I * z * u))
        (I * (u : ℂ) * Complex.exp (I * z * u)) z := by
      simpa [mul_comm] using hlin.cexp
    have hassoc : (fun z : ℂ => ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u
          * (I * u * Complex.exp (I * z * u)))
        = fun z : ℂ => (((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * (I * (u : ℂ)))
            * Complex.exp (I * z * u) := by
      funext w; ring
    rw [hassoc]
    exact (hexp.const_mul _).congr_deriv (hpoint2 z u)
  rw [hfun]
  have hres := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hball hF_meas hF_int hF'_meas
    h_bound hbound_int' h_diff).2
  rwa [MeasureTheory.integral_neg] at hres


/-- **The backward heat equation for the amplitude-warped fiber.**  Differentiating the warp parameter
is the same as minus the second derivative in the height variable:

    ∂_λ (flowStage λ z)  =  − ∂_z² (flowStage λ z).

This is the exact input the merger argument consumes: at a zero of order `m ≥ 2` the `λ`-derivative is
pinned by the `z`-derivatives, and descending in `λ` the coincident cancellations must separate off the
axis. -/
theorem flowStage_heat_equation {lam₀ lam₁ : ℝ} (h0 : 0 ≤ lam₀) (hlt : lam₀ < lam₁) (h1 : lam₁ ≤ 1)
    (z : ℂ) :
    deriv (fun lam : ℝ => flowStage lam z) lam₀ = -deriv (deriv (flowStage lam₀)) z := by
  rw [(hasDerivAt_flowStage_lam h0 hlt h1 z).deriv,
    (hasDerivAt_deriv_flowStage h0 (le_trans hlt.le h1) z).deriv, neg_neg]

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.hasDerivAt_flowStage_lam
#print axioms CriticalLinePhasor.XiKernel.hasDerivAt_deriv_flowStage
#print axioms CriticalLinePhasor.XiKernel.flowStage_heat_equation
