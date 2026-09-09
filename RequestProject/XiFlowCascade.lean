import RequestProject.XiKernelTransform
import RequestProject.GrowthDisplacementLaw
import RequestProject.OneVanishingPerHeight

/-!
# T1b–d: the flow cascade `Ξ_λ(z) = ∫ e^{λu²} K(u) e^{izu} du` (ledger 674)

* `Kker_conj`: `K` is real on the axis (theta conjugation + `hasDerivAt_conj_conj`).
* `flowStage lam z = ∫ e^{λu²} K(u) e^{izu} du`; `flowStage_zero`: `Ξ_0 = Ktrans = xiSection`.
* `hasDerivAt_flowStage`: each stage is entire for `0 ≤ λ ≤ 1` (T1b), by the domination
  `‖·‖ ≤ M e^{λu²} D(|u|)` and the quadratic-vs-super-exponential decay lemma `integrable_Dq`.
* `flowStage_conj`: `Ξ_λ(z̄) = conj Ξ_λ(z)` (T1d), from evenness and reality of `K`.
* `tendstoLocallyUniformly_flowStage`: `Ξ_{1/(n+1)} → ξ-section` locally uniformly (T1c), by dominated
  convergence.
* **`flowCascade : MidpointCascade`** with **`realStages_flowCascade`**.
-/

open Complex Set Filter Topology MeasureTheory CriticalLinePhasor.XiChannel CriticalLinePhasor.Cascade

namespace CriticalLinePhasor.XiKernel

/-! ### Reality of `K` on the axis -/

theorem thetaExp_conj (w : ℂ) : thetaExp ((starRingEnd ℂ) w) = (starRingEnd ℂ) (thetaExp w) := by
  unfold thetaExp
  rw [jacobiTheta₂_conj, map_zero]
  congr 1
  rw [map_mul, Complex.conj_I, ← Complex.exp_conj, map_mul, map_ofNat]
  ring

theorem PsiC_conj (w : ℂ) : PsiC ((starRingEnd ℂ) w) = (starRingEnd ℂ) (PsiC w) := by
  unfold PsiC
  rw [thetaExp_conj, map_div₀, map_sub, map_one, map_ofNat]

theorem conj_mem_strip {w : ℂ} (hw : w ∈ strip) : (starRingEnd ℂ) w ∈ strip := by
  change |((starRingEnd ℂ) w).im| < Real.pi / 4
  rw [Complex.conj_im, abs_neg]; exact hw

theorem deriv_PsiC_conj {w : ℂ} (hw : w ∈ strip) :
    deriv PsiC ((starRingEnd ℂ) w) = (starRingEnd ℂ) (deriv PsiC w) := by
  have hd : HasDerivAt PsiC (deriv PsiC w) w :=
    (differentiableOn_PsiC.differentiableAt (strip_isOpen.mem_nhds hw)).hasDerivAt
  have h := CriticalLinePhasor.GrowthDisplacement.hasDerivAt_conj_conj hd
  have hfun : (fun z => (starRingEnd ℂ) (PsiC ((starRingEnd ℂ) z))) = PsiC := by
    funext z; rw [PsiC_conj, Complex.conj_conj]
  rw [hfun] at h
  exact h.deriv

theorem deriv_deriv_PsiC_conj {w : ℂ} (hw : w ∈ strip) :
    deriv (deriv PsiC) ((starRingEnd ℂ) w) = (starRingEnd ℂ) (deriv (deriv PsiC) w) := by
  have hd : HasDerivAt (deriv PsiC) (deriv (deriv PsiC) w) w :=
    (differentiableOn_deriv_PsiC.differentiableAt (strip_isOpen.mem_nhds hw)).hasDerivAt
  have h := CriticalLinePhasor.GrowthDisplacement.hasDerivAt_conj_conj hd
  have hev : deriv PsiC =ᶠ[𝓝 ((starRingEnd ℂ) w)] fun z => (starRingEnd ℂ) (deriv PsiC ((starRingEnd ℂ) z)) := by
    filter_upwards [strip_isOpen.mem_nhds (conj_mem_strip hw)] with z hz
    rw [deriv_PsiC_conj hz, Complex.conj_conj]
  exact (h.congr_of_eventuallyEq hev).deriv

theorem Psi1_conj (u : ℝ) : (starRingEnd ℂ) (Psi1 u) = Psi1 u := by
  unfold Psi1
  rw [← deriv_PsiC_conj (ofReal_mem_strip u), Complex.conj_ofReal]

theorem Psi2_conj (u : ℝ) : (starRingEnd ℂ) (Psi2 u) = Psi2 u := by
  unfold Psi2
  rw [← deriv_deriv_PsiC_conj (ofReal_mem_strip u), Complex.conj_ofReal]

/-- **`K` is real on the axis.** -/
theorem Kker_conj (u : ℝ) : (starRingEnd ℂ) (Kker u) = Kker u := by
  unfold Kker
  rw [map_mul, map_add, Psi1_conj, Psi2_conj, ← Complex.exp_conj, map_div₀, Complex.conj_ofReal, map_ofNat]

/-! ### The Gaussian-weighted profile and its integrability -/

/-- `Dq λ c b u = e^{λu²} D_{c,b}(|u|)`. -/
noncomputable def Dq (lam c b u : ℝ) : ℝ := Real.exp (lam * u ^ 2) * Dabs c b u

theorem Dq_nonneg (lam c b u : ℝ) : 0 ≤ Dq lam c b u := by unfold Dq; exact mul_nonneg (Real.exp_pos _).le (Dabs_nonneg _ _ _)

theorem continuous_Dq (lam c b : ℝ) : Continuous (Dq lam c b) := by
  unfold Dq; exact (Real.continuous_exp.comp (by fun_prop)).mul (continuous_Dabs c b)

theorem Dq_even (lam c b u : ℝ) : Dq lam c b (-u) = Dq lam c b u := by
  unfold Dq Dabs; simp

/-- For `0 ≤ λ ≤ 1`, `b ≥ 0`, `c ≥ 0` and `u ≥ (10 b + c + 1)/4 + b`:
`λu² + cu − (5/2) e^{2(u−b)} ≤ −u`. -/
theorem decay_dominated_q {lam c b u : ℝ} (hlam : lam ≤ 1) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hu : (10 * b + c + 1) / 4 + b ≤ u) :
    lam * u ^ 2 + c * u - 5 / 2 * Real.exp (2 * (u - b)) ≤ -u := by
  have hq : 0 ≤ (10 * b + c + 1) / 4 := by positivity
  have hub : b ≤ u := by linarith
  have hu0 : 0 ≤ u := by linarith
  have h := Real.quadratic_le_exp_of_nonneg (x := 2 * (u - b)) (by linarith)
  -- e^{2(u−b)} ≥ 2(u−b)², so (5/2)e^{2(u−b)} ≥ 5(u−b)² ≥ λu² + (c+1)u
  nlinarith [sq_nonneg (u - b), mul_nonneg hu0 (by linarith : (0:ℝ) ≤ 4 * u - (10 * b + c + 1)),
    mul_le_mul_of_nonneg_right hlam (sq_nonneg u), sq_nonneg b, sq_nonneg u]

theorem integrableOn_Dq_Ici {lam c b : ℝ} (_hlam0 : 0 ≤ lam) (hlam : lam ≤ 1) (hc : 0 ≤ c) (hb : 0 ≤ b) :
    IntegrableOn (Dq lam c b) (Ici 0) := by
  set u₁ := (10 * b + c + 1) / 4 + b with hu₁
  have hu₁0 : 0 ≤ u₁ := by rw [hu₁]; positivity
  have hcont := continuous_Dq lam c b
  have h1 : IntegrableOn (Dq lam c b) (Icc 0 u₁) := hcont.continuousOn.integrableOn_Icc
  have h2 : IntegrableOn (Dq lam c b) (Ioi u₁) := by
    have hg : IntegrableOn (fun u : ℝ => Real.exp (-1 * u)) (Ioi u₁) :=
      exp_neg_integrableOn_Ioi u₁ (by norm_num)
    refine hg.mono' hcont.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : u₁ < u := hu
    have hu0 : 0 ≤ u := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (Dq_nonneg _ _ _ _)]
    unfold Dq Dabs Dprof
    rw [abs_of_nonneg hu0, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := decay_dominated_q hlam hc hb (le_of_lt (by rw [hu₁] at hu'; exact hu'))
    linarith
  have hunion : Ici (0:ℝ) = Icc 0 u₁ ∪ Ioi u₁ := by
    ext y; simp only [mem_Ici, mem_union, mem_Icc, mem_Ioi]
    constructor
    · intro h; by_cases hy : y ≤ u₁
      · exact Or.inl ⟨h, hy⟩
      · exact Or.inr (lt_of_not_ge hy)
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact le_trans hu₁0 h.le
  rw [hunion]
  exact h1.union h2

/-- **`Dq` is integrable on `ℝ`** for `0 ≤ λ ≤ 1`, `c, b ≥ 0`. -/
theorem integrable_Dq {lam c b : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1) (hc : 0 ≤ c) (hb : 0 ≤ b) :
    Integrable (Dq lam c b) := by
  have hpos := integrableOn_Dq_Ici hlam0 hlam hc hb
  have hneg : IntegrableOn (Dq lam c b) (Iic 0) := by
    have := hpos.comp_neg
    rw [show -(Ici (0:ℝ)) = Iic 0 by ext x; simp] at this
    refine this.congr_fun (fun u _ => ?_) measurableSet_Iic
    show Dq lam c b (-u) = Dq lam c b u
    exact Dq_even lam c b u
  rw [← integrableOn_univ, ← Iic_union_Ici (a := (0:ℝ))]
  exact hneg.union hpos

/-! ### The flow stages -/

/-- `Ξ_λ(z) = ∫ e^{λu²} K(u) e^{izu} du`. -/
noncomputable def flowStage (lam : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)

theorem flowStage_zero (z : ℂ) : flowStage 0 z = Ktrans z := by
  unfold flowStage Ktrans
  simp

theorem continuous_flow_integrand (lam : ℝ) (z : ℂ) :
    Continuous (fun u : ℝ => ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)) :=
  ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))).mul continuous_Kker).mul
    (Complex.continuous_exp.comp (by fun_prop))

theorem continuous_flow_integrand' (lam : ℝ) (z : ℂ) :
    Continuous (fun u : ℝ => ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * (I * u * Complex.exp (I * z * u))) :=
  ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))).mul continuous_Kker).mul
    (by fun_prop)

/-- Pointwise domination of the integrand and its `z`-derivative. -/
theorem flow_integrand_bound {lam : ℝ} (_hlam0 : 0 ≤ lam) {M : ℝ}
    (hK : ∀ u : ℝ, ‖Kker u‖ ≤ M * Dabs (1 / 2) (2 * Rc) u) {z : ℂ} {a : ℝ} (hz : |z.im| ≤ a) (u : ℝ) :
    ‖((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)‖
      ≤ M * Dq lam (1 / 2 + a) (2 * Rc) u := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 := hK u
  have h2 := norm_exp_I_mul_le hz u
  have hM : 0 ≤ M := by
    have := (norm_nonneg (Kker 0)).trans (hK 0)
    have hD : 0 < Dabs (1 / 2) (2 * Rc) 0 := by unfold Dabs Dprof; positivity
    nlinarith
  calc Real.exp (lam * u ^ 2) * ‖Kker u‖ * ‖Complex.exp (I * z * u)‖
      ≤ Real.exp (lam * u ^ 2) * (M * Dabs (1 / 2) (2 * Rc) u) * Real.exp (a * |u|) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le) h2 (norm_nonneg _)
          (mul_nonneg (Real.exp_pos _).le (mul_nonneg hM (Dabs_nonneg _ _ _)))
    _ = M * (Real.exp (lam * u ^ 2) * (Dabs (1 / 2) (2 * Rc) u * Real.exp (a * |u|))) := by ring
    _ = M * Dq lam (1 / 2 + a) (2 * Rc) u := by rw [Dabs_mul_exp]; rfl

theorem flow_integrand'_bound {lam : ℝ} (_hlam0 : 0 ≤ lam) {M : ℝ}
    (hK : ∀ u : ℝ, ‖Kker u‖ ≤ M * Dabs (1 / 2) (2 * Rc) u) {z : ℂ} {a : ℝ} (hz : |z.im| ≤ a) (u : ℝ) :
    ‖((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * (I * u * Complex.exp (I * z * u))‖
      ≤ M * Dq lam (1 / 2 + (a + 1)) (2 * Rc) u := by
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_real, Real.norm_eq_abs]
  have hM : 0 ≤ M := by
    have := (norm_nonneg (Kker 0)).trans (hK 0)
    have hD : 0 < Dabs (1 / 2) (2 * Rc) 0 := by unfold Dabs Dprof; positivity
    nlinarith
  calc Real.exp (lam * u ^ 2) * ‖Kker u‖ * (|u| * ‖Complex.exp (I * z * u)‖)
      ≤ Real.exp (lam * u ^ 2) * (M * Dabs (1 / 2) (2 * Rc) u) * (Real.exp |u| * Real.exp (a * |u|)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hK u) (Real.exp_pos _).le)
          (mul_le_mul (abs_le_exp_abs u) (norm_exp_I_mul_le hz u) (norm_nonneg _) (Real.exp_pos _).le)
          (by positivity) (mul_nonneg (Real.exp_pos _).le (mul_nonneg hM (Dabs_nonneg _ _ _)))
    _ = M * (Real.exp (lam * u ^ 2) * (Dabs (1 / 2) (2 * Rc) u * Real.exp ((a + 1) * |u|))) := by
        rw [← Real.exp_add]; ring_nf
    _ = M * Dq lam (1 / 2 + (a + 1)) (2 * Rc) u := by rw [Dabs_mul_exp]; rfl

theorem integrable_flow_integrand {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1) (z : ℂ) :
    Integrable (fun u : ℝ => ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)) := by
  obtain ⟨M, hM, hK⟩ := Kker_bound
  have hdom : Integrable (fun u : ℝ => M * Dq lam (1 / 2 + |z.im|) (2 * Rc) u) :=
    (integrable_Dq hlam0 hlam (by positivity) (by have := Rc_pos; positivity)).const_mul M
  refine hdom.mono' (continuous_flow_integrand lam z).aestronglyMeasurable ?_
  filter_upwards with u
  exact flow_integrand_bound hlam0 hK le_rfl u

/-- **T1b: each stage is entire.** -/
theorem hasDerivAt_flowStage {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1) (z₀ : ℂ) :
    HasDerivAt (flowStage lam)
      (∫ u : ℝ, ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * (I * u * Complex.exp (I * z₀ * u))) z₀ := by
  obtain ⟨M, hM, hK⟩ := Kker_bound
  set a : ℝ := |z₀.im| + 1 with ha
  have hball : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ one_pos
  have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable
      (fun u : ℝ => ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)) volume :=
    Eventually.of_forall fun z => (continuous_flow_integrand lam z).aestronglyMeasurable
  have hF_int := integrable_flow_integrand hlam0 hlam z₀
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ => ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * (I * u * Complex.exp (I * z₀ * u))) volume :=
    (continuous_flow_integrand' lam z₀).aestronglyMeasurable
  have hbound_int : Integrable (fun u : ℝ => M * Dq lam (1 / 2 + (a + 1)) (2 * Rc) u) :=
    (integrable_Dq hlam0 hlam (by positivity) (by have := Rc_pos; positivity)).const_mul M
  have h_bound : ∀ᵐ u ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      ‖((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * (I * u * Complex.exp (I * z * u))‖
        ≤ M * Dq lam (1 / 2 + (a + 1)) (2 * Rc) u := by
    filter_upwards with u
    intro z hz
    exact flow_integrand'_bound hlam0 hK (by rw [ha]; exact im_le_of_mem_ball hz) u
  have h_diff : ∀ᵐ u ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      HasDerivAt (fun z : ℂ => ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u))
        (((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * (I * u * Complex.exp (I * z * u))) z := by
    filter_upwards with u
    intro z _
    have h1 : HasDerivAt (fun z : ℂ => I * z * u) (I * u) z := by
      simpa using ((hasDerivAt_id z).const_mul I).mul_const (u : ℂ)
    exact (h1.cexp.const_mul (((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u)).congr_deriv (by ring)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hball hF_meas hF_int hF'_meas h_bound
    hbound_int h_diff).2

theorem differentiable_flowStage {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1) :
    Differentiable ℂ (flowStage lam) := fun z => (hasDerivAt_flowStage hlam0 hlam z).differentiableAt

/-- **T1d: the stages are real on the axis.** -/
theorem flowStage_conj (lam : ℝ) (z : ℂ) :
    flowStage lam ((starRingEnd ℂ) z) = (starRingEnd ℂ) (flowStage lam z) := by
  unfold flowStage
  rw [← integral_conj]
  -- conj of the integrand at `u` is the integrand at `z̄` and `−u`; substitute `u ↦ −u`
  conv_rhs => rw [← MeasureTheory.integral_neg_eq_self]
  apply integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [map_mul, Complex.conj_ofReal, Kker_conj, ← Complex.exp_conj, Complex.conj_I, map_neg,
    Complex.ofReal_neg, neg_sq, Kker_even]
  congr 1
  congr 1
  ring

/-! ### T1c: locally uniform convergence `Ξ_{1/(n+1)} → ξ-section` -/

/-- The stage index `n ↦ λ_n = 1/(n+1)`. -/
noncomputable def lamSeq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem lamSeq_nonneg (n : ℕ) : 0 ≤ lamSeq n := by unfold lamSeq; positivity
theorem lamSeq_le_one (n : ℕ) : lamSeq n ≤ 1 := by
  unfold lamSeq; rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
theorem tendsto_lamSeq : Tendsto lamSeq atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

/-- On a compact set, the stages converge uniformly to `Ktrans`. -/
theorem tendstoUniformlyOn_flowStage {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n => flowStage (lamSeq n)) Ktrans atTop K := by
  obtain ⟨A₀, hA₀⟩ := hK.isBounded.exists_norm_le
  set A : ℝ := max A₀ 0 with hAdef
  have hA : ∀ z ∈ K, ‖z‖ ≤ A := fun z hz => (hA₀ z hz).trans (le_max_left _ _)
  have hA0 : 0 ≤ A := le_max_right _ _
  obtain ⟨M, hM, hKb⟩ := Kker_bound
  -- the error functional `J n = ∫ (e^{λ_n u²} − 1) ‖K(u)‖ e^{A|u|} du → 0`
  set J : ℕ → ℝ := fun n => ∫ u : ℝ, (Real.exp (lamSeq n * u ^ 2) - 1) * ‖Kker u‖ * Real.exp (A * |u|) with hJ
  have hJcont : ∀ n, Continuous (fun u : ℝ => (Real.exp (lamSeq n * u ^ 2) - 1) * ‖Kker u‖ * Real.exp (A * |u|)) :=
    fun n => (((Real.continuous_exp.comp (by fun_prop)).sub continuous_const).mul continuous_Kker.norm).mul
      (Real.continuous_exp.comp (by fun_prop))
  have hdom : Integrable (fun u : ℝ => M * Dq 1 (1 / 2 + A) (2 * Rc) u) :=
    (integrable_Dq zero_le_one le_rfl (by positivity) (by have := Rc_pos; positivity)).const_mul M
  have hJbound : ∀ n, ∀ u : ℝ, ‖(Real.exp (lamSeq n * u ^ 2) - 1) * ‖Kker u‖ * Real.exp (A * |u|)‖
      ≤ M * Dq 1 (1 / 2 + A) (2 * Rc) u := by
    intro n u
    have h0 : 0 ≤ Real.exp (lamSeq n * u ^ 2) - 1 := by
      have := Real.add_one_le_exp (lamSeq n * u ^ 2)
      have := mul_nonneg (lamSeq_nonneg n) (sq_nonneg u); linarith
    have h1 : Real.exp (lamSeq n * u ^ 2) - 1 ≤ Real.exp (1 * u ^ 2) := by
      have := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (lamSeq_le_one n) (sq_nonneg u))
      linarith [Real.exp_pos (1 * u ^ 2)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (Real.exp (lamSeq n * u ^ 2) - 1) * ‖Kker u‖ * Real.exp (A * |u|)
        ≤ Real.exp (1 * u ^ 2) * (M * Dabs (1 / 2) (2 * Rc) u) * Real.exp (A * |u|) := by
          gcongr; exact hKb u
      _ = M * (Real.exp (1 * u ^ 2) * (Dabs (1 / 2) (2 * Rc) u * Real.exp (A * |u|))) := by ring
      _ = M * Dq 1 (1 / 2 + A) (2 * Rc) u := by rw [Dabs_mul_exp]; rfl
  have hJlim : Tendsto J atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (F := fun n u =>
        (Real.exp (lamSeq n * u ^ 2) - 1) * ‖Kker u‖ * Real.exp (A * |u|)) (f := fun _ => (0:ℝ))
      (fun u => M * Dq 1 (1 / 2 + A) (2 * Rc) u)
      (fun n => (hJcont n).aestronglyMeasurable) hdom
      (fun n => Eventually.of_forall (hJbound n)) ?_
    · simpa [hJ] using this
    · filter_upwards with u
      have h1 : Tendsto (fun n => lamSeq n * u ^ 2) atTop (𝓝 0) := by
        simpa using tendsto_lamSeq.mul_const (u ^ 2)
      have h2 : Tendsto (fun n => Real.exp (lamSeq n * u ^ 2) - 1) atTop (𝓝 0) := by
        have := (Real.tendsto_exp_nhds_zero_nhds_one.comp h1).sub_const 1
        simpa using this
      have := (h2.mul_const ‖Kker u‖).mul_const (Real.exp (A * |u|))
      simpa using this
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hev := (Metric.tendsto_nhds.mp hJlim) ε hε
  filter_upwards [hev] with n hn
  intro z hz
  have hzA : |z.im| ≤ A := (Complex.abs_im_le_norm z).trans (hA z hz)
  rw [dist_eq_norm, ← flowStage_zero]
  unfold flowStage
  rw [← integral_sub (integrable_flow_integrand (le_refl 0) zero_le_one z)
    (integrable_flow_integrand (lamSeq_nonneg n) (lamSeq_le_one n) z)]
  refine lt_of_le_of_lt ?_ (by rw [Real.dist_eq, sub_zero] at hn; exact (le_abs_self _).trans_lt hn)
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _) ?_ (Eventually.of_forall fun u => ?_)
  · exact hdom.mono' (hJcont n).aestronglyMeasurable (Eventually.of_forall (hJbound n))
  · -- pointwise: ‖(1 − e^{λu²}) K e^{izu}‖ ≤ (e^{λu²} − 1)‖K‖e^{A|u|}
    have h0 : 0 ≤ Real.exp (lamSeq n * u ^ 2) - 1 := by
      have := Real.add_one_le_exp (lamSeq n * u ^ 2)
      have := mul_nonneg (lamSeq_nonneg n) (sq_nonneg u); linarith
    have hEq : ((Real.exp (0 * u ^ 2) : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)
        - ((Real.exp (lamSeq n * u ^ 2) : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)
        = -(((Real.exp (lamSeq n * u ^ 2) - 1 : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)) := by
      simp only [zero_mul, Real.exp_zero, Complex.ofReal_one, Complex.ofReal_sub]; ring
    dsimp only
    rw [hEq, norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    gcongr
    exact norm_exp_I_mul_le hzA u

/-- **T1c.** -/
theorem tendstoLocallyUniformly_flowStage :
    TendstoLocallyUniformly (fun n => flowStage (lamSeq n)) xiSection atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  have := tendstoUniformlyOn_flowStage hK
  have hfun : xiSection = Ktrans := funext xiSection_eq_Ktrans
  rw [hfun]; exact this

/-- **The flow cascade.** -/
noncomputable def flowCascade : MidpointCascade where
  stage n := flowStage (lamSeq n)
  stage_entire n := differentiable_flowStage (lamSeq_nonneg n) (lamSeq_le_one n)
  converges := tendstoLocallyUniformly_flowStage

/-- **The flow cascade has real stages.** -/
theorem realStages_flowCascade : RealStages flowCascade := fun n z => flowStage_conj (lamSeq n) z

/-- **T1 assembled:** RH follows from one vanishing per height on the flow stages. -/
theorem rh_of_oneVanishingPerHeight_flow (h : OneVanishingPerHeight flowCascade) : RiemannHypothesis :=
  rh_of_oneVanishingPerHeight flowCascade realStages_flowCascade h

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.realStages_flowCascade
#print axioms CriticalLinePhasor.XiKernel.rh_of_oneVanishingPerHeight_flow
