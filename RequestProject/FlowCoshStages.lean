import RequestProject.XiFlowCascade
import RequestProject.StripShiftClass

/-!
# The cosh-power stages of the flow (T2c, strip narrowing)

The imaginary shift `f ↦ f(· + ih) + f(· − ih)` acts on the transform `∫ K(u) e^{izu} du` by multiplying the kernel
by `2cosh(hu)`:

* `coshStage h N z = ∫ (2cosh(hu))^N K(u) e^{izu} du`, with `coshStage h 0 = Ktrans` and
  `shiftOp h (coshStage h N) = coshStage h (N+1)`; hence `(shiftOp h)^[N] Ktrans = coshStage h N`.
* With `h_n = √(2λ/(n+1))`, `cosh(h_n u)^{n+1} → e^{λu²}` and the normalised stages
  `coshApprox lam n z = ∫ cosh(h_n u)^{n+1} K(u) e^{izu} du` converge to `flowStage lam` locally uniformly on `ℂ`
  (dominated convergence; uniform on every horizontal strip).
* No weighted transform `∫ w(u) K(u) e^{izu} du` with `w` continuous and nonvanishing is identically zero
  (Fourier inversion and `ξ(½) ≠ 0`).
-/

open Complex Filter Topology MeasureTheory Set
open scoped FourierTransform
open CriticalLinePhasor.DeBruijn (shiftOp)

namespace CriticalLinePhasor.XiKernel

/-! ### Two elementary bounds on `cosh` -/

theorem one_add_sq_div_two_le_cosh (r : ℝ) : 1 + r ^ 2 / 2 ≤ Real.cosh r := by
  have h := sum_le_hasSum (Finset.range 2)
    (fun i _ => div_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg r) i) (by positivity))
    (Real.hasSum_cosh r)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

/-! ### Integrability of weighted transforms -/

/-- A continuous weight of at most exponential growth keeps the transform's integrand integrable. -/
theorem integrable_weighted_Kker {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (w : ℝ → ℝ) (hw : Continuous w)
    (hwb : ∀ u, |w u| ≤ A * Real.exp (c * |u|)) (z : ℂ) :
    Integrable (fun u : ℝ => ((w u : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)) := by
  obtain ⟨M, hM, hK⟩ := Kker_bound
  have hcont : Continuous (fun u : ℝ => ((w u : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)) :=
    ((Complex.continuous_ofReal.comp hw).mul continuous_Kker).mul (Complex.continuous_exp.comp (by fun_prop))
  have hdom : Integrable (fun u : ℝ => (A * M) * Dabs (1 / 2 + c + |z.im|) (2 * Rc) u) :=
    (integrable_Dabs (by positivity) _).const_mul (A * M)
  refine hdom.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with u
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := hK u
  have h2 := norm_exp_I_mul_le (le_refl |z.im|) u
  have h3 := hwb u
  have hD := Dabs_nonneg (1 / 2) (2 * Rc) u
  calc |w u| * ‖Kker u‖ * ‖Complex.exp (I * z * u)‖
      ≤ (A * Real.exp (c * |u|)) * (M * Dabs (1 / 2) (2 * Rc) u) * Real.exp (|z.im| * |u|) :=
        mul_le_mul (mul_le_mul h3 h1 (norm_nonneg _) (by positivity)) h2 (norm_nonneg _)
          (by positivity)
    _ = (A * M) * (Dabs (1 / 2) (2 * Rc) u * Real.exp (c * |u|) * Real.exp (|z.im| * |u|)) := by ring
    _ = (A * M) * Dabs (1 / 2 + c + |z.im|) (2 * Rc) u := by rw [Dabs_mul_exp, Dabs_mul_exp]

/-! ### The cosh-power stages -/

/-- `coshStage h N z = ∫ (2cosh(hu))^N K(u) e^{izu} du`. -/
noncomputable def coshStage (h : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, (((2 * Real.cosh (h * u)) ^ N : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)

theorem two_cosh_pow_bound (h : ℝ) (N : ℕ) (u : ℝ) :
    |(2 * Real.cosh (h * u)) ^ N| ≤ (2 : ℝ) ^ N * Real.exp ((N * |h|) * |u|) := by
  have hc : 0 < Real.cosh (h * u) := Real.cosh_pos _
  rw [abs_of_pos (by positivity), show (N * |h|) * |u| = N * (|h| * |u|) by ring, Real.exp_nat_mul,
    ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have := cosh_le_exp_abs (h * u)
  rw [abs_mul] at this
  linarith

theorem integrable_coshStage_integrand (h : ℝ) (N : ℕ) (z : ℂ) :
    Integrable (fun u : ℝ => (((2 * Real.cosh (h * u)) ^ N : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)) :=
  integrable_weighted_Kker (by positivity) (by positivity) _ (by fun_prop) (two_cosh_pow_bound h N) z

theorem coshStage_zero (h : ℝ) : coshStage h 0 = Ktrans := by
  funext z
  unfold coshStage Ktrans
  simp

/-- **The shift multiplies the kernel by `2cosh(hu)`.** -/
theorem coshStage_shift (h : ℝ) (N : ℕ) (z : ℂ) :
    coshStage h N (z + I * h) + coshStage h N (z - I * h) = coshStage h (N + 1) z := by
  unfold coshStage
  rw [← integral_add (integrable_coshStage_integrand h N _) (integrable_coshStage_integrand h N _)]
  congr 1
  funext u
  have e1 : Complex.exp (I * (z + I * h) * u) = Complex.exp (I * z * u) * Complex.exp (-((h : ℂ) * u)) := by
    rw [← Complex.exp_add]; congr 1; linear_combination ((h : ℂ) * u) * Complex.I_mul_I
  have e2 : Complex.exp (I * (z - I * h) * u) = Complex.exp (I * z * u) * Complex.exp ((h : ℂ) * u) := by
    rw [← Complex.exp_add]; congr 1; linear_combination (-((h : ℂ) * u)) * Complex.I_mul_I
  rw [e1, e2]
  push_cast
  rw [pow_succ]
  have hc := Complex.two_cosh (x := (h : ℂ) * u)
  linear_combination (-((2 * Complex.cosh ((h : ℂ) * u)) ^ N * Kker u * Complex.exp (I * z * u))) * hc

/-- **`N` shifts of the transform are the `N`-th cosh-power stage.** -/
theorem shiftOp_iterate_Ktrans (h : ℝ) (N : ℕ) : (shiftOp h)^[N] Ktrans = coshStage h N := by
  induction N with
  | zero => simp [coshStage_zero]
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih]
    funext z
    exact coshStage_shift h N z

theorem differentiable_shiftOp {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h : ℝ) :
    Differentiable ℂ (shiftOp h f) :=
  (hf.comp (differentiable_id.add_const _)).add (hf.comp (differentiable_id.sub_const _))

theorem differentiable_coshStage (h : ℝ) (N : ℕ) : Differentiable ℂ (coshStage h N) := by
  rw [← shiftOp_iterate_Ktrans]
  induction N with
  | zero => simpa using differentiable_Ktrans
  | succ N ih => rw [Function.iterate_succ_apply']; exact differentiable_shiftOp ih h

/-! ### The normalised stages and their limit -/

/-- `h_n = √(2λ/(n+1))`. -/
noncomputable def flowShift (lam : ℝ) (n : ℕ) : ℝ := Real.sqrt (2 * lam / (n + 1))

/-- `coshApprox lam n z = ∫ cosh(h_n u)^{n+1} K(u) e^{izu} du`. -/
noncomputable def coshApprox (lam : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, ((Real.cosh (flowShift lam n * u) ^ (n + 1) : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)

theorem coshStage_eq_two_pow_mul_coshApprox (lam : ℝ) (n : ℕ) (z : ℂ) :
    coshStage (flowShift lam n) (n + 1) z = (2 : ℂ) ^ (n + 1) * coshApprox lam n z := by
  unfold coshStage coshApprox
  rw [← integral_const_mul]
  congr 1
  funext u
  push_cast
  ring

theorem coshApprox_eq_zero_iff (lam : ℝ) (n : ℕ) (z : ℂ) :
    coshApprox lam n z = 0 ↔ coshStage (flowShift lam n) (n + 1) z = 0 := by
  rw [coshStage_eq_two_pow_mul_coshApprox]
  simp

theorem flowShift_sq {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) : (flowShift lam n) ^ 2 = 2 * lam / (n + 1) := by
  unfold flowShift
  exact Real.sq_sqrt (by positivity)

/-- The cosh powers are squeezed between `(1 + λu²/(n+1))^{n+1}` and `e^{λu²}`. -/
theorem cosh_pow_le_exp {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) (u : ℝ) :
    Real.cosh (flowShift lam n * u) ^ (n + 1) ≤ Real.exp (lam * u ^ 2) := by
  calc Real.cosh (flowShift lam n * u) ^ (n + 1)
      ≤ (Real.exp ((flowShift lam n * u) ^ 2 / 2)) ^ (n + 1) :=
        pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) _
    _ = Real.exp (lam * u ^ 2) := by
        rw [← Real.exp_nat_mul, mul_pow, flowShift_sq hlam]
        congr 1
        field_simp
        push_cast
        ring

theorem one_add_pow_le_cosh_pow {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) (u : ℝ) :
    (1 + lam * u ^ 2 / (n + 1)) ^ (n + 1) ≤ Real.cosh (flowShift lam n * u) ^ (n + 1) := by
  apply pow_le_pow_left₀ (by positivity)
  have := one_add_sq_div_two_le_cosh (flowShift lam n * u)
  rw [mul_pow, flowShift_sq hlam] at this
  calc 1 + lam * u ^ 2 / (n + 1) = 1 + 2 * lam / (n + 1) * u ^ 2 / 2 := by ring
    _ ≤ _ := this

theorem tendsto_cosh_pow {lam : ℝ} (hlam : 0 ≤ lam) (u : ℝ) :
    Tendsto (fun n : ℕ => Real.cosh (flowShift lam n * u) ^ (n + 1)) atTop (𝓝 (Real.exp (lam * u ^ 2))) := by
  have hlow : Tendsto (fun n : ℕ => (1 + lam * u ^ 2 / (n + 1)) ^ (n + 1)) atTop
      (𝓝 (Real.exp (lam * u ^ 2))) := by
    have := (Real.tendsto_one_add_div_pow_exp (lam * u ^ 2)).comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    push_cast
    rfl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => one_add_pow_le_cosh_pow hlam n u) (fun n => cosh_pow_le_exp hlam n u)

theorem integrable_coshApprox_integrand (lam : ℝ) (n : ℕ) (z : ℂ) :
    Integrable (fun u : ℝ =>
      ((Real.cosh (flowShift lam n * u) ^ (n + 1) : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)) := by
  have := integrable_coshStage_integrand (flowShift lam n) (n + 1) z
  have h2 : (fun u : ℝ => ((Real.cosh (flowShift lam n * u) ^ (n + 1) : ℝ) : ℂ) * Kker u *
      Complex.exp (I * z * u)) = fun u => ((2 : ℂ) ^ (n + 1))⁻¹ *
      ((((2 * Real.cosh (flowShift lam n * u)) ^ (n + 1) : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)) := by
    funext u; push_cast; field_simp; ring
  rw [h2]
  exact this.const_mul _

/-- The error integrand: `|e^{λu²} − cosh(h_n u)^{n+1}| ‖K(u)‖ e^{a|u|}`. -/
noncomputable def coshErr (lam a : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  |Real.exp (lam * u ^ 2) - Real.cosh (flowShift lam n * u) ^ (n + 1)| * ‖Kker u‖ * Real.exp (a * |u|)

theorem coshErr_le {lam : ℝ} (hlam : 0 ≤ lam) (a : ℝ) (n : ℕ) {M : ℝ}
    (hK : ∀ u, ‖Kker u‖ ≤ M * Dabs (1 / 2) (2 * Rc) u) (u : ℝ) :
    coshErr lam a n u ≤ M * Dq lam (1 / 2 + a) (2 * Rc) u := by
  unfold coshErr
  have h1 : |Real.exp (lam * u ^ 2) - Real.cosh (flowShift lam n * u) ^ (n + 1)| ≤ Real.exp (lam * u ^ 2) := by
    rw [abs_of_nonneg (by linarith [cosh_pow_le_exp hlam n u])]
    linarith [pow_nonneg (Real.cosh_pos (flowShift lam n * u)).le (n + 1)]
  have hM : 0 ≤ M := by
    have := (norm_nonneg (Kker 0)).trans (hK 0)
    have hD : 0 < Dabs (1 / 2) (2 * Rc) 0 := by unfold Dabs Dprof; positivity
    nlinarith
  calc |Real.exp (lam * u ^ 2) - Real.cosh (flowShift lam n * u) ^ (n + 1)| * ‖Kker u‖ * Real.exp (a * |u|)
      ≤ Real.exp (lam * u ^ 2) * (M * Dabs (1 / 2) (2 * Rc) u) * Real.exp (a * |u|) :=
        mul_le_mul (mul_le_mul h1 (hK u) (norm_nonneg _) (Real.exp_pos _).le) le_rfl
          (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (mul_nonneg hM (Dabs_nonneg _ _ _)))
    _ = M * (Real.exp (lam * u ^ 2) * (Dabs (1 / 2) (2 * Rc) u * Real.exp (a * |u|))) := by ring
    _ = M * Dq lam (1 / 2 + a) (2 * Rc) u := by rw [Dabs_mul_exp]; rfl

theorem continuous_coshErr (lam a : ℝ) (n : ℕ) : Continuous (coshErr lam a n) := by
  unfold coshErr
  have hK : Continuous (fun u : ℝ => ‖Kker u‖) := continuous_Kker.norm
  fun_prop

theorem tendsto_integral_coshErr {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => ∫ u : ℝ, coshErr lam a n u) atTop (𝓝 0) := by
  obtain ⟨M, hM, hK⟩ := Kker_bound
  have hbound : Integrable (fun u : ℝ => M * Dq lam (1 / 2 + a) (2 * Rc) u) :=
    (integrable_Dq hlam0 hlam (by positivity) (by have := Rc_pos; positivity)).const_mul M
  have := tendsto_integral_of_dominated_convergence (F := fun n => coshErr lam a n) (f := fun _ => 0)
    (fun u => M * Dq lam (1 / 2 + a) (2 * Rc) u)
    (fun n => (continuous_coshErr lam a n).aestronglyMeasurable) hbound
    (fun n => Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold coshErr; positivity)]
      exact coshErr_le hlam0 a n hK u)
    (Eventually.of_forall fun u => by
      unfold coshErr
      have h := (tendsto_cosh_pow hlam0 u).const_sub (Real.exp (lam * u ^ 2))
      rw [sub_self] at h
      have h2 := (h.abs).mul_const (‖Kker u‖ * Real.exp (a * |u|))
      simp only [abs_zero, zero_mul] at h2
      refine h2.congr fun n => ?_
      ring)
  have h0 : (∫ u : ℝ, (fun _ : ℝ => (0 : ℝ)) u) = 0 := by simp
  rw [← h0]
  exact this

/-- **Uniform convergence on horizontal strips.** -/
theorem tendstoUniformlyOn_coshApprox {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    TendstoUniformlyOn (coshApprox lam) (flowStage lam) atTop {z : ℂ | |z.im| ≤ a} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_order.1 (tendsto_integral_coshErr hlam0 hlam ha)).2 ε hε] with n hn z hz
  rw [dist_eq_norm]
  unfold flowStage coshApprox
  rw [← integral_sub (integrable_flow_integrand hlam0 hlam z) (integrable_coshApprox_integrand lam n z)]
  refine lt_of_le_of_lt ?_ hn
  refine norm_integral_le_of_norm_le ?_ (Eventually.of_forall fun u => ?_)
  · -- the error integrand is integrable
    obtain ⟨M, hM, hK⟩ := Kker_bound
    have hbound : Integrable (fun u : ℝ => M * Dq lam (1 / 2 + a) (2 * Rc) u) :=
      (integrable_Dq hlam0 hlam (by positivity) (by have := Rc_pos; positivity)).const_mul M
    refine hbound.mono' (continuous_coshErr lam a n).aestronglyMeasurable ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold coshErr; positivity)]
    exact coshErr_le hlam0 a n hK u
  · unfold coshErr
    rw [show ((Real.exp (lam * u ^ 2) : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u) -
        ((Real.cosh (flowShift lam n * u) ^ (n + 1) : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)
        = (((Real.exp (lam * u ^ 2) - Real.cosh (flowShift lam n * u) ^ (n + 1) : ℝ) : ℂ)) * Kker u *
          Complex.exp (I * z * u) by push_cast; ring]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := norm_exp_I_mul_le hz u
    exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Locally uniform convergence on `ℂ`.** -/
theorem tendstoLocallyUniformly_coshApprox {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1) :
    TendstoLocallyUniformly (coshApprox lam) (flowStage lam) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨A, hA⟩ := hK.isBounded.exists_norm_le
  refine (tendstoUniformlyOn_coshApprox hlam0 hlam (a := max A 0) (le_max_right _ _)).mono ?_
  intro z hz
  simp only [Set.mem_ofPred_eq]
  exact (Complex.abs_im_le_norm z).trans ((hA z hz).trans (le_max_left _ _))

/-! ### No weighted transform vanishes identically -/

theorem xiSection_zero_ne_zero : CriticalLinePhasor.XiChannel.xiSection 0 ≠ 0 := by
  intro h0
  have hmem := (ZD.riemannXi_eq_zero_iff _).mp (by simpa [CriticalLinePhasor.XiChannel.xiSection] using h0)
  obtain ⟨h0', h1, hz⟩ := hmem
  have him := riemannZeta_nontrivial_zero_im_ge_two hz (by
    intro n hn
    have := congrArg Complex.re hn
    simp at this
    linarith)
  simp at him
  linarith

/-- **A weighted transform is not identically zero:** for `w` continuous and nonvanishing with `w·K` integrable,
`z ↦ ∫ w(u) K(u) e^{izu} du` takes a nonzero value. -/
theorem weighted_transform_ne_zero (w : ℝ → ℝ) (hw : Continuous w) (hwne : ∀ u, w u ≠ 0)
    (hint : Integrable (fun u : ℝ => ((w u : ℝ) : ℂ) * Kker u)) :
    ∃ z : ℂ, (∫ u : ℝ, ((w u : ℝ) : ℂ) * Kker u * Complex.exp (I * z * u)) ≠ 0 := by
  by_contra hall
  push Not at hall
  set f : ℝ → ℂ := fun u => ((w u : ℝ) : ℂ) * Kker u with hf
  have hfc : Continuous f := (Complex.continuous_ofReal.comp hw).mul continuous_Kker
  have hF : 𝓕 f = 0 := by
    funext ξ
    rw [Pi.zero_apply, Real.fourier_real_eq_integral_exp_smul, ← hall (-(2 * Real.pi * ξ : ℝ))]
    congr 1
    funext v
    simp only [hf, smul_eq_mul]
    have he : Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * I)
        = Complex.exp (I * -((2 * Real.pi * ξ : ℝ) : ℂ) * (v : ℂ)) := by
      congr 1; push_cast; ring
    rw [he]
    ring
  have hinv := hfc.fourierInv_fourier_eq hint (by rw [hF]; exact integrable_zero _ _ _)
  rw [hF] at hinv
  have hzero : f = 0 := by
    rw [← hinv]
    funext v
    rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
    simp
  have hK : ∀ u, Kker u = 0 := by
    intro u
    have := congrFun hzero u
    simp only [hf, Pi.zero_apply, mul_eq_zero, Complex.ofReal_eq_zero] at this
    exact this.resolve_left (hwne u)
  apply xiSection_zero_ne_zero
  rw [xiSection_eq_Ktrans]
  unfold Ktrans
  simp [hK]

theorem coshStage_ne_zero (h : ℝ) (N : ℕ) : ∃ z : ℂ, coshStage h N z ≠ 0 := by
  refine weighted_transform_ne_zero (fun u => (2 * Real.cosh (h * u)) ^ N) (by fun_prop)
    (fun u => by have := Real.cosh_pos (h * u); positivity) ?_
  have := integrable_coshStage_integrand h N 0
  simpa using this

theorem flowStage_ne_zero {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1) : ∃ z : ℂ, flowStage lam z ≠ 0 := by
  refine weighted_transform_ne_zero (fun u => Real.exp (lam * u ^ 2)) (by fun_prop)
    (fun u => (Real.exp_pos _).ne') ?_
  have := integrable_flow_integrand hlam0 hlam 0
  simpa using this

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.shiftOp_iterate_Ktrans
#print axioms CriticalLinePhasor.XiKernel.tendstoLocallyUniformly_coshApprox
#print axioms CriticalLinePhasor.XiKernel.coshStage_ne_zero
#print axioms CriticalLinePhasor.XiKernel.flowStage_ne_zero
