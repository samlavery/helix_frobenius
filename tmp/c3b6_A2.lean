import c3b6_A1

/-!
# C3 batch 6, block A2 — the modified-Bessel ODE for `K_{ix}`, proved

`kix j x A = ∫_{w>0} (-cosh w)^j e^{-A cosh w} cos(xw) dw` (block A1).  Here:

1. `hasDerivAt_kix` — **`kix (j+1)` IS the `A`-derivative of `kix j`**, by differentiation
   under the integral with the block-A1 Gaussian majorant.  So `kix 1 = K'`, `kix 2 = K''`.
2. `kix_bessel_ode` — **the modified-Bessel equation**
   `A²·K'' + A·K' − (A² − x²)·K = 0`,
   proved from the integral representation by two applications of FTC-2 on `(0,∞)`
   (`MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'`), with all boundary terms
   vanishing at both ends and every integrability side condition discharged by the
   majorant.  No asymptotics, no series, no analytic continuation.

The two integrations by parts are, with `g(w) = −sinh w · e^{-A cosh w}`:

* `g′(w) = (A sinh²w − cosh w)e^{-A cosh w}` and `g(0) = 0`, so
  `∫ g′ cos(xw) = x ∫ g sin(xw)`;
* `(e^{-A cosh w})′ = A·g(w)` and `e^{-A cosh 0}·sin 0 = 0`, so
  `A ∫ g sin(xw) = −x·K`;
* pointwise `A·cosh²w − cosh w − A = A sinh²w − cosh w`, so
  `A·K″ + K′ − A·K = ∫ g′ cos(xw)`.

Chaining: `A(A K″ + K′ − A K) = A x ∫ g sin = x·(−x K) = −x²K`, i.e. the ODE.

SCOPE: nothing here mentions `Ξ`, zeros, or RH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B6.Bessel

/-! ### 1. Elementary `sinh`/`cosh` comparisons -/

theorem abs_sinh_le_cosh (w : ℝ) : |Real.sinh w| ≤ Real.cosh w := by
  rw [abs_le, Real.sinh_eq, Real.cosh_eq]
  constructor <;> nlinarith [Real.exp_pos w, Real.exp_pos (-w)]

theorem sinh_sq_le_cosh_sq (w : ℝ) : Real.sinh w ^ 2 ≤ Real.cosh w ^ 2 := by
  have h := Real.cosh_sq_sub_sinh_sq w
  linarith

/-! ### 2. The majorant tends to zero -/

theorem coshMaj_tendsto_zero (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (coshMaj j δ) atTop (nhds 0) := by
  have hb : (0 : ℝ) < δ / 4 := by linarith
  have hev : ∀ᶠ w in atTop,
      ((j : ℝ) - δ / 2) * w - (δ / 4) * w ^ 2 ≤ -w := by
    filter_upwards [eventually_ge_atTop
      (max 0 ((((j : ℝ) - δ / 2) + 1) / (δ / 4)))] with w hw
    have hw0 : (0 : ℝ) ≤ w := le_trans (le_max_left _ _) hw
    have hw1 : (((j : ℝ) - δ / 2) + 1) / (δ / 4) ≤ w := le_trans (le_max_right _ _) hw
    have hw2 : ((j : ℝ) - δ / 2) + 1 ≤ (δ / 4) * w := by
      rw [div_le_iff₀ hb] at hw1
      linarith
    nlinarith
  have hq : Tendsto (fun w : ℝ => ((j : ℝ) - δ / 2) * w - (δ / 4) * w ^ 2) atTop atBot :=
    tendsto_atBot_mono' _ hev tendsto_neg_atTop_atBot
  have hexp : Tendsto (fun w : ℝ =>
      Real.exp (((j : ℝ) - δ / 2) * w - (δ / 4) * w ^ 2)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hq
  have heq : coshMaj j δ = fun w : ℝ =>
      Real.exp (-(δ / 2)) * Real.exp (((j : ℝ) - δ / 2) * w - (δ / 4) * w ^ 2) := rfl
  rw [heq]
  have h := hexp.const_mul (Real.exp (-(δ / 2)))
  rw [mul_zero] at h
  exact h

/-! ### 3. Differentiation under the integral sign -/

/-- Pointwise: `∂_A [(-cosh w)^j e^{-A cosh w} cos(xw)] = (-cosh w)^{j+1} e^{-A cosh w} cos(xw)`. -/
theorem hasDerivAt_kixTerm (j : ℕ) (x A w : ℝ) :
    HasDerivAt (fun a => kixTerm j x a w) (kixTerm (j + 1) x A w) A := by
  have hlin : HasDerivAt (fun a : ℝ => -(a * Real.cosh w)) (-Real.cosh w) A := by
    have h := ((hasDerivAt_id' (x := A)).mul_const (Real.cosh w)).neg
    refine h.congr_deriv ?_
    ring
  have hexp : HasDerivAt (fun a : ℝ => Real.exp (-(a * Real.cosh w)))
      (Real.exp (-(A * Real.cosh w)) * (-Real.cosh w)) A := hlin.exp
  have h := (hexp.const_mul ((-Real.cosh w) ^ j)).mul_const (Real.cos (x * w))
  refine h.congr_deriv ?_
  unfold kixTerm
  rw [pow_succ]
  ring

/-- **`kix (j+1)` is the `A`-derivative of `kix j`.**  Differentiation under the integral,
dominated on the neighbourhood `A' > A/2` by `coshMaj (j+1) (A/2)`. -/
theorem hasDerivAt_kix (j : ℕ) (x : ℝ) {A : ℝ} (hA : 0 < A) :
    HasDerivAt (kix j x) (kix (j + 1) x A) A := by
  have hδ : (0 : ℝ) < A / 2 := by linarith
  have hs : Ioi (A / 2) ∈ nhds A := isOpen_Ioi.mem_nhds (by simp only [mem_Ioi]; linarith)
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun a w => kixTerm j x a w) (F' := fun a w => kixTerm (j + 1) x a w)
    (x₀ := A) (bound := coshMaj (j + 1) (A / 2)) (s := Ioi (A / 2)) hs
    (Filter.Eventually.of_forall fun a => (kixTerm_continuous j x a).aestronglyMeasurable)
    (kixTerm_integrableOn j x hA)
    (kixTerm_continuous (j + 1) x A).aestronglyMeasurable
    ?_ ((coshMaj_integrable (j + 1) hδ).integrableOn)
    (Filter.Eventually.of_forall fun w a _ => hasDerivAt_kixTerm j x a w)).2
  · exact key
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with w hw a ha
    rw [Real.norm_eq_abs]
    exact kixTerm_abs_le hδ (le_of_lt ha) (le_of_lt hw)

/-! ### 4. The two auxiliary profiles -/

/-- `g(w) = −sinh w · e^{-A cosh w}`. -/
def gFun (A w : ℝ) : ℝ := -Real.sinh w * Real.exp (-(A * Real.cosh w))

/-- `g′(w) = (A sinh²w − cosh w)·e^{-A cosh w}`. -/
def gDer (A w : ℝ) : ℝ :=
  (A * Real.sinh w ^ 2 - Real.cosh w) * Real.exp (-(A * Real.cosh w))

theorem gFun_zero (A : ℝ) : gFun A 0 = 0 := by simp [gFun]

theorem hasDerivAt_gFun (A w : ℝ) : HasDerivAt (gFun A) (gDer A w) w := by
  have hq : HasDerivAt (fun v : ℝ => -(A * Real.cosh v)) (-(A * Real.sinh w)) w := by
    have h := ((Real.hasDerivAt_cosh w).const_mul A).neg
    refine h.congr_deriv ?_
    ring
  have hexp : HasDerivAt (fun v : ℝ => Real.exp (-(A * Real.cosh v)))
      (Real.exp (-(A * Real.cosh w)) * (-(A * Real.sinh w))) w := hq.exp
  have hs : HasDerivAt (fun v : ℝ => -Real.sinh v) (-Real.cosh w) w :=
    (Real.hasDerivAt_sinh w).neg
  have h := hs.mul hexp
  refine h.congr_deriv ?_
  unfold gDer
  have hcs := Real.cosh_sq_sub_sinh_sq w
  ring

/-- The exponential profile itself. -/
def eFun (A w : ℝ) : ℝ := Real.exp (-(A * Real.cosh w))

theorem hasDerivAt_eFun (A w : ℝ) : HasDerivAt (eFun A) (A * gFun A w) w := by
  have hq : HasDerivAt (fun v : ℝ => -(A * Real.cosh v)) (-(A * Real.sinh w)) w := by
    have h := ((Real.hasDerivAt_cosh w).const_mul A).neg
    refine h.congr_deriv ?_
    ring
  have hexp := hq.exp
  refine hexp.congr_deriv ?_
  unfold gFun
  ring

/-! ### 5. Integrability of the auxiliary integrands -/

theorem gFun_abs_le {A w : ℝ} (hA : 0 < A) (hw : 0 ≤ w) :
    |gFun A w| ≤ coshMaj 1 A w := by
  have h1 : |gFun A w| ≤ Real.cosh w ^ 1 * Real.exp (-(A * Real.cosh w)) := by
    unfold gFun
    rw [abs_mul, abs_neg, abs_of_nonneg (Real.exp_pos _).le, pow_one]
    exact mul_le_mul_of_nonneg_right (abs_sinh_le_cosh w) (Real.exp_pos _).le
  exact h1.trans (cosh_pow_exp_le hA le_rfl hw)

theorem eFun_abs_le {A w : ℝ} (hA : 0 < A) (hw : 0 ≤ w) :
    |eFun A w| ≤ coshMaj 0 A w := by
  have h1 : |eFun A w| ≤ Real.cosh w ^ 0 * Real.exp (-(A * Real.cosh w)) := by
    unfold eFun
    rw [abs_of_nonneg (Real.exp_pos _).le, pow_zero, one_mul]
  exact h1.trans (cosh_pow_exp_le hA le_rfl hw)

theorem gDer_abs_le {A w : ℝ} (hA : 0 < A) (hw : 0 ≤ w) :
    |gDer A w| ≤ A * coshMaj 2 A w + coshMaj 1 A w := by
  have hcs := sinh_sq_le_cosh_sq w
  have hs2 : (0 : ℝ) ≤ Real.sinh w ^ 2 := sq_nonneg _
  have hc1 : (1 : ℝ) ≤ Real.cosh w := one_le_cosh w
  have hE : (0 : ℝ) < Real.exp (-(A * Real.cosh w)) := Real.exp_pos _
  have h1 : |gDer A w|
      ≤ (A * Real.cosh w ^ 2 + Real.cosh w) * Real.exp (-(A * Real.cosh w)) := by
    unfold gDer
    rw [abs_mul, abs_of_nonneg hE.le]
    refine mul_le_mul_of_nonneg_right ?_ hE.le
    rw [abs_le]
    constructor <;> nlinarith
  have h2 : (A * Real.cosh w ^ 2 + Real.cosh w) * Real.exp (-(A * Real.cosh w))
      = A * (Real.cosh w ^ 2 * Real.exp (-(A * Real.cosh w)))
        + Real.cosh w ^ 1 * Real.exp (-(A * Real.cosh w)) := by
    rw [pow_one]; ring
  rw [h2] at h1
  refine h1.trans ?_
  have hb2 := cosh_pow_exp_le (j := 2) hA le_rfl hw
  have hb1 := cosh_pow_exp_le (j := 1) hA le_rfl hw
  have : A * (Real.cosh w ^ 2 * Real.exp (-(A * Real.cosh w))) ≤ A * coshMaj 2 A w :=
    mul_le_mul_of_nonneg_left hb2 hA.le
  linarith

/-- Generic integrability transfer from a pointwise bound on `Ioi 0`. -/
theorem integrableOn_of_bound {f b : ℝ → ℝ} (hf : Continuous f)
    (hb : IntegrableOn b (Ioi (0 : ℝ)))
    (hbd : ∀ w ∈ Ioi (0 : ℝ), |f w| ≤ b w) :
    IntegrableOn f (Ioi (0 : ℝ)) := by
  refine Integrable.mono hb hf.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with w hw
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (hbd w hw).trans (le_abs_self _)

theorem continuous_gFun (A : ℝ) : Continuous (gFun A) := by
  unfold gFun
  exact Real.continuous_sinh.neg.mul
    (Real.continuous_exp.comp (continuous_const.mul Real.continuous_cosh).neg)

theorem continuous_gDer (A : ℝ) : Continuous (gDer A) := by
  unfold gDer
  exact ((continuous_const.mul (Real.continuous_sinh.pow 2)).sub Real.continuous_cosh).mul
    (Real.continuous_exp.comp (continuous_const.mul Real.continuous_cosh).neg)

theorem continuous_eFun (A : ℝ) : Continuous (eFun A) :=
  Real.continuous_exp.comp (continuous_const.mul Real.continuous_cosh).neg

theorem integrableOn_gFun_sin (x : ℝ) {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun w => gFun A w * Real.sin (x * w)) (Ioi (0 : ℝ)) := by
  refine integrableOn_of_bound
    ((continuous_gFun A).mul (Real.continuous_sin.comp (continuous_const.mul continuous_id)))
    (coshMaj_integrableOn 1 hA) ?_
  intro w hw
  rw [abs_mul]
  calc |gFun A w| * |Real.sin (x * w)| ≤ |gFun A w| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
    _ = |gFun A w| := by ring
    _ ≤ coshMaj 1 A w := gFun_abs_le hA (le_of_lt hw)

theorem integrableOn_eFun_cos (x : ℝ) {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun w => eFun A w * Real.cos (x * w)) (Ioi (0 : ℝ)) := by
  refine integrableOn_of_bound
    ((continuous_eFun A).mul (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    (coshMaj_integrableOn 0 hA) ?_
  intro w hw
  rw [abs_mul]
  calc |eFun A w| * |Real.cos (x * w)| ≤ |eFun A w| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
    _ = |eFun A w| := by ring
    _ ≤ coshMaj 0 A w := eFun_abs_le hA (le_of_lt hw)

theorem integrableOn_gDer_cos (x : ℝ) {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun w => gDer A w * Real.cos (x * w)) (Ioi (0 : ℝ)) := by
  refine integrableOn_of_bound
    ((continuous_gDer A).mul (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    (((coshMaj_integrableOn 2 hA).const_mul A).add (coshMaj_integrableOn 1 hA)) ?_
  intro w hw
  rw [abs_mul]
  calc |gDer A w| * |Real.cos (x * w)| ≤ |gDer A w| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
    _ = |gDer A w| := by ring
    _ ≤ A * coshMaj 2 A w + coshMaj 1 A w := gDer_abs_le hA (le_of_lt hw)

/-! ### 6. The boundary behaviour at `+∞` -/

theorem tendsto_gFun_cos (x : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun w => gFun A w * Real.cos (x * w)) atTop (nhds 0) := by
  refine squeeze_zero_norm' ?_ (coshMaj_tendsto_zero 1 hA)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with w hw
  rw [Real.norm_eq_abs, abs_mul]
  calc |gFun A w| * |Real.cos (x * w)| ≤ |gFun A w| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
    _ = |gFun A w| := by ring
    _ ≤ coshMaj 1 A w := gFun_abs_le hA hw

theorem tendsto_eFun_sin (x : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun w => eFun A w * Real.sin (x * w)) atTop (nhds 0) := by
  refine squeeze_zero_norm' ?_ (coshMaj_tendsto_zero 0 hA)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with w hw
  rw [Real.norm_eq_abs, abs_mul]
  calc |eFun A w| * |Real.sin (x * w)| ≤ |eFun A w| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
    _ = |eFun A w| := by ring
    _ ≤ coshMaj 0 A w := eFun_abs_le hA hw

/-! ### 7. The two integrations by parts -/

/-- **First integration by parts.**  `∫ g′(w)cos(xw)dw = x·∫ g(w)sin(xw)dw`. -/
theorem ibp_one (x : ℝ) {A : ℝ} (hA : 0 < A) :
    (∫ w in Ioi (0 : ℝ), gDer A w * Real.cos (x * w))
      = x * ∫ w in Ioi (0 : ℝ), gFun A w * Real.sin (x * w) := by
  have hderiv : ∀ w ∈ Ici (0 : ℝ),
      HasDerivAt (fun v => gFun A v * Real.cos (x * v))
        (gDer A w * Real.cos (x * w) - x * (gFun A w * Real.sin (x * w))) w := by
    intro w _
    have hc : HasDerivAt (fun v : ℝ => Real.cos (x * v)) (-Real.sin (x * w) * x) w := by
      have hlin : HasDerivAt (fun v : ℝ => x * v) x w := by
        have h := (hasDerivAt_id' (x := w)).const_mul x
        refine h.congr_deriv ?_
        ring
      exact (Real.hasDerivAt_cos (x * w)).comp w hlin
    have h := (hasDerivAt_gFun A w).mul hc
    refine h.congr_deriv ?_
    ring
  have hint : IntegrableOn
      (fun w => gDer A w * Real.cos (x * w) - x * (gFun A w * Real.sin (x * w)))
      (Ioi (0 : ℝ)) :=
    (integrableOn_gDer_cos x hA).sub ((integrableOn_gFun_sin x hA).const_mul x)
  have hlim : Tendsto (fun w => gFun A w * Real.cos (x * w)) atTop (nhds 0) :=
    tendsto_gFun_cos x hA
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [gFun_zero, zero_mul, sub_zero] at hftc
  rw [integral_sub (integrableOn_gDer_cos x hA)
    ((integrableOn_gFun_sin x hA).const_mul x), integral_const_mul] at hftc
  linarith

/-- **Second integration by parts.**  `A·∫ g(w)sin(xw)dw = −x·K_{ix}(A)`. -/
theorem ibp_two (x : ℝ) {A : ℝ} (hA : 0 < A) :
    A * (∫ w in Ioi (0 : ℝ), gFun A w * Real.sin (x * w)) = -(x * kix 0 x A) := by
  have hderiv : ∀ w ∈ Ici (0 : ℝ),
      HasDerivAt (fun v => eFun A v * Real.sin (x * v))
        (A * (gFun A w * Real.sin (x * w)) + x * (eFun A w * Real.cos (x * w))) w := by
    intro w _
    have hs : HasDerivAt (fun v : ℝ => Real.sin (x * v)) (Real.cos (x * w) * x) w := by
      have hlin : HasDerivAt (fun v : ℝ => x * v) x w := by
        have h := (hasDerivAt_id' (x := w)).const_mul x
        refine h.congr_deriv ?_
        ring
      exact (Real.hasDerivAt_sin (x * w)).comp w hlin
    have h := (hasDerivAt_eFun A w).mul hs
    refine h.congr_deriv ?_
    ring
  have hint : IntegrableOn
      (fun w => A * (gFun A w * Real.sin (x * w)) + x * (eFun A w * Real.cos (x * w)))
      (Ioi (0 : ℝ)) :=
    ((integrableOn_gFun_sin x hA).const_mul A).add ((integrableOn_eFun_cos x hA).const_mul x)
  have hlim : Tendsto (fun w => eFun A w * Real.sin (x * w)) atTop (nhds 0) :=
    tendsto_eFun_sin x hA
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  have h0 : eFun A 0 * Real.sin (x * 0) = 0 := by simp
  rw [h0, sub_zero] at hftc
  rw [integral_add ((integrableOn_gFun_sin x hA).const_mul A)
    ((integrableOn_eFun_cos x hA).const_mul x), integral_const_mul, integral_const_mul] at hftc
  have hK : (∫ w in Ioi (0 : ℝ), eFun A w * Real.cos (x * w)) = kix 0 x A := by
    unfold kix kixTerm eFun
    simp
  rw [hK] at hftc
  linarith

/-! ### 8. The linear combination and the ODE -/

theorem combo_pointwise (x A w : ℝ) :
    A * kixTerm 2 x A w + kixTerm 1 x A w - A * kixTerm 0 x A w
      = gDer A w * Real.cos (x * w) := by
  unfold kixTerm gDer
  have hcs := Real.cosh_sq_sub_sinh_sq w
  linear_combination (A * Real.exp (-(A * Real.cosh w)) * Real.cos (x * w)) * hcs

theorem combo_integral (x : ℝ) {A : ℝ} (hA : 0 < A) :
    A * kix 2 x A + kix 1 x A - A * kix 0 x A
      = ∫ w in Ioi (0 : ℝ), gDer A w * Real.cos (x * w) := by
  have h2 := kixTerm_integrableOn 2 x hA
  have h1 := kixTerm_integrableOn 1 x hA
  have h0 := kixTerm_integrableOn 0 x hA
  have hcongr : (∫ w in Ioi (0 : ℝ), gDer A w * Real.cos (x * w))
      = ∫ w in Ioi (0 : ℝ),
          (A * kixTerm 2 x A w + kixTerm 1 x A w - A * kixTerm 0 x A w) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
    exact (combo_pointwise x A w).symm
  have e1 : (∫ w in Ioi (0 : ℝ),
        (A * kixTerm 2 x A w + kixTerm 1 x A w - A * kixTerm 0 x A w))
      = (∫ w in Ioi (0 : ℝ), (A * kixTerm 2 x A w + kixTerm 1 x A w))
        - ∫ w in Ioi (0 : ℝ), A * kixTerm 0 x A w :=
    integral_sub ((h2.const_mul A).add h1) (h0.const_mul A)
  have e2 : (∫ w in Ioi (0 : ℝ), (A * kixTerm 2 x A w + kixTerm 1 x A w))
      = (∫ w in Ioi (0 : ℝ), A * kixTerm 2 x A w)
        + ∫ w in Ioi (0 : ℝ), kixTerm 1 x A w :=
    integral_add (h2.const_mul A) h1
  rw [hcongr, e1, e2, integral_const_mul, integral_const_mul]
  rfl

/-- **THE MODIFIED-BESSEL ODE FOR `K_{ix}`.**  With `K = kix 0 x`, `K′ = kix 1 x`,
`K″ = kix 2 x` (`hasDerivAt_kix`),

  `A²·K″(A) + A·K′(A) − (A² − x²)·K(A) = 0`   for every `A > 0`.

Proved from the integral representation alone. -/
theorem kix_bessel_ode (x : ℝ) {A : ℝ} (hA : 0 < A) :
    A ^ 2 * kix 2 x A + A * kix 1 x A - (A ^ 2 - x ^ 2) * kix 0 x A = 0 := by
  have h1 := ibp_one x hA
  have h2 := ibp_two x hA
  have h3 := combo_integral x hA
  have hstep : A * (A * kix 2 x A + kix 1 x A - A * kix 0 x A)
      = A * (x * ∫ w in Ioi (0 : ℝ), gFun A w * Real.sin (x * w)) := by
    rw [h3, h1]
  have hstep2 : A * (x * ∫ w in Ioi (0 : ℝ), gFun A w * Real.sin (x * w))
      = x * (A * ∫ w in Ioi (0 : ℝ), gFun A w * Real.sin (x * w)) := by ring
  rw [hstep2, h2] at hstep
  nlinarith [hstep, hA]

/-- The `deriv` form: `K′ = kix 1`, `K″ = kix 2`, on `A > 0`. -/
theorem deriv_kix (j : ℕ) (x : ℝ) {A : ℝ} (hA : 0 < A) :
    deriv (kix j x) A = kix (j + 1) x A :=
  (hasDerivAt_kix j x hA).deriv

end C3B6.Bessel

section AxiomAudit
#print axioms C3B6.Bessel.abs_sinh_le_cosh
#print axioms C3B6.Bessel.coshMaj_tendsto_zero
#print axioms C3B6.Bessel.hasDerivAt_kixTerm
#print axioms C3B6.Bessel.hasDerivAt_kix
#print axioms C3B6.Bessel.hasDerivAt_gFun
#print axioms C3B6.Bessel.hasDerivAt_eFun
#print axioms C3B6.Bessel.integrableOn_gDer_cos
#print axioms C3B6.Bessel.tendsto_gFun_cos
#print axioms C3B6.Bessel.ibp_one
#print axioms C3B6.Bessel.ibp_two
#print axioms C3B6.Bessel.combo_pointwise
#print axioms C3B6.Bessel.combo_integral
#print axioms C3B6.Bessel.kix_bessel_ode
#print axioms C3B6.Bessel.deriv_kix
end AxiomAudit
