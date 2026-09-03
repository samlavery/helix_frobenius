import Mathlib
import RequestProject.WeilExplicitFormula

/-!
# Track W0 — the test class: smooth compactly supported profiles (ledger 534)

For `g : ℝ → ℂ` smooth with compact support, `F = laplaceTest g` (`F(s) = ∫ g(x) e^{(s−½)x} dx`)
is entire (`laplaceTest_differentiable`, differentiation under the integral) and has power decay
of order 4 on every strip (`laplaceTest_decay`, four integrations by parts:
`F(s) = (s−½)^{−4} · laplaceTest (g'''') s`). With W5 this gives the explicit formula with no
analytic hypothesis on `F`: `weil_explicit_formula_smooth`.

No `sorry`, no `axiom`.
-/

open Complex MeasureTheory Filter Topology
open scoped ContDiff Real

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-! ## Support radius -/

theorem exists_support_radius {g : ℝ → ℂ} (hsupp : HasCompactSupport g) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, R < |x| → g x = 0 := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp (IsCompact.isBounded hsupp)
  refine ⟨max r 0, le_max_right _ _, fun x hx => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hxs
  have := hr hxs
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  have := le_max_left r 0
  linarith

/-! ## Entireness -/

theorem laplaceTest_integrand_integrable {g : ℝ → ℂ} (hg : Continuous g)
    (hsupp : HasCompactSupport g) (s : ℂ) :
    Integrable (fun x : ℝ => g x * Complex.exp ((s - 1 / 2) * x)) :=
  (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hsupp.mul_right

theorem laplaceTest_hasDerivAt {g : ℝ → ℂ} (hg : Continuous g) (hsupp : HasCompactSupport g)
    (s₀ : ℂ) :
    HasDerivAt (laplaceTest g) (∫ x : ℝ, g x * (x * Complex.exp ((s₀ - 1 / 2) * x))) s₀ := by
  have hball : Metric.ball s₀ 1 ∈ 𝓝 s₀ := Metric.ball_mem_nhds s₀ one_pos
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) hball
    (F := fun s : ℂ => fun x : ℝ => g x * Complex.exp ((s - 1 / 2) * x))
    (F' := fun s : ℂ => fun x : ℝ => g x * (x * Complex.exp ((s - 1 / 2) * x)))
    (bound := fun x : ℝ => ‖g x‖ * (|x| * Real.exp ((‖s₀‖ + 3 / 2) * |x|)))
    (Filter.Eventually.of_forall (fun s =>
      (laplaceTest_integrand_integrable hg hsupp s).aestronglyMeasurable))
    (laplaceTest_integrand_integrable hg hsupp s₀)
    ((hg.mul (by fun_prop)).aestronglyMeasurable)
    ?_ ?_ ?_
  · exact h.2
  · refine Filter.Eventually.of_forall (fun x s hs => ?_)
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.exp_le_exp.mpr
    have hre : ((s - 1 / 2) * (x : ℂ)).re = (s.re - 1 / 2) * x := by simp
    rw [hre]
    have h1 : (s.re - 1 / 2) * x ≤ |s.re - 1 / 2| * |x| := by
      rw [← abs_mul]
      exact le_abs_self _
    have h2 : |s.re - 1 / 2| ≤ ‖s₀‖ + 3 / 2 := by
      have hs' : ‖s - s₀‖ < 1 := by
        rw [Metric.mem_ball, dist_eq_norm] at hs
        exact hs
      have : |s.re - 1 / 2| ≤ |s.re| + 1 / 2 := by
        have := abs_sub s.re (1 / 2)
        simpa using this
      have h3 : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
      have h4 : ‖s‖ ≤ ‖s₀‖ + 1 := by
        have := norm_sub_norm_le s s₀
        linarith
      linarith
    calc (s.re - 1 / 2) * x ≤ |s.re - 1 / 2| * |x| := h1
      _ ≤ (‖s₀‖ + 3 / 2) * |x| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  · exact ((hg.norm.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hsupp.comp_left norm_zero).mul_right)
  · refine Filter.Eventually.of_forall (fun x s _ => ?_)
    have h1 : HasDerivAt (fun w : ℂ => Complex.exp ((w - 1 / 2) * x))
        (Complex.exp ((s - 1 / 2) * x) * x) s := by
      have := (((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).mul_const (x : ℂ)).cexp
      simpa using this
    have := h1.const_mul (g x)
    refine this.congr_deriv ?_
    ring

theorem laplaceTest_differentiable {g : ℝ → ℂ} (hg : Continuous g) (hsupp : HasCompactSupport g) :
    Differentiable ℂ (laplaceTest g) :=
  fun s => (laplaceTest_hasDerivAt hg hsupp s).differentiableAt

/-! ## Integration by parts -/

theorem hasCompactSupport_mul_tendsto_zero {h : ℝ → ℂ} (hsupp : HasCompactSupport h) (v : ℝ → ℂ) :
    Tendsto (fun x : ℝ => h x * v x) atTop (𝓝 0) ∧
      Tendsto (fun x : ℝ => h x * v x) atBot (𝓝 0) := by
  obtain ⟨R, hR0, hR⟩ := exists_support_radius hsupp
  constructor
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop R] with x hx
    rw [hR x (by rw [abs_of_pos (by linarith)]; linarith), zero_mul]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_atBot (-R)] with x hx
    rw [hR x (by rw [abs_of_neg (by linarith)]; linarith), zero_mul]

theorem hasDerivAt_exp_line (s : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp ((s - 1 / 2) * y))
      ((s - 1 / 2) * Complex.exp ((s - 1 / 2) * x)) x := by
  have h1 : HasDerivAt (fun w : ℂ => Complex.exp ((s - 1 / 2) * w))
      (Complex.exp ((s - 1 / 2) * x) * (s - 1 / 2)) (x : ℂ) := by
    have := ((hasDerivAt_id (x : ℂ)).const_mul (s - 1 / 2)).cexp
    simpa using this
  have := h1.comp_ofReal
  refine this.congr_deriv ?_
  ring

/-- **One integration by parts**: `laplaceTest h s = −(s−½)⁻¹ · laplaceTest (deriv h) s`. -/
theorem laplaceTest_deriv_step {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h)
    {s : ℂ} (hs : s ≠ 1 / 2) :
    laplaceTest h s = -(s - 1 / 2)⁻¹ * laplaceTest (deriv h) s := by
  have hs0 : s - 1 / 2 ≠ 0 := sub_ne_zero.mpr hs
  have hdiff : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hcont' : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hu : ∀ x, HasDerivAt h (deriv h x) x := fun x => (hdiff x).hasDerivAt
  have hv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp ((s - 1 / 2) * y) / (s - 1 / 2))
      (Complex.exp ((s - 1 / 2) * x)) x := by
    intro x
    have := (hasDerivAt_exp_line s x).div_const (s - 1 / 2)
    refine this.congr_deriv ?_
    exact mul_div_cancel_left₀ _ hs0
  have huv' : Integrable (h * fun y : ℝ => Complex.exp ((s - 1 / 2) * y)) :=
    laplaceTest_integrand_integrable hh.continuous hsupp s
  have hu'v : Integrable (deriv h * fun y : ℝ => Complex.exp ((s - 1 / 2) * y) / (s - 1 / 2)) :=
    (hcont'.mul (by fun_prop)).integrable_of_hasCompactSupport hsupp.deriv.mul_right
  obtain ⟨htop, hbot⟩ := hasCompactSupport_mul_tendsto_zero hsupp
    (fun y : ℝ => Complex.exp ((s - 1 / 2) * y) / (s - 1 / 2))
  have key := integral_mul_deriv_eq_deriv_mul (u := h) (u' := deriv h)
    (v := fun y : ℝ => Complex.exp ((s - 1 / 2) * y) / (s - 1 / 2))
    (v' := fun y : ℝ => Complex.exp ((s - 1 / 2) * y))
    (fun x _ => hu x) (fun x _ => hv x) huv' hu'v hbot htop
  unfold laplaceTest
  rw [key, sub_zero, zero_sub]
  have : ∫ x : ℝ, deriv h x * (Complex.exp ((s - 1 / 2) * x) / (s - 1 / 2))
      = (∫ x : ℝ, deriv h x * Complex.exp ((s - 1 / 2) * x)) / (s - 1 / 2) := by
    rw [← integral_div]
    congr 1
    funext x
    ring
  rw [this]
  field_simp

theorem hasCompactSupport_iterate_deriv {g : ℝ → ℂ} (hsupp : HasCompactSupport g) (n : ℕ) :
    HasCompactSupport (deriv^[n] g) := by
  induction n with
  | zero => exact hsupp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.deriv

/-- **Four integrations by parts**: `laplaceTest g s = (s−½)^{−4} · laplaceTest (g'''') s`. -/
theorem laplaceTest_eq_fourth_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hsupp : HasCompactSupport g)
    {s : ℂ} (hs : s ≠ 1 / 2) :
    laplaceTest g s = ((s - 1 / 2)⁻¹) ^ 4 * laplaceTest (deriv^[4] g) s := by
  have hstep : ∀ n : ℕ, laplaceTest (deriv^[n] g) s
      = -(s - 1 / 2)⁻¹ * laplaceTest (deriv^[n + 1] g) s := by
    intro n
    rw [Function.iterate_succ_apply']
    exact laplaceTest_deriv_step ((hg.iterate_deriv n).of_le (by exact_mod_cast le_top))
      (hasCompactSupport_iterate_deriv hsupp n) hs
  have h0 := hstep 0
  have h1 := hstep 1
  have h2 := hstep 2
  have h3 := hstep 3
  simp only [Function.iterate_zero, id] at h0
  rw [h0, h1, h2, h3]
  ring

/-! ## Decay on a strip -/

/-- The elementary bound `‖laplaceTest h (σ + it)‖ ≤ e^{MR} ∫‖h‖` for `|σ − ½| ≤ M` and
`supp h ⊆ [−R, R]`. -/
theorem laplaceTest_norm_le {h : ℝ → ℂ} (hh : Continuous h) (hsupp : HasCompactSupport h)
    {R : ℝ} (_hR0 : 0 ≤ R) (hR : ∀ x : ℝ, R < |x| → h x = 0) {M : ℝ} (hM0 : 0 ≤ M)
    {σ : ℝ} (hσ : |σ - 1 / 2| ≤ M) (t : ℝ) :
    ‖laplaceTest h (σ + t * I)‖ ≤ Real.exp (M * R) * ∫ x : ℝ, ‖h x‖ := by
  unfold laplaceTest
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le
    ((hh.norm.integrable_of_hasCompactSupport (hsupp.comp_left norm_zero)).const_mul _)
    (Filter.Eventually.of_forall (fun x => ?_))
  rw [norm_mul, Complex.norm_exp]
  have hre : (((σ : ℂ) + t * I - 1 / 2) * (x : ℂ)).re = (σ - 1 / 2) * x := by simp
  rw [hre]
  by_cases hx : h x = 0
  · rw [hx, norm_zero, zero_mul, mul_zero]
  · have hxR : |x| ≤ R := by
      by_contra hcon
      exact hx (hR x (lt_of_not_ge hcon))
    have : (σ - 1 / 2) * x ≤ M * R := by
      calc (σ - 1 / 2) * x ≤ |σ - 1 / 2| * |x| := by rw [← abs_mul]; exact le_abs_self _
        _ ≤ M * R := mul_le_mul hσ hxR (abs_nonneg _) hM0
    calc ‖h x‖ * Real.exp ((σ - 1 / 2) * x) ≤ ‖h x‖ * Real.exp (M * R) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr this) (norm_nonneg _)
      _ = Real.exp (M * R) * ‖h x‖ := mul_comm _ _

theorem norm_line_sub_half_ge (σ t : ℝ) : |t| ≤ ‖(σ : ℂ) + t * I - 1 / 2‖ := by
  have := Complex.abs_im_le_norm ((σ : ℂ) + t * I - 1 / 2)
  have him : ((σ : ℂ) + t * I - 1 / 2).im = t := by simp
  rwa [him] at this

/-- **Decay of order 4 on every strip** for a smooth compactly supported profile. -/
theorem laplaceTest_decay {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hsupp : HasCompactSupport g)
    (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc a b, ∀ T : ℝ,
      ‖laplaceTest g (x + T * I)‖ ≤ C / (1 + |T|) ^ 4 := by
  obtain ⟨R, hR0, hR⟩ := exists_support_radius hsupp
  set M : ℝ := max |a - 1 / 2| |b - 1 / 2| with hM
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (le_max_left _ _)
  have hg4 : ContDiff ℝ ∞ (deriv^[4] g) := hg.iterate_deriv 4
  have hsupp4 : HasCompactSupport (deriv^[4] g) := hasCompactSupport_iterate_deriv hsupp 4
  have hR4 : ∀ x : ℝ, R < |x| → deriv^[4] g x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxs
    -- the support of the derivatives is contained in the support of `g`
    have hsub : tsupport (deriv^[4] g) ⊆ tsupport g := by
      have h1 : ∀ n : ℕ, tsupport (deriv^[n + 1] g) ⊆ tsupport (deriv^[n] g) := by
        intro n
        rw [Function.iterate_succ_apply']
        exact tsupport_deriv_subset
      exact (h1 3).trans ((h1 2).trans ((h1 1).trans (h1 0)))
    have hx0 : g x = 0 := hR x hx
    have hxt : x ∈ tsupport g := hsub hxs
    -- `x ∈ tsupport g` with `R < |x|`: contradiction with the support radius via closure
    have hopen : ∀ y ∈ {y : ℝ | R < |y|}, g y = 0 := fun y hy => hR y hy
    have hclosed : tsupport g ⊆ {y : ℝ | |y| ≤ R} := by
      apply closure_minimal
      · intro y hy
        by_contra hcon
        exact hy (hR y (lt_of_not_ge hcon))
      · exact isClosed_le continuous_abs continuous_const
    have : |x| ≤ R := hclosed hxt
    linarith
  set K0 : ℝ := Real.exp (M * R) * ∫ x : ℝ, ‖g x‖ with hK0
  set K4 : ℝ := Real.exp (M * R) * ∫ x : ℝ, ‖deriv^[4] g x‖ with hK4
  have hK0nn : 0 ≤ K0 := mul_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => norm_nonneg _))
  have hK4nn : 0 ≤ K4 := mul_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => norm_nonneg _))
  refine ⟨16 * max K0 K4, by positivity, fun σ hσ T => ?_⟩
  have hσM : |σ - 1 / 2| ≤ M := by
    rcases le_or_gt σ (1 / 2) with h | h
    · calc |σ - 1 / 2| = 1 / 2 - σ := by rw [abs_of_nonpos (by linarith)]; ring
        _ ≤ 1 / 2 - a := by linarith [hσ.1]
        _ ≤ |a - 1 / 2| := by rw [abs_sub_comm]; exact le_abs_self _
        _ ≤ M := le_max_left _ _
    · calc |σ - 1 / 2| = σ - 1 / 2 := abs_of_pos (by linarith)
        _ ≤ b - 1 / 2 := by linarith [hσ.2]
        _ ≤ |b - 1 / 2| := le_abs_self _
        _ ≤ M := le_max_right _ _
  have hbound0 : ‖laplaceTest g (σ + T * I)‖ ≤ K0 :=
    laplaceTest_norm_le hg.continuous hsupp hR0 hR hM0 hσM T
  have hpos : (0 : ℝ) < (1 + |T|) ^ 4 := by positivity
  rcases le_or_gt |T| 1 with hT | hT
  · -- small `|T|`: `(1+|T|)^4 ≤ 16`
    have h16 : (1 + |T|) ^ 4 ≤ 16 := by
      have : 1 + |T| ≤ 2 := by linarith
      calc (1 + |T|) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (by positivity) this 4
        _ = 16 := by norm_num
    calc ‖laplaceTest g (σ + T * I)‖ ≤ K0 := hbound0
      _ ≤ max K0 K4 := le_max_left _ _
      _ = 16 * max K0 K4 / 16 := by ring
      _ ≤ 16 * max K0 K4 / (1 + |T|) ^ 4 :=
          div_le_div_of_nonneg_left (by positivity) hpos h16
  · -- large `|T|`: use the fourth derivative
    have hs : ((σ : ℂ) + T * I) ≠ 1 / 2 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      rw [this, abs_zero] at hT
      linarith
    have hdist : |T| ≤ ‖(σ : ℂ) + T * I - 1 / 2‖ := norm_line_sub_half_ge σ T
    have hTpos : 0 < |T| := by linarith
    have hbound4 : ‖laplaceTest g (σ + T * I)‖ ≤ K4 / |T| ^ 4 := by
      rw [laplaceTest_eq_fourth_deriv hg hsupp hs, norm_mul, norm_pow, norm_inv]
      have h4 := laplaceTest_norm_le hg4.continuous hsupp4 hR0 hR4 hM0 hσM T
      have hinv : ‖(σ : ℂ) + T * I - 1 / 2‖⁻¹ ^ 4 ≤ (|T|⁻¹) ^ 4 := by
        apply pow_le_pow_left₀ (by positivity)
        exact inv_anti₀ hTpos hdist
      calc ‖(σ : ℂ) + T * I - 1 / 2‖⁻¹ ^ 4 * ‖laplaceTest (deriv^[4] g) (σ + T * I)‖
          ≤ (|T|⁻¹) ^ 4 * K4 := mul_le_mul hinv h4 (norm_nonneg _) (by positivity)
        _ = K4 / |T| ^ 4 := by rw [inv_pow]; ring
    have h16 : (1 + |T|) ^ 4 ≤ 16 * |T| ^ 4 := by
      have : 1 + |T| ≤ 2 * |T| := by linarith
      calc (1 + |T|) ^ 4 ≤ (2 * |T|) ^ 4 := pow_le_pow_left₀ (by positivity) this 4
        _ = 16 * |T| ^ 4 := by ring
    calc ‖laplaceTest g (σ + T * I)‖ ≤ K4 / |T| ^ 4 := hbound4
      _ ≤ max K0 K4 / |T| ^ 4 := div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = 16 * max K0 K4 / (16 * |T| ^ 4) := by
          rw [mul_div_mul_left _ _ (by norm_num : (16 : ℝ) ≠ 0)]
      _ ≤ 16 * max K0 K4 / (1 + |T|) ^ 4 :=
          div_le_div_of_nonneg_left (by positivity) hpos h16

/-- **Weil's explicit formula for smooth compactly supported profiles** (strip `[a, b]`,
`a < 0 < 1 < b`). -/
theorem weil_explicit_formula_smooth {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hsupp : HasCompactSupport g) {a b : ℝ} (ha : a < 0) (hb : 1 < b) :
    ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * laplaceTest g ρ.val
      = (1 / (2 * π)) * ((∫ t : ℝ, laplaceTest g (b + t * I) * weilArch (b + t * I))
          + (∫ t : ℝ, laplaceTest g (a + t * I) * weilArch (1 - ((a : ℂ) + t * I))))
        - ∑' n : ℕ, primeWeight n * (g (Real.log n) + g (-Real.log n)) := by
  obtain ⟨C, hC, hdec⟩ := laplaceTest_decay hg hsupp a b
  exact weil_explicit_formula hg.continuous hsupp (laplaceTest_differentiable hg.continuous hsupp)
    (le_refl 4) hC ha hb hdec

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.laplaceTest_differentiable
#print axioms CriticalLinePhasor.ContourArgument.laplaceTest_decay
#print axioms CriticalLinePhasor.ContourArgument.weil_explicit_formula_smooth
