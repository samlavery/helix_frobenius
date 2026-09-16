import RequestProject.FlowHeatEquation

/-!
# The warped fiber is Lipschitz in the warp parameter, uniformly on horizontal strips

`‖flowStage λ z − flowStage λ' z‖ ≤ |λ − λ'| · C(a)` for every `z` with `|Im z| ≤ a`.  This is stronger
than the locally uniform `λ`-continuity the Hurwitz step needs, and it comes straight out of
`lam_integrand_bound`: the `λ`-difference of the Gaussian weight is controlled by the `λ`-derivative's
integrand, `|e^{λu²} − e^{λ'u²}| ≤ |λ − λ'| u² e^{λ₁u²}`.
-/

open Complex MeasureTheory Filter Topology

namespace CriticalLinePhasor.XiKernel

/-- `|e^x − e^y| ≤ |x − y| · e^{max x y}`. -/
theorem abs_exp_sub_exp_le (x y : ℝ) :
    |Real.exp x - Real.exp y| ≤ |x - y| * Real.exp (max x y) := by
  have key : ∀ s t : ℝ, s ≤ t → Real.exp t - Real.exp s ≤ (t - s) * Real.exp t := by
    intro s t hst
    have h1 : 1 - (t - s) ≤ Real.exp (-(t - s)) := by
      have := Real.add_one_le_exp (-(t - s)); linarith
    have h3 : Real.exp s = Real.exp t * Real.exp (-(t - s)) := by
      rw [← Real.exp_add]; ring_nf
    have h4 : 0 < Real.exp t := Real.exp_pos t
    nlinarith
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr h)), abs_of_nonpos (by linarith),
      max_eq_right h]
    have := key x y h
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)), abs_of_nonneg (by linarith),
      max_eq_left h]
    have := key y x h
    linarith

/-- Pointwise `λ`-difference bound on the integrand, in terms of the `λ`-derivative's profile. -/
theorem flow_integrand_lam_diff_bound {lam lam' lam₁ : ℝ} (hl : lam ≤ lam₁) (hl' : lam' ≤ lam₁)
    {M : ℝ} (hK : ∀ u : ℝ, ‖Kker u‖ ≤ M * Dabs (1 / 2) (2 * Rc) u) {z : ℂ} {a : ℝ}
    (hz : |z.im| ≤ a) (u : ℝ) :
    ‖(((Real.exp (lam * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)
        - (((Real.exp (lam' * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)‖
      ≤ |lam - lam'| * ((4 * M) * Dq lam₁ (1 / 2 + (a + 1)) (2 * Rc) u) := by
  have hfac : (((Real.exp (lam * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)
      - (((Real.exp (lam' * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)
      = (((Real.exp (lam * u ^ 2) - Real.exp (lam' * u ^ 2) : ℝ)) : ℂ)
          * Kker u * Complex.exp (I * z * u) := by push_cast; ring
  rw [hfac, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  -- the exponential difference
  have hdiff : |Real.exp (lam * u ^ 2) - Real.exp (lam' * u ^ 2)|
      ≤ |lam - lam'| * (u ^ 2 * Real.exp (lam₁ * u ^ 2)) := by
    refine (abs_exp_sub_exp_le _ _).trans ?_
    have habs : |lam * u ^ 2 - lam' * u ^ 2| = |lam - lam'| * u ^ 2 := by
      rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg u)]
    have hmax : Real.exp (max (lam * u ^ 2) (lam' * u ^ 2)) ≤ Real.exp (lam₁ * u ^ 2) := by
      refine Real.exp_le_exp.mpr (max_le ?_ ?_) <;>
        exact mul_le_mul_of_nonneg_right (by assumption) (sq_nonneg u)
    rw [habs]
    calc |lam - lam'| * u ^ 2 * Real.exp (max (lam * u ^ 2) (lam' * u ^ 2))
        ≤ |lam - lam'| * u ^ 2 * Real.exp (lam₁ * u ^ 2) := by
          exact mul_le_mul_of_nonneg_left hmax (by positivity)
      _ = |lam - lam'| * (u ^ 2 * Real.exp (lam₁ * u ^ 2)) := by ring
  -- reassemble against the compiled λ-derivative bound
  have hbd := lam_integrand_bound (lam := lam₁) (lam₁ := lam₁) le_rfl hK hz u
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ u ^ 2 * Real.exp (lam₁ * u ^ 2))] at hbd
  have hKn : 0 ≤ ‖Kker u‖ := norm_nonneg _
  have hEn : 0 ≤ ‖Complex.exp (I * z * u)‖ := norm_nonneg _
  calc |Real.exp (lam * u ^ 2) - Real.exp (lam' * u ^ 2)| * ‖Kker u‖ * ‖Complex.exp (I * z * u)‖
      ≤ (|lam - lam'| * (u ^ 2 * Real.exp (lam₁ * u ^ 2))) * ‖Kker u‖
          * ‖Complex.exp (I * z * u)‖ := by
        gcongr
    _ = |lam - lam'| * (u ^ 2 * Real.exp (lam₁ * u ^ 2) * ‖Kker u‖
          * ‖Complex.exp (I * z * u)‖) := by ring
    _ ≤ |lam - lam'| * ((4 * M) * Dq lam₁ (1 / 2 + (a + 1)) (2 * Rc) u) := by
        exact mul_le_mul_of_nonneg_left hbd (abs_nonneg _)

/-- **Lipschitz in `λ`, uniformly on the strip `|Im z| ≤ a`.** -/
theorem flowStage_lipschitz_lam {lam₁ : ℝ} (h1 : lam₁ ≤ 1) (h1' : 0 ≤ lam₁) {a : ℝ}
    (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam lam' : ℝ, 0 ≤ lam → 0 ≤ lam' → lam ≤ lam₁ → lam' ≤ lam₁ →
      ∀ z : ℂ, |z.im| ≤ a →
      ‖flowStage lam z - flowStage lam' z‖ ≤ |lam - lam'| * C := by
  obtain ⟨M, hM, hK⟩ := Kker_bound
  have hMnn : 0 ≤ M := by
    have := (norm_nonneg (Kker 0)).trans (hK 0)
    have hD : 0 < Dabs (1 / 2) (2 * Rc) 0 := by unfold Dabs Dprof; positivity
    nlinarith
  have hint : Integrable (fun u : ℝ => (4 * M) * Dq lam₁ (1 / 2 + (a + 1)) (2 * Rc) u) :=
    (integrable_Dq h1' h1 (by linarith) (by have := Rc_pos; positivity)).const_mul (4 * M)
  refine ⟨∫ u : ℝ, (4 * M) * Dq lam₁ (1 / 2 + (a + 1)) (2 * Rc) u, ?_, ?_⟩
  · refine integral_nonneg fun u => ?_
    exact mul_nonneg (by positivity) (Dq_nonneg _ _ _ _)
  · intro lam lam' h0 h0' hl hl' z hz
    have hsub : flowStage lam z - flowStage lam' z
        = ∫ u : ℝ, ((((Real.exp (lam * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)
            - (((Real.exp (lam' * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)) := by
      rw [integral_sub (integrable_flow_integrand h0 (le_trans hl h1) z)
        (integrable_flow_integrand h0' (le_trans hl' h1) z)]
      rfl
    rw [hsub]
    calc ‖∫ u : ℝ, ((((Real.exp (lam * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)
            - (((Real.exp (lam' * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u))‖
        ≤ ∫ u : ℝ, |lam - lam'| * ((4 * M) * Dq lam₁ (1 / 2 + (a + 1)) (2 * Rc) u) := by
          refine norm_integral_le_of_norm_le (hint.const_mul _) ?_
          filter_upwards with u
          exact flow_integrand_lam_diff_bound hl hl' hK hz u
      _ = |lam - lam'| * ∫ u : ℝ, (4 * M) * Dq lam₁ (1 / 2 + (a + 1)) (2 * Rc) u := by
          rw [integral_const_mul]

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.flowStage_lipschitz_lam
