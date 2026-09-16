import RequestProject.FlowLambdaLipschitz

/-!
# The warp-derivative `J(s,z) = ∂_λ Ξ_s(z)` is Lipschitz in `s`, uniformly on horizontal strips

The merger argument needs the SIGN of `∂_λΞ_s(x)` on a two-dimensional neighbourhood of `(λ₀, x₀)`.
It is obtained from two one-dimensional facts:
* `flowLamDeriv_lipschitz_lam` (here) — `‖J(s,z) − J(s',z)‖ ≤ |s − s'|·C(a)` for `|Im z| ≤ a`;
* continuity of `J(λ₀, ·)` at `x₀`, which is free because `Ξ_{λ₀}` is entire.

The weight carries an extra `u²` relative to `flowStage`, and `u⁴ ≤ 4·u²·e^{|u|}` absorbs it into the
same profile `Dq`.
-/

open Complex MeasureTheory Filter Topology

namespace CriticalLinePhasor.XiKernel

/-- The `λ`-derivative of the warped fiber, as a function of `(s, z)`. -/
noncomputable def flowLamDeriv (s : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, (((u ^ 2 * Real.exp (s * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)

theorem hasDerivAt_flowStage_lam' {lam₀ lam₁ : ℝ} (h0 : 0 ≤ lam₀) (hlt : lam₀ < lam₁)
    (h1 : lam₁ ≤ 1) (z : ℂ) :
    HasDerivAt (fun lam : ℝ => flowStage lam z) (flowLamDeriv lam₀ z) lam₀ :=
  hasDerivAt_flowStage_lam h0 hlt h1 z

/-- `u⁴ ≤ 4 u² e^{|u|}`: the extra weight is absorbed into the same profile. -/
theorem sq_sq_le (u : ℝ) : u ^ 2 * u ^ 2 ≤ u ^ 2 * (4 * Real.exp |u|) :=
  mul_le_mul_of_nonneg_left (sq_le_four_mul_exp_abs u) (sq_nonneg u)

/-- Pointwise `s`-difference bound for the `λ`-derivative's integrand. -/
theorem lam_integrand_diff_bound {s s' lam₁ : ℝ} (hl : s ≤ lam₁) (hl' : s' ≤ lam₁)
    {M : ℝ} (hK : ∀ u : ℝ, ‖Kker u‖ ≤ M * Dabs (1 / 2) (2 * Rc) u) (hM : 0 ≤ M) {z : ℂ} {a : ℝ}
    (hz : |z.im| ≤ a) (u : ℝ) :
    ‖(((u ^ 2 * Real.exp (s * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)
        - (((u ^ 2 * Real.exp (s' * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)‖
      ≤ |s - s'| * ((16 * M) * Dq lam₁ (1 / 2 + (a + 2)) (2 * Rc) u) := by
  have hfac : (((u ^ 2 * Real.exp (s * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)
      - (((u ^ 2 * Real.exp (s' * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)
      = (((u ^ 2 * (Real.exp (s * u ^ 2) - Real.exp (s' * u ^ 2)) : ℝ)) : ℂ)
          * Kker u * Complex.exp (I * z * u) := by push_cast; ring
  rw [hfac, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hdiff : |Real.exp (s * u ^ 2) - Real.exp (s' * u ^ 2)|
      ≤ |s - s'| * (u ^ 2 * Real.exp (lam₁ * u ^ 2)) := by
    refine (abs_exp_sub_exp_le _ _).trans ?_
    have habs : |s * u ^ 2 - s' * u ^ 2| = |s - s'| * u ^ 2 := by
      rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg u)]
    have hmax : Real.exp (max (s * u ^ 2) (s' * u ^ 2)) ≤ Real.exp (lam₁ * u ^ 2) := by
      refine Real.exp_le_exp.mpr (max_le ?_ ?_) <;>
        exact mul_le_mul_of_nonneg_right (by assumption) (sq_nonneg u)
    rw [habs]
    calc |s - s'| * u ^ 2 * Real.exp (max (s * u ^ 2) (s' * u ^ 2))
        ≤ |s - s'| * u ^ 2 * Real.exp (lam₁ * u ^ 2) :=
          mul_le_mul_of_nonneg_left hmax (by positivity)
      _ = |s - s'| * (u ^ 2 * Real.exp (lam₁ * u ^ 2)) := by ring
  have hnormprod : |u ^ 2 * (Real.exp (s * u ^ 2) - Real.exp (s' * u ^ 2))|
      ≤ |s - s'| * (u ^ 2 * u ^ 2 * Real.exp (lam₁ * u ^ 2)) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg u)]
    calc u ^ 2 * |Real.exp (s * u ^ 2) - Real.exp (s' * u ^ 2)|
        ≤ u ^ 2 * (|s - s'| * (u ^ 2 * Real.exp (lam₁ * u ^ 2))) :=
          mul_le_mul_of_nonneg_left hdiff (sq_nonneg u)
      _ = |s - s'| * (u ^ 2 * u ^ 2 * Real.exp (lam₁ * u ^ 2)) := by ring
  have hKu := hK u
  have hexpz := norm_exp_I_mul_le hz u
  have hDnn := Dabs_nonneg (1 / 2) (2 * Rc) u
  have hu4 := sq_sq_le u
  have hu2 := sq_le_four_mul_exp_abs u
  -- assemble
  have hu4' : u ^ 2 * u ^ 2 ≤ 16 * (Real.exp |u| * Real.exp |u|) := by
    have h := mul_le_mul hu2 hu2 (sq_nonneg u) (by positivity : (0:ℝ) ≤ 4 * Real.exp |u|)
    nlinarith [Real.exp_pos |u|]
  have hmain : u ^ 2 * u ^ 2 * Real.exp (lam₁ * u ^ 2)
      ≤ 16 * (Real.exp |u| * Real.exp |u|) * Real.exp (lam₁ * u ^ 2) :=
    mul_le_mul_of_nonneg_right hu4' (Real.exp_pos _).le
  calc |u ^ 2 * (Real.exp (s * u ^ 2) - Real.exp (s' * u ^ 2))| * ‖Kker u‖
        * ‖Complex.exp (I * z * u)‖
      ≤ (|s - s'| * (u ^ 2 * u ^ 2 * Real.exp (lam₁ * u ^ 2)))
          * (M * Dabs (1 / 2) (2 * Rc) u) * Real.exp (a * |u|) := by
        gcongr
    _ ≤ (|s - s'| * (16 * (Real.exp |u| * Real.exp |u|) * Real.exp (lam₁ * u ^ 2)))
          * (M * Dabs (1 / 2) (2 * Rc) u) * Real.exp (a * |u|) := by
        gcongr
    _ = |s - s'| * ((16 * M) * (Real.exp (lam₁ * u ^ 2)
          * (Dabs (1 / 2) (2 * Rc) u * Real.exp (a * |u|) * Real.exp (2 * |u|)))) := by
        rw [show Real.exp (2 * |u|) = Real.exp |u| * Real.exp |u| by
          rw [← Real.exp_add]; ring_nf]
        ring
    _ = |s - s'| * ((16 * M) * Dq lam₁ (1 / 2 + (a + 2)) (2 * Rc) u) := by
        rw [Dabs_mul_exp, Dabs_mul_exp]
        unfold Dq
        rw [show (1 / 2 + a + 2 : ℝ) = 1 / 2 + (a + 2) by ring]

/-- **`J(·, z)` is Lipschitz in the warp parameter, uniformly on `|Im z| ≤ a`.** -/
theorem flowLamDeriv_lipschitz_lam {lam₁ : ℝ} (h1 : lam₁ ≤ 1) (h1' : 0 ≤ lam₁) {a : ℝ}
    (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s s' : ℝ, 0 ≤ s → 0 ≤ s' → s ≤ lam₁ → s' ≤ lam₁ →
      ∀ z : ℂ, |z.im| ≤ a → ‖flowLamDeriv s z - flowLamDeriv s' z‖ ≤ |s - s'| * C := by
  obtain ⟨M, hM, hK⟩ := Kker_bound
  have hMnn : 0 ≤ M := by
    have := (norm_nonneg (Kker 0)).trans (hK 0)
    have hD : 0 < Dabs (1 / 2) (2 * Rc) 0 := by unfold Dabs Dprof; positivity
    nlinarith
  have hint : Integrable (fun u : ℝ => (16 * M) * Dq lam₁ (1 / 2 + (a + 2)) (2 * Rc) u) :=
    (integrable_Dq h1' h1 (by linarith) (by have := Rc_pos; positivity)).const_mul (16 * M)
  refine ⟨∫ u : ℝ, (16 * M) * Dq lam₁ (1 / 2 + (a + 2)) (2 * Rc) u, ?_, ?_⟩
  · exact integral_nonneg fun u => mul_nonneg (by positivity) (Dq_nonneg _ _ _ _)
  · intro s s' hs hs' hsl hsl' z hz
    have hdom : Integrable (fun u : ℝ => (4 * M) * Dq lam₁ (1 / 2 + (a + 1)) (2 * Rc) u) :=
      (integrable_Dq h1' h1 (by linarith) (by have := Rc_pos; positivity)).const_mul (4 * M)
    have hIs : Integrable (fun u : ℝ =>
        (((u ^ 2 * Real.exp (s * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)) := by
      refine hdom.mono' (continuous_lam_integrand s z).aestronglyMeasurable ?_
      filter_upwards with u
      exact lam_integrand_bound hsl hK hz u
    have hIs' : Integrable (fun u : ℝ =>
        (((u ^ 2 * Real.exp (s' * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)) := by
      refine hdom.mono' (continuous_lam_integrand s' z).aestronglyMeasurable ?_
      filter_upwards with u
      exact lam_integrand_bound hsl' hK hz u
    unfold flowLamDeriv
    rw [← integral_sub hIs hIs']
    calc ‖∫ u : ℝ, ((((u ^ 2 * Real.exp (s * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u)
            - (((u ^ 2 * Real.exp (s' * u ^ 2) : ℝ)) : ℂ) * Kker u * Complex.exp (I * z * u))‖
        ≤ ∫ u : ℝ, |s - s'| * ((16 * M) * Dq lam₁ (1 / 2 + (a + 2)) (2 * Rc) u) := by
          refine norm_integral_le_of_norm_le (hint.const_mul _) ?_
          filter_upwards with u
          exact lam_integrand_diff_bound hsl hsl' hK hMnn hz u
      _ = |s - s'| * ∫ u : ℝ, (16 * M) * Dq lam₁ (1 / 2 + (a + 2)) (2 * Rc) u := by
          rw [integral_const_mul]

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.flowLamDeriv_lipschitz_lam
