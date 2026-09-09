import RequestProject.XiKernelBounds

/-!
# T1a, step 3 (i): integrability and limits of `e^{sy} Ψ^{(k)}(y)` on `ℝ` for `Re s > 1` (ledger 671)

Positive side: the super-exponential bounds of `XiKernelBounds.lean` dominate `e^{Re s · y}‖Ψ^{(k)}(y)‖` by
`M e^{−y}` beyond a threshold, and by a constant on the compact initial segment.  Negative side: the reflections
of `XiKernelEven.lean` give `‖Ψ^{(k)}(y)‖ ≤ M e^{−y}` for `y ≤ 0`, so `e^{Re s · y}‖Ψ^{(k)}(y)‖ ≤ M e^{(Re s − 1) y}`,
integrable on `Iic 0` and tending to `0` at `−∞` when `Re s > 1`.
-/

open Complex Set Filter Topology MeasureTheory

namespace CriticalLinePhasor.XiKernel

/-- The complex exponential weight `E_s(y) = e^{sy}` and its derivative. -/
noncomputable def Ew (s : ℂ) (y : ℝ) : ℂ := Complex.exp (s * y)

theorem hasDerivAt_Ew (s : ℂ) (y : ℝ) : HasDerivAt (Ew s) (s * Ew s y) y := by
  have hc : HasDerivAt (fun w : ℂ => Complex.exp (s * w)) (Complex.exp (s * y) * s) (y : ℂ) :=
    ((hasDerivAt_id (y : ℂ)).const_mul s).cexp.congr_deriv (by simp)
  exact hc.comp_ofReal.congr_deriv (by unfold Ew; ring)

theorem norm_Ew (s : ℂ) (y : ℝ) : ‖Ew s y‖ = Real.exp (s.re * y) := by
  unfold Ew; rw [Complex.norm_exp]; simp

theorem continuous_Ew (s : ℂ) : Continuous (Ew s) :=
  continuous_iff_continuousAt.mpr fun y => (hasDerivAt_Ew s y).continuousAt

/-- Continuity of `Ψ`, `Ψ′`, `Ψ″` on the axis. -/
theorem continuous_Psi0 : Continuous (fun y : ℝ => PsiC y) :=
  continuous_iff_continuousAt.mpr fun y => (hasDerivAt_Psi0 y).continuousAt
theorem continuous_Psi1 : Continuous Psi1 :=
  continuous_iff_continuousAt.mpr fun y => (hasDerivAt_Psi1 y).continuousAt

theorem differentiableOn_deriv_deriv_PsiC : DifferentiableOn ℂ (deriv (deriv PsiC)) strip := by
  have := differentiableOn_iteratedDeriv_PsiC 2
  simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this

theorem hasDerivAt_Psi2 (y : ℝ) : HasDerivAt Psi2 (deriv (deriv (deriv PsiC)) y) y :=
  ((differentiableOn_deriv_deriv_PsiC.differentiableAt
    (strip_isOpen.mem_nhds (ofReal_mem_strip y))).hasDerivAt).comp_ofReal

theorem continuous_Psi2 : Continuous Psi2 :=
  continuous_iff_continuousAt.mpr fun y => (hasDerivAt_Psi2 y).continuousAt

/-! ### A real decay lemma: `e^{a y} · exp(−(5/2) e^{2(y−b)})` is integrable on `Ici b` and tends to `0`. -/

/-- For `y ≥ y₁ := max b (b + (a + 1)/5)`, `a y − (5/2) e^{2(y − b)} ≤ −y + (a+1) b`. -/
theorem decay_dominated (a b : ℝ) {y : ℝ} (hy : b + (a + 1) / 5 ≤ y) (hyb : b ≤ y) :
    a * y - 5 / 2 * Real.exp (2 * (y - b)) ≤ -y + (a + 1) * b := by
  have h := Real.quadratic_le_exp_of_nonneg (x := 2 * (y - b)) (by linarith)
  nlinarith [sq_nonneg (y - b)]

theorem integrableOn_decay (a b : ℝ) :
    IntegrableOn (fun y : ℝ => Real.exp (a * y) * Real.exp (-(5 / 2) * Real.exp (2 * (y - b)))) (Ici b) := by
  set y₁ := max b (b + (a + 1) / 5) with hy₁
  have hcont : Continuous (fun y : ℝ => Real.exp (a * y) * Real.exp (-(5 / 2) * Real.exp (2 * (y - b)))) := by
    fun_prop
  have h1 : IntegrableOn (fun y : ℝ => Real.exp (a * y) * Real.exp (-(5 / 2) * Real.exp (2 * (y - b))))
      (Icc b y₁) := hcont.continuousOn.integrableOn_Icc
  have h2 : IntegrableOn (fun y : ℝ => Real.exp (a * y) * Real.exp (-(5 / 2) * Real.exp (2 * (y - b))))
      (Ioi y₁) := by
    have hg : IntegrableOn (fun y : ℝ => Real.exp ((a + 1) * b) * Real.exp (-1 * y)) (Ioi y₁) :=
      (exp_neg_integrableOn_Ioi y₁ (by norm_num : (0:ℝ) < 1)).const_mul _
    refine hg.mono' hcont.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hy' : y₁ < y := hy
    have := decay_dominated a b (le_trans (le_max_right _ _) hy'.le) (le_trans (le_max_left _ _) hy'.le)
    linarith
  have hunion : Ici b = Icc b y₁ ∪ Ioi y₁ := by
    ext y; simp only [mem_Ici, mem_union, mem_Icc, mem_Ioi]
    constructor
    · intro h; by_cases hy : y ≤ y₁
      · exact Or.inl ⟨h, hy⟩
      · exact Or.inr (lt_of_not_ge hy)
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact le_trans (le_max_left _ _) h.le
  rw [hunion]
  exact h1.union h2

theorem tendsto_decay (a b : ℝ) :
    Tendsto (fun y : ℝ => Real.exp (a * y) * Real.exp (-(5 / 2) * Real.exp (2 * (y - b)))) atTop (𝓝 0) := by
  have hbound : ∀ᶠ y in atTop, Real.exp (a * y) * Real.exp (-(5 / 2) * Real.exp (2 * (y - b)))
      ≤ Real.exp ((a + 1) * b) * Real.exp (-y) := by
    filter_upwards [eventually_ge_atTop (max b (b + (a + 1) / 5))] with y hy
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := decay_dominated a b (le_trans (le_max_right _ _) hy) (le_trans (le_max_left _ _) hy)
    linarith
  have hlim : Tendsto (fun y : ℝ => Real.exp ((a + 1) * b) * Real.exp (-y)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (Real.exp ((a + 1) * b))
  exact squeeze_zero' (Eventually.of_forall fun y => by positivity) hbound hlim

/-! ### Uniform bounds on `[0, ∞)` and reflected bounds on `(−∞, 0]` -/

/-- A continuous function bounded beyond `b ≥ 0` is bounded on `[0, ∞)`. -/
theorem exists_bound_Ici {f : ℝ → ℂ} (hf : Continuous f) {b C : ℝ} (_hb : 0 ≤ b)
    (hC : ∀ t, b ≤ t → ‖f t‖ ≤ C) : ∃ M, 0 ≤ M ∧ ∀ t, 0 ≤ t → ‖f t‖ ≤ M := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0:ℝ)) (b := b)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max M₀ (max C 0), le_max_of_le_right (le_max_right _ _), fun t ht => ?_⟩
  by_cases hbt : t ≤ b
  · exact (hM₀ t ⟨ht, hbt⟩).trans (le_max_left _ _)
  · exact (hC t (le_of_not_ge hbt)).trans (le_max_of_le_right (le_max_left _ _))

theorem bound_Psi0_nonneg : ∀ t : ℝ, 0 ≤ t → ‖PsiC t‖ ≤ 2 := fun t ht =>
  (Psi0_bound ht).trans (by
    have := Real.exp_le_one_iff.mpr (by nlinarith [Real.exp_pos (2 * t)] : -(5/2) * Real.exp (2 * t) ≤ 0)
    linarith)

theorem exists_bound_Psi1 : ∃ M, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → ‖Psi1 t‖ ≤ M :=
  exists_bound_Ici continuous_Psi1 Rc_pos.le (fun t ht => (Psi1_bound ht).trans (by
    have hR := Rc_pos
    have := Real.exp_le_one_iff.mpr
      (by nlinarith [Real.exp_pos (2 * (t - Rc))] : -(5/2) * Real.exp (2 * (t - Rc)) ≤ 0)
    calc 2 / Rc * Real.exp (-(5 / 2) * Real.exp (2 * (t - Rc))) ≤ 2 / Rc * 1 := by gcongr
      _ = 2 / Rc := mul_one _))

theorem exists_bound_Psi2 : ∃ M, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → ‖Psi2 t‖ ≤ M :=
  exists_bound_Ici continuous_Psi2 (by have := Rc_pos; positivity : (0:ℝ) ≤ 2 * Rc)
    (fun t ht => (Psi2_bound ht).trans (by
      have hR := Rc_pos
      have := Real.exp_le_one_iff.mpr
        (by nlinarith [Real.exp_pos (2 * (t - 2 * Rc))] : -(5/2) * Real.exp (2 * (t - 2 * Rc)) ≤ 0)
      calc 2 / Rc ^ 2 * Real.exp (-(5 / 2) * Real.exp (2 * (t - 2 * Rc))) ≤ 2 / Rc ^ 2 * 1 := by gcongr
        _ = 2 / Rc ^ 2 := mul_one _))

/-- Reflected bound for `Ψ` on `y ≤ 0`: `‖Ψ(y)‖ ≤ 3 e^{−y}`. -/
theorem bound_Psi0_nonpos {y : ℝ} (hy : y ≤ 0) : ‖PsiC y‖ ≤ 3 * Real.exp (-y) := by
  rw [PsiC_reflect y]
  have h0 := bound_Psi0_nonneg (-y) (by linarith)
  have hexp : ‖Complex.exp (-(y : ℂ))‖ = Real.exp (-y) := by
    rw [Complex.norm_exp]; simp
  have h1 : (1 : ℝ) ≤ Real.exp (-y) := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  calc ‖Complex.exp (-(y : ℂ)) * PsiC (-(y : ℂ)) + (Complex.exp (-(y : ℂ)) - 1) / 2‖
      ≤ ‖Complex.exp (-(y : ℂ)) * PsiC (-(y : ℂ))‖ + ‖(Complex.exp (-(y : ℂ)) - 1) / 2‖ := norm_add_le _ _
    _ ≤ Real.exp (-y) * 2 + (Real.exp (-y) + 1) / 2 := by
        gcongr
        · rw [norm_mul, hexp]
          have : ‖PsiC (-(y : ℂ))‖ ≤ 2 := by rw [← Complex.ofReal_neg]; exact h0
          gcongr
        · rw [norm_div, Complex.norm_ofNat]
          gcongr
          exact (norm_sub_le _ _).trans (by rw [hexp, norm_one])
    _ ≤ 3 * Real.exp (-y) := by linarith

/-- Reflected bound for `Ψ′` on `y ≤ 0`. -/
theorem bound_Psi1_nonpos : ∃ M, 0 ≤ M ∧ ∀ y : ℝ, y ≤ 0 → ‖Psi1 y‖ ≤ M * Real.exp (-y) := by
  obtain ⟨M1, hM1, hb1⟩ := exists_bound_Psi1
  refine ⟨2 + M1 + 1 / 2, by positivity, fun y hy => ?_⟩
  rw [Psi1_reflect y]
  have hexp : ‖Complex.exp (-(y : ℂ))‖ = Real.exp (-y) := by rw [Complex.norm_exp]; simp
  have h0 : ‖PsiC (-(y : ℂ))‖ ≤ 2 := by rw [← Complex.ofReal_neg]; exact bound_Psi0_nonneg (-y) (by linarith)
  have h1 : ‖Psi1 (-y)‖ ≤ M1 := hb1 (-y) (by linarith)
  have he := Real.exp_pos (-y)
  calc ‖-Complex.exp (-(y : ℂ)) * PsiC (-(y : ℂ)) - Complex.exp (-(y : ℂ)) * Psi1 (-y)
        - Complex.exp (-(y : ℂ)) / 2‖
      ≤ ‖-Complex.exp (-(y : ℂ)) * PsiC (-(y : ℂ))‖ + ‖Complex.exp (-(y : ℂ)) * Psi1 (-y)‖
        + ‖Complex.exp (-(y : ℂ)) / 2‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
    _ = Real.exp (-y) * ‖PsiC (-(y : ℂ))‖ + Real.exp (-y) * ‖Psi1 (-y)‖ + Real.exp (-y) / 2 := by
          rw [norm_mul, norm_neg, hexp, norm_mul, hexp, norm_div, hexp, Complex.norm_ofNat]
    _ ≤ Real.exp (-y) * 2 + Real.exp (-y) * M1 + Real.exp (-y) / 2 := by gcongr
    _ = (2 + M1 + 1 / 2) * Real.exp (-y) := by ring

/-- Reflected bound for `Ψ″` on `y ≤ 0`. -/
theorem bound_Psi2_nonpos : ∃ M, 0 ≤ M ∧ ∀ y : ℝ, y ≤ 0 → ‖Psi2 y‖ ≤ M * Real.exp (-y) := by
  obtain ⟨M1, hM1, hb1⟩ := exists_bound_Psi1
  obtain ⟨M2, hM2, hb2⟩ := exists_bound_Psi2
  refine ⟨2 + 2 * M1 + M2 + 1 / 2, by positivity, fun y hy => ?_⟩
  rw [Psi2_reflect y]
  have hexp : ‖Complex.exp (-(y : ℂ))‖ = Real.exp (-y) := by rw [Complex.norm_exp]; simp
  have h0 : ‖PsiC (-(y : ℂ))‖ ≤ 2 := by rw [← Complex.ofReal_neg]; exact bound_Psi0_nonneg (-y) (by linarith)
  have h1 : ‖Psi1 (-y)‖ ≤ M1 := hb1 (-y) (by linarith)
  have h2 : ‖Psi2 (-y)‖ ≤ M2 := hb2 (-y) (by linarith)
  have he := Real.exp_pos (-y)
  calc ‖Complex.exp (-(y : ℂ)) * PsiC (-(y : ℂ)) + 2 * Complex.exp (-(y : ℂ)) * Psi1 (-y)
        + Complex.exp (-(y : ℂ)) * Psi2 (-y) + Complex.exp (-(y : ℂ)) / 2‖
      ≤ ‖Complex.exp (-(y : ℂ)) * PsiC (-(y : ℂ))‖ + ‖2 * Complex.exp (-(y : ℂ)) * Psi1 (-y)‖
        + ‖Complex.exp (-(y : ℂ)) * Psi2 (-y)‖ + ‖Complex.exp (-(y : ℂ)) / 2‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
    _ = Real.exp (-y) * ‖PsiC (-(y : ℂ))‖ + 2 * Real.exp (-y) * ‖Psi1 (-y)‖
        + Real.exp (-y) * ‖Psi2 (-y)‖ + Real.exp (-y) / 2 := by
          rw [norm_mul, hexp, norm_mul, norm_mul, hexp, Complex.norm_ofNat, norm_mul, hexp, norm_div,
            hexp, Complex.norm_ofNat]
    _ ≤ Real.exp (-y) * 2 + 2 * Real.exp (-y) * M1 + Real.exp (-y) * M2 + Real.exp (-y) / 2 := by gcongr
    _ = (2 + 2 * M1 + M2 + 1 / 2) * Real.exp (-y) := by ring

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.integrableOn_decay
#print axioms CriticalLinePhasor.XiKernel.bound_Psi2_nonpos
