import RequestProject.XiKernelIntegrable

/-!
# T1a, step 3 (ii)–(iii): the two integrations by parts (ledger 672)

For `Re s > 1`, `e^{sy}Ψ^{(k)}(y)` is integrable on `ℝ` and tends to `0` at `±∞` (k = 0, 1, 2), so
`∫ e^{sy}Ψ′ = −s ∫ e^{sy}Ψ` and `∫ e^{sy}Ψ″ = −s ∫ e^{sy}Ψ′`, hence with `Λ(s) = 2∫e^{sy}Ψ` (step 2):
  **`xi_integral_form`: `½ s(s−1) Λ(s) = ∫ e^{sy} (Ψ″(y) + Ψ′(y)) dy`.**
-/

open Complex Set Filter Topology MeasureTheory

namespace CriticalLinePhasor.XiKernel

/-- Two-sided integrability and limits from a reflected bound on the left and a super-exponential bound on
the right. -/
theorem integrable_and_tendsto {s : ℂ} (hs : 1 < s.re) {f : ℝ → ℂ} (hf : Continuous f)
    {M : ℝ} (hneg : ∀ y : ℝ, y ≤ 0 → ‖f y‖ ≤ M * Real.exp (-y))
    {b C : ℝ} (hb : 0 ≤ b) (hpos : ∀ y : ℝ, b ≤ y → ‖f y‖ ≤ C * Real.exp (-(5 / 2) * Real.exp (2 * (y - b)))) :
    Integrable (fun y => Ew s y * f y) ∧ Tendsto (fun y => Ew s y * f y) atBot (𝓝 0)
      ∧ Tendsto (fun y => Ew s y * f y) atTop (𝓝 0) := by
  have hcont : Continuous (fun y => Ew s y * f y) := (continuous_Ew s).mul hf
  have hnorm : ∀ y, ‖Ew s y * f y‖ = Real.exp (s.re * y) * ‖f y‖ := fun y => by
    rw [norm_mul, norm_Ew]
  have ha : 0 < s.re - 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- integrable: Iic 0 ∪ Ioi 0, and Ioi 0 = Ioc 0 b ∪ Ioi b
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    refine IntegrableOn.union ?_ ?_
    · have hg : IntegrableOn (fun y : ℝ => M * Real.exp ((s.re - 1) * y)) (Iic 0) :=
        (integrableOn_exp_mul_Iic ha 0).const_mul M
      refine hg.mono' hcont.aestronglyMeasurable.restrict ?_
      filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
      rw [hnorm]
      calc Real.exp (s.re * y) * ‖f y‖ ≤ Real.exp (s.re * y) * (M * Real.exp (-y)) := by
            gcongr; exact hneg y hy
        _ = M * Real.exp ((s.re - 1) * y) := by
            rw [show Real.exp (s.re * y) * (M * Real.exp (-y))
                = M * (Real.exp (s.re * y) * Real.exp (-y)) by ring, ← Real.exp_add]
            congr 2; ring
    · rw [← Ioc_union_Ioi_eq_Ioi hb]
      refine IntegrableOn.union ?_ ?_
      · exact (hcont.continuousOn.integrableOn_Icc (a := 0) (b := b)).mono_set Ioc_subset_Icc_self
      · have hg : IntegrableOn
            (fun y : ℝ => C * (Real.exp (s.re * y) * Real.exp (-(5 / 2) * Real.exp (2 * (y - b))))) (Ioi b) :=
          ((integrableOn_decay s.re b).mono_set Ioi_subset_Ici_self).const_mul C
        refine hg.mono' hcont.aestronglyMeasurable.restrict ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        rw [hnorm]
        calc Real.exp (s.re * y) * ‖f y‖
            ≤ Real.exp (s.re * y) * (C * Real.exp (-(5 / 2) * Real.exp (2 * (y - b)))) := by
              gcongr; exact hpos y (le_of_lt hy)
          _ = C * (Real.exp (s.re * y) * Real.exp (-(5 / 2) * Real.exp (2 * (y - b)))) := by ring
  · -- atBot
    have hlim : Tendsto (fun y : ℝ => M * Real.exp ((s.re - 1) * y)) atBot (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot ha))
      simpa using this.const_mul M
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_le_atBot (0 : ℝ)] with y hy
    rw [hnorm]
    calc Real.exp (s.re * y) * ‖f y‖ ≤ Real.exp (s.re * y) * (M * Real.exp (-y)) := by
          gcongr; exact hneg y hy
      _ = M * Real.exp ((s.re - 1) * y) := by
          rw [show Real.exp (s.re * y) * (M * Real.exp (-y))
              = M * (Real.exp (s.re * y) * Real.exp (-y)) by ring, ← Real.exp_add]
          congr 2; ring
  · -- atTop
    have hlim : Tendsto (fun y : ℝ => C * (Real.exp (s.re * y) * Real.exp (-(5 / 2) * Real.exp (2 * (y - b)))))
        atTop (𝓝 0) := by simpa using (tendsto_decay s.re b).const_mul C
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop b] with y hy
    rw [hnorm]
    calc Real.exp (s.re * y) * ‖f y‖
        ≤ Real.exp (s.re * y) * (C * Real.exp (-(5 / 2) * Real.exp (2 * (y - b)))) := by
          gcongr; exact hpos y hy
      _ = C * (Real.exp (s.re * y) * Real.exp (-(5 / 2) * Real.exp (2 * (y - b)))) := by ring

theorem Psi0_data {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun y => Ew s y * PsiC y) ∧ Tendsto (fun y => Ew s y * PsiC y) atBot (𝓝 0)
      ∧ Tendsto (fun y => Ew s y * PsiC y) atTop (𝓝 0) :=
  integrable_and_tendsto hs continuous_Psi0 (M := 3) (fun y hy => bound_Psi0_nonpos hy) (b := 0) le_rfl
    (C := 2) (fun y hy => by simpa using Psi0_bound hy)

theorem Psi1_data {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun y => Ew s y * Psi1 y) ∧ Tendsto (fun y => Ew s y * Psi1 y) atBot (𝓝 0)
      ∧ Tendsto (fun y => Ew s y * Psi1 y) atTop (𝓝 0) := by
  obtain ⟨M, -, hM⟩ := bound_Psi1_nonpos
  exact integrable_and_tendsto hs continuous_Psi1 hM Rc_pos.le (C := 2 / Rc) (fun y hy => Psi1_bound hy)

theorem Psi2_data {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun y => Ew s y * Psi2 y) ∧ Tendsto (fun y => Ew s y * Psi2 y) atBot (𝓝 0)
      ∧ Tendsto (fun y => Ew s y * Psi2 y) atTop (𝓝 0) := by
  obtain ⟨M, -, hM⟩ := bound_Psi2_nonpos
  exact integrable_and_tendsto hs continuous_Psi2 hM (by have := Rc_pos; positivity)
    (C := 2 / Rc ^ 2) (fun y hy => Psi2_bound hy)

/-- **First integration by parts:** `∫ e^{sy}Ψ′ = −s ∫ e^{sy}Ψ`. -/
theorem ibp1 {s : ℂ} (hs : 1 < s.re) :
    ∫ y, Ew s y * Psi1 y = -(s * ∫ y, Ew s y * PsiC y) := by
  obtain ⟨hi0, hb0, ht0⟩ := Psi0_data hs
  obtain ⟨hi1, -, -⟩ := Psi1_data hs
  have hu'v : Integrable (fun y => (s * Ew s y) * PsiC y) := by
    have := hi0.const_mul s
    refine this.congr (Eventually.of_forall fun y => ?_)
    ring
  have := integral_mul_deriv_eq_deriv_mul (u := Ew s) (v := fun y : ℝ => PsiC y)
    (u' := fun y => s * Ew s y) (v' := Psi1) (a' := 0) (b' := 0)
    (fun x _ => hasDerivAt_Ew s x) (fun x _ => hasDerivAt_Psi0 x) hi1 hu'v hb0 ht0
  rw [this, sub_self, zero_sub, ← integral_const_mul]
  congr 1
  apply integral_congr_ae (Eventually.of_forall fun y => ?_)
  ring

/-- **Second integration by parts:** `∫ e^{sy}Ψ″ = −s ∫ e^{sy}Ψ′`. -/
theorem ibp2 {s : ℂ} (hs : 1 < s.re) :
    ∫ y, Ew s y * Psi2 y = -(s * ∫ y, Ew s y * Psi1 y) := by
  obtain ⟨hi1, hb1, ht1⟩ := Psi1_data hs
  obtain ⟨hi2, -, -⟩ := Psi2_data hs
  have hu'v : Integrable (fun y => (s * Ew s y) * Psi1 y) := by
    have := hi1.const_mul s
    refine this.congr (Eventually.of_forall fun y => ?_)
    ring
  have := integral_mul_deriv_eq_deriv_mul (u := Ew s) (v := Psi1)
    (u' := fun y => s * Ew s y) (v' := Psi2) (a' := 0) (b' := 0)
    (fun x _ => hasDerivAt_Ew s x) (fun x _ => hasDerivAt_Psi1 x) hi2 hu'v hb1 ht1
  rw [this, sub_self, zero_sub, ← integral_const_mul]
  congr 1
  apply integral_congr_ae (Eventually.of_forall fun y => ?_)
  ring

/-- **Step 3:** for `Re s > 1`, `½ s(s−1) Λ(s) = ∫ e^{sy} (Ψ″(y) + Ψ′(y)) dy`. -/
theorem xi_integral_form {s : ℂ} (hs : 1 < s.re) :
    s * (s - 1) / 2 * completedRiemannZeta s = ∫ y, Ew s y * (Psi2 y + Psi1 y) := by
  have hΛ : completedRiemannZeta s = 2 * ∫ y, Ew s y * PsiC y := by
    rw [completedRiemannZeta_eq_integral_Psi hs]
    congr 1
    apply integral_congr_ae (Eventually.of_forall fun y => ?_)
    rw [PsiC_ofReal]; rfl
  obtain ⟨hi1, -, -⟩ := Psi1_data hs
  obtain ⟨hi2, -, -⟩ := Psi2_data hs
  have hsplit : ∫ y, Ew s y * (Psi2 y + Psi1 y) = (∫ y, Ew s y * Psi2 y) + ∫ y, Ew s y * Psi1 y := by
    rw [← integral_add hi2 hi1]
    apply integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  rw [hsplit, ibp2 hs, ibp1 hs, hΛ]
  ring

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.xi_integral_form
