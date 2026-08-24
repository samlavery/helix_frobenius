import RequestProject.DVPWeightedBound

/-!
# The clock-measure ledger is `O(log²)` — the register's own vocabulary

`|∫₁₀ᵀ S_all·(clockRate/π)| ≤ C·(1+log(1+T))²`: 421's main-term bound plus
the Stirling error `|clockRate/π − w₀| ≤ (10/π)/t²` integrated against the
a.e. census–Backlund bound (tail) and a fixed head constant.
UNCONDITIONAL.
-/

open Complex
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.ResidueJump

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The clock-measure ledger bound**: the clock-weighted running integral
of the full ledger is `O(log²)`, unconditionally. -/
theorem sall_clock_weighted_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, Real.exp 6 + 1 ≤ T →
      |∫ t in (10:ℝ)..T, SAll t * (clockRate t / Real.pi)|
        ≤ C * (1 + Real.log (1 + T))^2 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := sall_weighted_log_sq_bound
  have hπ := Real.pi_pos
  set M₀ : ℝ := Real.exp 6 + 1 with hM₀def
  have he6 : (403:ℝ) ≤ Real.exp 6 := by
    have h3 : (20.08:ℝ) ≤ Real.exp 3 := by
      have h33 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]
        norm_num
      nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
    have h66 : Real.exp 6 = Real.exp 3 * Real.exp 3 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [h3, Real.exp_pos 3]
  have hM₀10 : (10:ℝ) ≤ M₀ := by rw [hM₀def]; linarith
  set err : ℝ → ℝ := fun t => clockRate t / Real.pi
    - (1/(2*Real.pi)) * Real.log (t/(2*Real.pi)) with herrdef
  have herr_pt : ∀ t : ℝ, 10 ≤ t → |err t| ≤ (10/Real.pi)/t^2 := by
    intro t ht
    have ht0 : (0:ℝ) < t := by linarith
    have habs : |t| = t := abs_of_pos ht0
    have hmu := mu_stirling_explicit (τ := t) (by rw [habs]; linarith)
    rw [habs] at hmu
    have hcr := CriticalLinePhasor.CarrierScale.clockRate_eq_pi_mul_mu t
    have hkey : err t = Zeta23.mu t
        - 1/(2*Real.pi) * Real.log (t/(2*Real.pi)) := by
      rw [herrdef]
      simp only []
      rw [hcr]
      field_simp
    rw [hkey]
    exact hmu
  have herr_contOn : ∀ a b : ℝ, 10 ≤ a →
      ContinuousOn err (Set.Icc a b) := by
    intro a b ha
    intro t htm
    have ht0 : (0:ℝ) < t := by linarith [htm.1]
    apply ContinuousWithinAt.sub
    · exact ((continuous_clockRate.continuousAt).div_const _).continuousWithinAt
    · have h1 : ContinuousAt (fun t : ℝ => t/(2*Real.pi)) t :=
        continuousAt_id.div_const _
      have h2 : ContinuousAt Real.log (t/(2*Real.pi)) :=
        Real.continuousAt_log (by positivity)
      have h3 : ContinuousAt (Real.log ∘ fun t : ℝ => t/(2*Real.pi)) t :=
        ContinuousAt.comp h2 h1
      exact (continuousAt_const.mul h3).continuousWithinAt
  have hint_err : ∀ a b : ℝ, 10 ≤ a → a ≤ b → IntervalIntegrable
      (fun t => SAll t * err t) MeasureTheory.volume a b := by
    intro a b ha hab
    apply IntervalIntegrable.mul_continuousOn (sall_intervalIntegrable a b)
    rw [Set.uIcc_of_le hab]
    exact herr_contOn a b ha
  set K₀ : ℝ := |∫ t in (10:ℝ)..M₀, SAll t * err t| with hK₀def
  have hK₀0 : (0:ℝ) ≤ K₀ := abs_nonneg _
  refine ⟨2*C₁ + K₀ + 3, by linarith, ?_⟩
  intro T hT
  have hTM₀ : M₀ ≤ T := by rw [hM₀def] at *; linarith
  have hT10 : (10:ℝ) ≤ T := by linarith
  have hL0 : (0:ℝ) ≤ Real.log (1+T) := Real.log_nonneg (by linarith)
  set L : ℝ := 1 + Real.log (1 + T) with hLdef
  have hL1 : (1:ℝ) ≤ L := by rw [hLdef]; linarith
  -- split into the 421 main term and the error term
  have hsplit_fun : ∀ t : ℝ, SAll t * (clockRate t / Real.pi)
      = SAll t * ((1/(2*Real.pi)) * Real.log (t/(2*Real.pi)))
        + SAll t * err t := by
    intro t
    rw [herrdef]
    ring
  have hint_main : IntervalIntegrable
      (fun t => SAll t * ((1/(2*Real.pi)) * Real.log (t/(2*Real.pi))))
      MeasureTheory.volume 10 T := by
    apply IntervalIntegrable.mul_continuousOn (sall_intervalIntegrable 10 T)
    rw [Set.uIcc_of_le hT10]
    intro t htm
    have ht0 : (0:ℝ) < t := by linarith [htm.1]
    have h1 : ContinuousAt (fun t : ℝ => t/(2*Real.pi)) t :=
      continuousAt_id.div_const _
    have h2 : ContinuousAt Real.log (t/(2*Real.pi)) :=
      Real.continuousAt_log (by positivity)
    have h3 : ContinuousAt (Real.log ∘ fun t : ℝ => t/(2*Real.pi)) t :=
      ContinuousAt.comp h2 h1
    exact (continuousAt_const.mul h3).continuousWithinAt
  have hsplit : ∫ t in (10:ℝ)..T, SAll t * (clockRate t / Real.pi)
      = (∫ t in (10:ℝ)..T,
          SAll t * ((1/(2*Real.pi)) * Real.log (t/(2*Real.pi))))
        + ∫ t in (10:ℝ)..T, SAll t * err t := by
    rw [← intervalIntegral.integral_add hint_main
      (hint_err 10 T (le_refl 10) hT10)]
    apply intervalIntegral.integral_congr
    intro t _
    exact hsplit_fun t
  -- error term: head constant + a.e.-Backlund tail
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (hint_err 10 M₀ (le_refl 10) hM₀10) (hint_err M₀ T hM₀10 hTM₀)
  have htail : |∫ t in M₀..T, SAll t * err t|
      ≤ (20 * Real.log T + 3) * ((10/Real.pi)/M₀) := by
    have hae := sall_ae_bound (T₁ := M₀) (T₂ := T)
      (by rw [hM₀def]; linarith) hTM₀
    have hae2 : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Icc M₀ T →
        |SAll t * err t| ≤ (20 * Real.log T + 3) * ((10/Real.pi)/t^2) := by
      have hM₀null : (MeasureTheory.volume : MeasureTheory.Measure ℝ)
          ({M₀} : Set ℝ) = 0 := MeasureTheory.measure_singleton M₀
      rw [MeasureTheory.ae_iff] at hae ⊢
      refine MeasureTheory.measure_mono_null ?_
        (MeasureTheory.measure_union_null hae hM₀null)
      intro t htmem
      simp only [Set.mem_ofPred_eq, Classical.not_imp] at htmem
      obtain ⟨htIcc, hbnd⟩ := htmem
      rcases eq_or_lt_of_le htIcc.1 with heq | hlt
      · exact Set.mem_union_right _ (by simp [← heq])
      · refine Set.mem_union_left _ ?_
        simp only [Set.mem_ofPred_eq, Classical.not_imp]
        refine ⟨?_, ?_⟩
        · rw [Set.uIoc_of_le hTM₀]
          exact ⟨hlt, htIcc.2⟩
        · intro hSb
          apply hbnd
          have ht10 : (10:ℝ) ≤ t := by linarith [htIcc.1]
          have herrb := herr_pt t ht10
          rw [abs_mul]
          have h1 : |SAll t| * |err t|
              ≤ (20 * Real.log T + 3) * ((10/Real.pi)/t^2) := by
            apply mul_le_mul hSb herrb (abs_nonneg _)
            have hlogT0 : (0:ℝ) ≤ Real.log T :=
              Real.log_nonneg (by linarith)
            linarith
          exact h1
    have h1 := intervalIntegral.abs_integral_le_integral_abs
      (f := fun t : ℝ => SAll t * err t)
      (μ := MeasureTheory.volume) hTM₀
    have hint_maj : IntervalIntegrable
        (fun t : ℝ => (20 * Real.log T + 3) * ((10/Real.pi)/t^2))
        MeasureTheory.volume M₀ T := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hTM₀]
      intro t htm
      have ht0 : (0:ℝ) < t := by linarith [htm.1]
      exact (continuousAt_const.mul (continuousAt_const.div
        ((continuous_pow 2).continuousAt)
        (by positivity))).continuousWithinAt
    have h2 : (∫ t in M₀..T, |SAll t * err t|)
        ≤ ∫ t in M₀..T, (20 * Real.log T + 3) * ((10/Real.pi)/t^2) := by
      apply intervalIntegral.integral_mono_ae_restrict hTM₀
        ((hint_err M₀ T hM₀10 hTM₀).abs) hint_maj
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr hae2
    -- evaluate the majorant integral
    have hsqftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => -(10/s)) (f' := fun t => 10/t^2)
      (a := M₀) (b := T)
      (fun t htm => inv_sq_hasDerivAt (by
        rw [Set.uIcc_of_le hTM₀] at htm
        linarith [htm.1]))
      (by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hTM₀]
        intro t htm
        have ht0 : (0:ℝ) < t := by linarith [htm.1]
        exact (continuousAt_const.div ((continuous_pow 2).continuousAt)
          (by positivity)).continuousWithinAt)
    have hmaj_eq : (∫ t in M₀..T,
        (20 * Real.log T + 3) * ((10/Real.pi)/t^2))
        = (20 * Real.log T + 3) * (1/Real.pi)
          * ∫ t in M₀..T, 10/t^2 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      field_simp
    have hsq_le : (∫ t in M₀..T, (10:ℝ)/t^2) ≤ 10/M₀ := by
      rw [hsqftc]
      have hTpos : (0:ℝ) < T := by linarith
      have : (0:ℝ) < 10/T := by positivity
      have hM₀pos : (0:ℝ) < M₀ := by linarith
      have heq : -(10/T) - -(10/M₀) = 10/M₀ - 10/T := by ring
      linarith [heq.le, heq.ge]
    have hlogT0 : (0:ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
    have hcoef : (0:ℝ) ≤ (20 * Real.log T + 3) * (1/Real.pi) := by
      positivity
    calc |∫ t in M₀..T, SAll t * err t|
        ≤ ∫ t in M₀..T, |SAll t * err t| := h1
      _ ≤ ∫ t in M₀..T, (20 * Real.log T + 3) * ((10/Real.pi)/t^2) := h2
      _ = (20 * Real.log T + 3) * (1/Real.pi) * ∫ t in M₀..T, 10/t^2 :=
          hmaj_eq
      _ ≤ (20 * Real.log T + 3) * (1/Real.pi) * (10/M₀) := by
          apply mul_le_mul_of_nonneg_left hsq_le hcoef
      _ = (20 * Real.log T + 3) * ((10/Real.pi)/M₀) := by
          field_simp
  -- final assembly
  have hmain := hC₁ T hT10
  have herr_total : |∫ t in (10:ℝ)..T, SAll t * err t|
      ≤ K₀ + (20 * Real.log T + 3) * ((10/Real.pi)/M₀) := by
    have heq : ∫ t in (10:ℝ)..T, SAll t * err t
        = (∫ t in (10:ℝ)..M₀, SAll t * err t)
          + ∫ t in M₀..T, SAll t * err t := hadj.symm
    rw [heq]
    calc |(∫ t in (10:ℝ)..M₀, SAll t * err t)
        + ∫ t in M₀..T, SAll t * err t|
        ≤ |∫ t in (10:ℝ)..M₀, SAll t * err t|
          + |∫ t in M₀..T, SAll t * err t| := abs_add_le _ _
      _ ≤ K₀ + (20 * Real.log T + 3) * ((10/Real.pi)/M₀) := by
          rw [hK₀def]
          linarith [htail]
  -- numeric: the tail coefficient is ≤ 1·L, and everything folds into C·L²
  have hlogTle : Real.log T ≤ L := by
    rw [hLdef]
    have := Real.log_le_log (by linarith : (0:ℝ) < T)
      (by linarith : T ≤ 1 + T)
    linarith
  have hM₀tail : (20 * Real.log T + 3) * ((10/Real.pi)/M₀) ≤ 3 * L := by
    have h1 : (10/Real.pi)/M₀ ≤ 1/100 := by
      have hπ3 := Real.pi_gt_three
      have hM₀400 : (400:ℝ) ≤ M₀ := by rw [hM₀def]; linarith
      have hq : (10:ℝ)/Real.pi ≤ 10/3 := by
        rw [div_le_div_iff₀ hπ (by norm_num : (0:ℝ) < 3)]
        nlinarith
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < M₀) (by norm_num : (0:ℝ) < 100)]
      nlinarith [hq, hM₀400]
    have hlogT0 : (0:ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
    have h2 : (0:ℝ) ≤ 20 * Real.log T + 3 := by linarith
    calc (20 * Real.log T + 3) * ((10/Real.pi)/M₀)
        ≤ (20 * Real.log T + 3) * (1/100) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ ≤ 3 * L := by nlinarith [hlogTle, hL1]
  rw [hsplit]
  calc |(∫ t in (10:ℝ)..T,
      SAll t * ((1/(2*Real.pi)) * Real.log (t/(2*Real.pi))))
      + ∫ t in (10:ℝ)..T, SAll t * err t|
      ≤ |∫ t in (10:ℝ)..T,
          SAll t * ((1/(2*Real.pi)) * Real.log (t/(2*Real.pi)))|
        + |∫ t in (10:ℝ)..T, SAll t * err t| := abs_add_le _ _
    _ ≤ C₁ * L^2 + (K₀ + 3 * L) := by
        rw [← hLdef] at hmain
        linarith [hmain, herr_total, hM₀tail]
    _ ≤ (2*C₁ + K₀ + 3) * L^2 := by
        have hL2 : (1:ℝ) ≤ L^2 := by nlinarith [hL1]
        have hLL : (0:ℝ) ≤ L^2 - L := by nlinarith [hL1]
        have hK₀L : K₀ ≤ K₀ * L^2 := by nlinarith [hK₀0, hL2]
        have hC₁L : (0:ℝ) ≤ C₁ * L^2 := by positivity
        linarith [hK₀L, hLL, hC₁L]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.sall_clock_weighted_bound
end AxiomAudit
