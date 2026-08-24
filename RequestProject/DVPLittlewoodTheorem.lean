import RequestProject.DVPSAllWindow
import RequestProject.DVPBacklund

/-!
# Littlewood's theorem, `N_all`-form: `LittlewoodBound` holds

The final assembly.  Fix a good base height `t₀ ∈ (e⁶, e⁶+1)`; for
`T ≤ t₀` the running integral is dominated by the fixed constant
`C₀ = ∫₀^{t₀}|S_all|`; for `T > t₀` pick a good `T' ∈ (T, T+1)`, split
`∫₀^T = ∫₀^{t₀} + ∫_{t₀}^{T'} − ∫_T^{T'}`, bound the window by 410 and the
unit tail by the a.e. census–Backlund bound.  UNCONDITIONAL.
-/

open Metric Complex MeasureTheory Topology Filter Set
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.ResidueJump

noncomputable section

namespace CriticalLinePhasor.DVP

/-- `S_all` is interval-integrable on every interval. -/
theorem sall_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable SAll MeasureTheory.volume a b :=
  (smult_intervalIntegrable a b).add (offline_intervalIntegrable a b)

/-- The a.e. pointwise Backlund bound for `S_all` above `e⁶`. -/
theorem sall_ae_bound {T₁ T₂ : ℝ} (h6 : Real.exp 6 ≤ T₁) (ht : T₁ ≤ T₂) :
    ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc T₁ T₂ →
      |SAll t| ≤ 20 * Real.log T₂ + 3 := by
  have hbadfin : (Complex.im '' stripZeroWindow T₂).Finite :=
    (stripZeroWindow_finite T₂).image _
  have hnull := hbadfin.measure_zero MeasureTheory.volume
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro t hmem
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at hmem
  obtain ⟨htI, hne⟩ := hmem
  rw [Set.uIoc_of_le ht] at htI
  have hpos : (0:ℝ) < T₁ := lt_of_lt_of_le (Real.exp_pos 6) h6
  by_contra htbad
  apply hne
  have hgood : GoodHeight t := by
    refine ⟨by linarith [htI.1], ?_⟩
    intro ρ hρ him
    apply htbad
    refine ⟨ρ, ⟨hρ, ?_, ?_⟩, him⟩
    · rw [him]
      linarith [htI.1]
    · rw [him]
      exact htI.2
  have hcensus := classicalSContour_eq_Smult_add_offLine hgood
  have hback := abs_classicalSContour_le (by linarith [htI.1]) hgood
  have hlogmono : Real.log t ≤ Real.log T₂ :=
    Real.log_le_log (by linarith [htI.1]) htI.2
  have hSAll : SAll t = classicalSContour hgood := by
    rw [SAll, ← hcensus]
  rw [hSAll]
  linarith [hback]

/-- **Littlewood's theorem in `N_all`-form**: the `LittlewoodBound`
predicate holds, unconditionally. -/
theorem littlewoodBound_holds : LittlewoodBound := by
  have he6pos : (0:ℝ) < Real.exp 6 := Real.exp_pos 6
  have he46 : Real.exp 4 ≤ Real.exp 6 := by
    apply Real.exp_le_exp.mpr
    norm_num
  obtain ⟨t₀, ht₀l, ht₀u, hgood₀⟩ := exists_goodHeight_between he6pos
  have ht₀pos : (0:ℝ) < t₀ := by linarith
  have he4t₀ : Real.exp 4 ≤ t₀ := by linarith
  have he6t₀ : Real.exp 6 ≤ t₀ := by linarith
  set C₀ : ℝ := ∫ t in (0:ℝ)..t₀, |SAll t| with hC₀def
  have hC₀0 : (0:ℝ) ≤ C₀ := by
    rw [hC₀def]
    exact intervalIntegral.integral_nonneg (le_of_lt ht₀pos)
      (fun t _ => abs_nonneg _)
  refine ⟨C₀ + 1635, ?_⟩
  intro T hT0
  have hlog1T : (0:ℝ) ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
  rcases le_or_gt T t₀ with hTt₀ | hTt₀
  · -- small T: dominated by the fixed constant
    have h1 : |∫ t in (0:ℝ)..T, SAll t| ≤ ∫ t in (0:ℝ)..T, |SAll t| :=
      intervalIntegral.abs_integral_le_integral_abs hT0
    have h2 : (∫ t in (0:ℝ)..T, |SAll t|) ≤ C₀ := by
      rw [hC₀def]
      have hadj := intervalIntegral.integral_add_adjacent_intervals
        ((sall_intervalIntegrable 0 T).abs)
        ((sall_intervalIntegrable T t₀).abs)
      have h3 : (0:ℝ) ≤ ∫ t in T..t₀, |SAll t| :=
        intervalIntegral.integral_nonneg hTt₀ (fun t _ => abs_nonneg _)
      linarith [hadj]
    calc |∫ t in (0:ℝ)..T, SAll t| ≤ C₀ := le_trans h1 h2
      _ ≤ (C₀ + 1635) * (1 + Real.log (1 + T)) := by nlinarith
  · -- large T: split through a good height in (T, T+1)
    obtain ⟨T', hT'l, hT'u, hgood'⟩ :=
      exists_goodHeight_between (by linarith : (0:ℝ) < T)
    have hTT' : T ≤ T' := le_of_lt hT'l
    have ht₀T' : t₀ ≤ T' := by linarith
    have hwin := window_SAll_integral_bound hgood₀ hgood' he4t₀ ht₀T'
    have hadj1 := intervalIntegral.integral_add_adjacent_intervals
      (sall_intervalIntegrable 0 t₀) (sall_intervalIntegrable t₀ T')
    have hadj2 := intervalIntegral.integral_add_adjacent_intervals
      (sall_intervalIntegrable 0 T) (sall_intervalIntegrable T T')
    have hhead : |∫ t in (0:ℝ)..t₀, SAll t| ≤ C₀ := by
      rw [hC₀def]
      exact intervalIntegral.abs_integral_le_integral_abs (le_of_lt ht₀pos)
    -- unit tail via a.e. Backlund
    have hlogT1 : (0:ℝ) ≤ Real.log (T + 1) := by
      apply Real.log_nonneg
      linarith
    have htail : |∫ t in T..T', SAll t| ≤ 20 * Real.log (T + 1) + 3 := by
      have hae := sall_ae_bound (T₁ := T) (T₂ := T + 1) (by linarith)
        (by linarith)
      have hae2 : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Icc T T' →
          |SAll t| ≤ 20 * Real.log (T + 1) + 3 := by
        have hTnull : (MeasureTheory.volume : Measure ℝ) ({T} : Set ℝ) = 0 :=
          measure_singleton T
        rw [ae_iff] at hae ⊢
        refine measure_mono_null ?_ (measure_union_null hae hTnull)
        intro t htmem
        simp only [Set.mem_ofPred_eq, Classical.not_imp] at htmem
        obtain ⟨htIcc, hbnd⟩ := htmem
        rcases eq_or_lt_of_le htIcc.1 with heq | hlt
        · exact Set.mem_union_right _ (by simp [← heq])
        · refine Set.mem_union_left _ ?_
          simp only [Set.mem_ofPred_eq, Classical.not_imp]
          refine ⟨?_, hbnd⟩
          rw [Set.uIoc_of_le (by linarith : T ≤ T + 1)]
          exact ⟨hlt, by linarith [htIcc.2]⟩
      have h1 : |∫ t in T..T', SAll t| ≤ ∫ t in T..T', |SAll t| :=
        intervalIntegral.abs_integral_le_integral_abs hTT'
      have h2 : (∫ t in T..T', |SAll t|)
          ≤ ∫ t in T..T', (20 * Real.log (T + 1) + 3 : ℝ) := by
        apply intervalIntegral.integral_mono_ae_restrict hTT'
          ((sall_intervalIntegrable T T').abs) intervalIntegrable_const
        rw [show ((fun t : ℝ => |SAll t|)
            ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc T T')]
            fun _ : ℝ => 20 * Real.log (T + 1) + 3)
          = ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Icc T T'),
              |SAll t| ≤ 20 * Real.log (T + 1) + 3 from rfl]
        exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr hae2
      have h3 : (∫ t in T..T', (20 * Real.log (T + 1) + 3 : ℝ))
          = (T' - T) * (20 * Real.log (T + 1) + 3) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      have h4 : (T' - T) * (20 * Real.log (T + 1) + 3)
          ≤ 20 * Real.log (T + 1) + 3 := by
        have hlen : T' - T ≤ 1 := by linarith
        nlinarith
      linarith [h1, h2, h3.le, h3.ge, h4]
    -- assemble
    have hsplit : ∫ t in (0:ℝ)..T, SAll t
        = (∫ t in (0:ℝ)..t₀, SAll t) + (∫ t in t₀..T', SAll t)
          - ∫ t in T..T', SAll t := by
      linarith [hadj1, hadj2]
    rw [hsplit]
    have hlogT' : Real.log T' ≤ Real.log (T + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlogeq : Real.log (T + 1) = Real.log (1 + T) := by
      ring_nf
    have habs : |(∫ t in (0:ℝ)..t₀, SAll t) + (∫ t in t₀..T', SAll t)
        - ∫ t in T..T', SAll t|
        ≤ |∫ t in (0:ℝ)..t₀, SAll t| + |∫ t in t₀..T', SAll t|
          + |∫ t in T..T', SAll t| := by
      have h1 := abs_add_le
        ((∫ t in (0:ℝ)..t₀, SAll t) + (∫ t in t₀..T', SAll t))
        (-(∫ t in T..T', SAll t))
      rw [abs_neg] at h1
      have h2 := abs_add_le (∫ t in (0:ℝ)..t₀, SAll t)
        (∫ t in t₀..T', SAll t)
      have heq : (∫ t in (0:ℝ)..t₀, SAll t) + (∫ t in t₀..T', SAll t)
          - ∫ t in T..T', SAll t
          = ((∫ t in (0:ℝ)..t₀, SAll t) + (∫ t in t₀..T', SAll t))
            + -(∫ t in T..T', SAll t) := by ring
      rw [heq]
      linarith [h1, h2]
    have hfin : |∫ t in (0:ℝ)..t₀, SAll t| + |∫ t in t₀..T', SAll t|
        + |∫ t in T..T', SAll t|
        ≤ C₀ + (12 + 1600 * Real.log T') + (20 * Real.log (T + 1) + 3) := by
      linarith [hhead, hwin, htail]
    calc |(∫ t in (0:ℝ)..t₀, SAll t) + (∫ t in t₀..T', SAll t)
        - ∫ t in T..T', SAll t|
        ≤ C₀ + (12 + 1600 * Real.log T') + (20 * Real.log (T + 1) + 3) :=
          le_trans habs hfin
      _ ≤ C₀ + 15 + 1620 * Real.log (1 + T) := by
          rw [← hlogeq]
          linarith [hlogT', hlogT1]
      _ ≤ (C₀ + 1635) * (1 + Real.log (1 + T)) := by nlinarith

/-- **The o(T) registration input holds unconditionally**: the running
full-strip ledger integral is sublinear. -/
theorem littlewood_o_input_holds :
    (fun T => ∫ t in (0:ℝ)..T,
        (Smult t + (offLineStripZeroCountMult t : ℝ)))
      =o[atTop] fun T : ℝ => T :=
  littlewood_o_input littlewoodBound_holds

/-- **The registration reduced to TWO residuals, unconditionally**: on the
concrete π-cells, `ClockCellMassBounded` and `OffLineMassLog` alone deliver
`classicalSContour = Smult` at every good height — the Littlewood input is
now a theorem, not a hypothesis. -/
theorem gram_registration_two_residuals (hOff : OffLineMassLog) :
    ∃ c : ℕ → ℝ, c 0 = 10 ∧ Monotone c
      ∧ (∀ n, theta (c (n + 1)) - theta (c n) = Real.pi)
      ∧ (ClockCellMassBounded c →
          ∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) :=
  gram_registration_from_littlewood littlewoodBound_holds hOff

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.sall_intervalIntegrable
#print axioms CriticalLinePhasor.DVP.sall_ae_bound
#print axioms CriticalLinePhasor.DVP.littlewoodBound_holds
#print axioms CriticalLinePhasor.DVP.littlewood_o_input_holds
#print axioms CriticalLinePhasor.DVP.gram_registration_two_residuals
end AxiomAudit
