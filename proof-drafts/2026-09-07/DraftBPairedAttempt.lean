import RequestProject.DraftBPrimeStages

open Complex Finset Filter Topology
open CriticalLinePhasor.SeatingLedger CriticalLinePhasor.ContourArgument

/- Retain Draft B's unconditional signature. Discharge its finite-part case
by convergence and put only the positive-degree arithmetic sum in the last goal. -/
example : RiemannHypothesis := by
  apply riemannHypothesis_of_explicit_stage_bound
  suffices h : ∃ C : ℝ, ∃ p : ℕ, ∀ k, ∀ᶠ N in atTop,
      ‖explicitCoeffStage N (k + 1)‖ ≤ C * (1 + ((k + 1 : ℕ) : ℝ) ^ p) by
    obtain ⟨C, p, h⟩ := h
    let D := max C 0 + ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) 0‖ + 1
    have hD : 0 ≤ D := by
      dsimp only [D]
      linarith [le_max_right C 0,
        norm_nonneg (toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) 0)]
    have hCD : C ≤ D := by
      dsimp only [D]
      linarith [le_max_left C 0,
        norm_nonneg (toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) 0)]
    refine ⟨D, p, ?_⟩
    intro k
    cases k with
    | zero =>
      have hev := (explicitCoeffStage_tendsto 0).norm.eventually_lt_const
        (lt_add_one ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) 0‖)
      filter_upwards [hev] with N hN
      have hle : ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) 0‖ + 1 ≤ D := by
        dsimp only [D]
        linarith [le_max_right C 0]
      calc ‖explicitCoeffStage N 0‖
          ≤ ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) 0‖ + 1 := hN.le
        _ ≤ D := hle
        _ ≤ D * (1 + ((0 : ℕ) : ℝ) ^ p) := by
          have hbase : (1 : ℝ) ≤ 1 + ((0 : ℕ) : ℝ) ^ p :=
            le_add_of_nonneg_right (pow_nonneg (Nat.cast_nonneg 0) p)
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hbase hD
    | succ k =>
      filter_upwards [h k] with N hN
      exact hN.trans (mul_le_mul_of_nonneg_right hCD (by positivity))
  simp only [explicitCoeffStage_eq_paired, pairedPrimeStageCoeff_succ_closed]
  trace_state
  exact?
