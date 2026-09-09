import RequestProject.ExplicitAnchorDischarge

open Complex Filter Topology
open CriticalLinePhasor.SeatingLedger

/- The first attempted estimate uses the compiled exponential envelope and
transfers it to stages. The last inequality is tested directly, not assumed. -/
example : RiemannHypothesis := by
  apply riemannHypothesis_of_explicit_stage_bound
  obtain ⟨C, hC⟩ := explicit_growth_unconditional
  refine ⟨C + 1, 0, ?_⟩
  intro k
  have hlt : ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k‖ <
      C * growthBase ^ k + 1 := lt_of_le_of_lt (hC k) (lt_add_one _)
  have hev := (explicitCoeffStage_tendsto k).norm.eventually_lt_const hlt
  filter_upwards [hev] with N hN
  calc ‖explicitCoeffStage N k‖ ≤ C * growthBase ^ k + 1 := hN.le
    _ ≤ (C + 1) * (1 + (k : ℝ) ^ 0) := by
      simp only [pow_zero]
      nlinarith [one_lt_growthBase]
