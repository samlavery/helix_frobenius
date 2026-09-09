import RequestProject.ExplicitAnchorDischarge

open Complex Filter Topology
open CriticalLinePhasor.SeatingLedger

/- The second route uses the exact completed coefficient as the cutoff envelope.
It permits a separate starting cutoff for each degree. Only the common
polynomial envelope is left to the final search. -/
example : RiemannHypothesis := by
  apply riemannHypothesis_of_explicit_stage_bound
  let B : ℕ → ℝ := fun k =>
    ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k‖ + 1
  have hB : ∀ k, ∀ᶠ N in atTop, ‖explicitCoeffStage N k‖ ≤ B k := by
    intro k
    exact ((explicitCoeffStage_tendsto k).norm.eventually_lt_const
      (lt_add_one _)).mono (fun N hN => hN.le)
  suffices h : ∃ C : ℝ, ∃ p : ℕ, ∀ k, B k ≤ C * (1 + (k : ℝ) ^ p) by
    obtain ⟨C, p, h⟩ := h
    exact ⟨C, p, fun k => (hB k).mono (fun N hN => hN.trans (h k))⟩
  dsimp only [B]
  exact?
