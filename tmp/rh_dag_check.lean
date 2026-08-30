import RequestProject.RiemannHypothesisBridge
import RequestProject.SeatingMassWrap
#print axioms RHBridge.no_offline_zeros_implies_rh
-- the composed endpoint: does the bridge consume the SAME ZD.NontrivialZeros?
theorem riemannHypothesis_of_channel_mass_check :
    ∃ A : ℝ, 0 < A ∧
      ((∀ s : ℂ, 1269/2 < |s.im| →
          A / (Real.log |s.im|)^9 < s.re → s.re < 1/2 →
          0 ≤ CriticalLinePhasor.SeatingLedger.seatMass s) →
        RiemannHypothesis) := by
  obtain ⟨A, hA0, h⟩ := CriticalLinePhasor.SeatingLedger.rh_of_channel_mass
  exact ⟨A, hA0, fun hM => RHBridge.no_offline_zeros_implies_rh (h hM)⟩
#print axioms riemannHypothesis_of_channel_mass_check
