import RequestProject.DVPSeatPrimeJoin

open Complex

noncomputable section

namespace CriticalLinePhasor.DVP

/-- Strategy B: obtain the reflected-pair bound directly from the compiled
prime-zero explicit formula.  The final `exact` records the precise missing
map from the explicit-formula identity to a uniform helix-amplitude bound. -/
example : 
    ∀ ρ : ℂ, ρ ∈ VMEFStandalone.NontrivialZeros →
      ∃ M : ℝ, ∀ θ : ℝ, VMEFStandalone.reflectedPairEnvelope ρ.re θ ≤ M := by
  intro ρ hρ
  have htwo : (2 : ℂ) ∉ VMEFStandalone.NontrivialZeros := by
    intro h
    norm_num [VMEFStandalone.NontrivialZeros] at h
  have hdual := VMEFStandalone.primeZeroDuality (2 : ℂ) (by norm_num) htwo
  exact hdual

end CriticalLinePhasor.DVP
