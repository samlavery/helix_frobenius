import RequestProject.SourceIsCancellation
import RequestProject.DoubleCoshProgram

/-!
# The Riemann Hypothesis in the source vocabulary (ledger 694)

With a source defined as the exact cancellation of two nonzero banks (`HasSource`, ledger 693):

* `SourcesOfZerosOnAxis` : every zero of ζ in the strip that has a source lies on the axis.
* `riemannHypothesis_of_sources` : every zero has a source, and sources of zeros lie on the axis ⟹ RH.

The statement is about the zeros of ζ.  (The fiber's limit is η = (1 − 2^{1−s})ζ, whose sources also include the
alternation points on Re s = 1, ledger 691; those are not zeros of ζ and are outside RH.)
-/

open Complex Filter Topology
open CriticalLinePhasor.Source DoubleCoshProgram

namespace CriticalLinePhasor.Source

/-- **Sources of zeros lie on the axis.** -/
def SourcesOfZerosOnAxis : Prop := ∀ ρ ∈ ZD.NontrivialZeros, HasSource ρ → ρ.re = 1 / 2

/-- **RH from sources:** every zero has a source, and every source of a zero is on the axis. -/
theorem riemannHypothesis_of_sources (h₁ : EveryZeroHasSource) (h₂ : SourcesOfZerosOnAxis) :
    RiemannHypothesis :=
  RiemannHypothesis_of_no_offline (fun ρ hρ => h₂ ρ hρ (h₁ ρ hρ))

end CriticalLinePhasor.Source

#print axioms CriticalLinePhasor.Source.riemannHypothesis_of_sources
