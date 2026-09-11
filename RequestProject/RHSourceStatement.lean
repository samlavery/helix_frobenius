import RequestProject.SourceIsCancellation
import RequestProject.DoubleCoshProgram

/-!
# The Riemann Hypothesis in the source vocabulary (ledger 694)

With a source defined as the exact cancellation of two nonzero banks (`HasSource`, ledger 693):

* `SourcesOfZerosOnAxis` : every zero of ζ in the strip that has a source lies on the axis.
* `riemannHypothesis_of_sources` : every zero has a source, and sources of zeros lie on the axis ⟹ RH.
* `rh_iff_sourcesOfZerosOnAxis` : given that every zero has a source, RH ⟺ sources of zeros lie on the axis.

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

/-- RH gives the axis for every zero in the strip. -/
theorem re_eq_half_of_rh (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) : ρ.re = 1 / 2 := by
  obtain ⟨h0, h1, hz⟩ := hρ
  refine hRH ρ hz ?_ ?_
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp at hre
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h1'
    rw [h1'] at h1
    simp at h1

/-- **The statement of RH in the source vocabulary.**  Once every zero has a source, the Riemann Hypothesis is
exactly: every source of a zero lies on the axis. -/
theorem rh_iff_sourcesOfZerosOnAxis (h : EveryZeroHasSource) :
    RiemannHypothesis ↔ SourcesOfZerosOnAxis := by
  constructor
  · intro hRH ρ hρ _
    exact re_eq_half_of_rh hRH hρ
  · intro h₂
    exact riemannHypothesis_of_sources h h₂

end CriticalLinePhasor.Source

#print axioms CriticalLinePhasor.Source.riemannHypothesis_of_sources
#print axioms CriticalLinePhasor.Source.rh_iff_sourcesOfZerosOnAxis
