import RequestProject.SeatingMassWrap
import RequestProject.XiLogDerivConstantFree

/-!
# Two-point summability at the mirror pair

`summable_two_point_mirror`: at a mirror pair `(s, 1−s)` off the zero set the
two-point Hadamard family `m_ρ·[(s−ρ)⁻¹ − ((1−s)−ρ)⁻¹]` is summable — the
compiled Hadamard-term summability differenced, the `1/ρ` normalizers
cancelling.  The mass door itself is the compiled `rh_of_channel_mass`.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- **Two-point summability** at the mirror pair `(s, 1−s)`: the compiled
Hadamard-term summability differenced, the `1/ρ` normalizers cancelling. -/
theorem summable_two_point_mirror {s : ℂ}
    (hs : s ∉ ZD.NontrivialZeros) (hs' : (1 - s) ∉ ZD.NontrivialZeros) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      (ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹ - ((1 - s) - ρ.val)⁻¹)) := by
  apply ((HilbertPolya.summable_hadamard_term hs).sub
    (HilbertPolya.summable_hadamard_term hs')).congr
  intro ρ
  ring

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.summable_two_point_mirror
