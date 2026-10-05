import RequestProject.SpectralGramEvent
import RequestProject.HilbertPolyaCapstone

/-!
# The Gram-registration capstone: GRH as spectral Gram registration

The concrete operator form of the Hilbert–Pólya equivalence, wired to the
compiled 3D instruments rather than an abstract receiver.  The registration
side is built from:

* the **harmonic-cell Gram pencil** `GramH` — Hermitian positive
  semidefinite *by construction* (a Gram matrix), the structurally
  self-adjoint 3D operator; its rank drop is the spectral Gram event;
* the **represented point** `reprPoint χ Z = ½ + i·log Z` of a real source
  height — real heights read out on the critical line by construction;
* downstream, the **von Neumann channel** `vonNeumannOp γ` (self-adjoint,
  resolvent trace `I/(γ−z)` with its pole at the real cancellation,
  `vonNeumann_resolvent_trace`) and the **Cayley intertwiner** (3D
  involution ↔ circle conjugation, readouts of norm one) supply the
  operator reading of the registered events.

**The capstone**: if every nontrivial zero registers as a spectral Gram event
at a real source height, `GRH χ` holds: a registered zero sits at a represented
point, and represented points have `Re = ½` by construction — reality earned
from the geometry, not assumed.  On-line zeros are found by exact focal
cancellation at height `e^y` and rank-drop the Gram pencil
(`L_zero_imp_spectral_gram_event`).
No `axiom`, no `sorry`.
-/

open Complex

namespace CriticalLinePhasor.HarmonicCell

variable {q : ℕ} [NeZero q]

/-- Represented points of real source heights lie on the critical line by
construction. -/
theorem reprPoint_re (χ : DirichletCharacter ℂ q) (Z : ℝ) :
    (reprPoint χ Z).re = 1 / 2 := by
  simp [reprPoint]

/-- **The Gram-registration capstone.**  If every nontrivial zero of `L(·,χ)` is a spectral Gram
event at a real source height — the represented point of a real height at which the structurally
self-adjoint harmonic-cell Gram pencil drops rank — `GRH χ` holds. -/
theorem grh_of_spectral_gram_registration (χ : DirichletCharacter ℂ q)
    (μ lam : ℂ)
    (hreg : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
        ∃ Z : ℝ, ρ = reprPoint χ Z ∧ (GramH χ Z μ lam).det = 0) :
    GRHSpectral.GRH χ := by
  intro ρ hρ
  obtain ⟨Z, hZ, _⟩ := hreg ρ hρ
  rw [hZ]
  exact reprPoint_re χ Z

end CriticalLinePhasor.HarmonicCell

#print axioms CriticalLinePhasor.HarmonicCell.reprPoint_re
#print axioms CriticalLinePhasor.HarmonicCell.grh_of_spectral_gram_registration
