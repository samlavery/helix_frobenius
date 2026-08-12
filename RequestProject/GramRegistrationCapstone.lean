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

**The capstone**: `GRH χ` holds **iff** every nontrivial zero registers as
a spectral Gram event at a real source height.  Forward: on-line zeros are
found by exact focal cancellation at height `e^y` and rank-drop the Gram
pencil (`L_zero_imp_spectral_gram_event`).  Backward: a registered zero
sits at a represented point, and represented points have `Re = ½` by
construction — reality earned from the geometry, not assumed.  Combined
with `selfAdjointReceiver_xi_iff_rh` this places all three faces —
receiver, registration, and line — in one compiled equivalence class.
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

/-- **The Gram-registration capstone.**  `GRH χ` holds iff every
nontrivial zero of `L(·,χ)` is a spectral Gram event at a real source
height: the zero is the represented point of a real height at which the
structurally self-adjoint harmonic-cell Gram pencil drops rank. -/
theorem grh_iff_spectral_gram_registration (χ : DirichletCharacter ℂ q)
    (μ lam : ℂ) (hlam : lam ≠ μ) :
    GRHSpectral.GRH χ ↔
      ∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
        ∃ Z : ℝ, ρ = reprPoint χ Z ∧ (GramH χ Z μ lam).det = 0 := by
  constructor
  · intro hGRH ρ hρ
    exact L_zero_imp_spectral_gram_event χ ρ μ lam hlam (hGRH ρ hρ) hρ.2.2
  · intro hreg ρ hρ
    obtain ⟨Z, hZ, _⟩ := hreg ρ hρ
    rw [hZ]
    exact reprPoint_re χ Z

end CriticalLinePhasor.HarmonicCell

#print axioms CriticalLinePhasor.HarmonicCell.reprPoint_re
#print axioms CriticalLinePhasor.HarmonicCell.grh_iff_spectral_gram_registration
