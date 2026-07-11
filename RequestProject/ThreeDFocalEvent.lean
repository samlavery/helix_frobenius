import RequestProject.SpectralSignFlip

/-!
# Native three-dimensional focal events

This file makes the 3-D event chain explicit on the finite phasor bank.  A focal cancellation at
a 3-D height `z` is a vanishing of a finite signed phasor sum.  The associated finite Gram
pencil rank-drops exactly at that cancellation, and the marked carrier point has a nonzero kernel
mode for the von Neumann fibre operator.

No analytic `L`-value, zero window, or chart-indexed operator occurs in these definitions.  The
separate 3-D-to-1-D projection is handled by `FinitePencil.lean`.
-/

open Complex Matrix
open scoped BigOperators ComplexConjugate

namespace CriticalLinePhasor.ThreeDFocal

open CriticalLinePhasor CriticalLinePhasor.HarmonicCell
open CriticalLinePhasor.SelfAdjointGenerator CriticalLinePhasor.UnconditionalFrobenius

variable {q : ℕ} [NeZero q]

/-- A finite phasor bank whose phase profile is indexed by the carrier height. -/
structure FocalBank where
  amplitude : ℕ → ℝ
  phase : ℝ → ℕ → ℝ
  cutoff : ℕ
  cutoff_pos : 1 ≤ cutoff
  amplitude_one_pos : 0 < amplitude 1
  amplitude_nonneg : ∀ n, 0 ≤ amplitude n

/-- The tested carrier amplitude `(π / 3) n^{-1/2}`. -/
noncomputable def carrierAmplitude (n : ℕ) : ℝ :=
  (Real.pi / 3) * (n : ℝ) ^ (-(1 / 2 : ℝ))

/-- The Mellin phase pulled back to the 3-D height coordinate `z`: `-z log n`. -/
noncomputable def carrierPhase (z : ℝ) (n : ℕ) : ℝ := -z * Real.log n

/-- The canonical completed carrier bank through the physical stage `N`. -/
noncomputable def carrierBank (N : ℕ) (hN : 1 ≤ N) : FocalBank where
  amplitude := carrierAmplitude
  phase := carrierPhase
  cutoff := N
  cutoff_pos := hN
  amplitude_one_pos := by
    simp [carrierAmplitude]
    positivity
  amplitude_nonneg := by
    intro n
    exact mul_nonneg (le_of_lt (div_pos Real.pi_pos (by norm_num)))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- The finite signed phasor closure at 3-D height `z`. -/
noncomputable def focalClosure (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ) : Prop :=
  finiteB χ bank.amplitude (bank.phase z) bank.cutoff = 0

/-- The harmonic Gram pencil built from the finite phasor bank at 3-D height `z`. -/
noncomputable def harmonicGram (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (mu lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (harmonicPencil ((finiteA χ bank.amplitude bank.cutoff : ℝ) : ℂ)
      (finiteB χ bank.amplitude (bank.phase z) bank.cutoff) mu lam)ᴴ *
    harmonicPencil ((finiteA χ bank.amplitude bank.cutoff : ℝ) : ℂ)
      (finiteB χ bank.amplitude (bank.phase z) bank.cutoff) mu lam

/-- A finite Gram rank drop at the 3-D height `z`. -/
noncomputable def FocalRankDrop (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (mu lam : ℂ) : Prop :=
  (harmonicGram χ bank z mu lam).det = 0

/-- The carrier point represented by a real spectral height. -/
noncomputable def carrierPoint (z : ℝ) : ℂ := 1 / 2 + Complex.I * (z : ℂ)

/-- The von Neumann Gram pencil at the same 3-D height and carrier point. -/
noncomputable def vonNeumannGram (z : ℝ) (mu lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  specGram z (carrierPoint z) mu lam

/-- A rank drop of the von Neumann Gram pencil. -/
noncomputable def VonNeumannRankDrop (z : ℝ) (mu lam : ℂ) : Prop :=
  (vonNeumannGram z mu lam).det = 0

/-- A native 3-D zero is, definitionally, full finite focal cancellation at height `z`. -/
noncomputable def ThreeDZero (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ) : Prop :=
  focalClosure χ bank z

omit [NeZero q] in
/-- Exact finite focal cancellation is exactly a finite Gram rank drop. -/
theorem focalClosure_iff_rankDrop (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (mu lam : ℂ) (hlam : lam ≠ mu) :
    focalClosure χ bank z ↔ FocalRankDrop χ bank z mu lam := by
  simpa only [focalClosure, FocalRankDrop, harmonicGram] using
    (finite_gramH_rank_drop_iff_channel_zero χ bank.amplitude (bank.phase z) bank.cutoff
      bank.cutoff_pos bank.amplitude_one_pos bank.amplitude_nonneg mu lam hlam).symm

/-- The von Neumann Gram pencil rank-drops at every carrier point of its own height. -/
theorem vonNeumannGram_rankDrop (z : ℝ) (mu lam : ℂ) (hlam : lam ≠ mu) :
    VonNeumannRankDrop z mu lam := by
  simpa only [VonNeumannRankDrop, vonNeumannGram, carrierPoint] using
    (specGram_rank_drop_on_line z hlam)

/-- A von Neumann Gram rank drop is exactly its nonzero fibre eigenstate. -/
theorem vonNeumannGram_rankDrop_iff_eigenstate (z : ℝ) (mu lam : ℂ) (hlam : lam ≠ mu) :
    VonNeumannRankDrop z mu lam ↔
      ∃ ψ : ℂ, ψ ≠ 0 ∧ specOp (vonNeumannOp z) (carrierPoint z) ψ = 0 := by
  rw [VonNeumannRankDrop, vonNeumannGram,
    specGram_det_zero_iff z (carrierPoint z) hlam,
    ← specOp_kernel_iff_specBchan_zero]

/-- The von Neumann fibre has a nonzero kernel mode at every marked carrier height. -/
theorem carrier_kernel_realized (z : ℝ) :
    ∃ ψ : ℂ, ψ ≠ 0 ∧ specOp (vonNeumannOp z) (carrierPoint z) ψ = 0 := by
  apply (specOp_kernel_iff_specBchan_zero z (carrierPoint z)).mpr
  simp only [carrierPoint, specBchan, specHeight]
  ring_nf
  rw [Complex.I_sq]
  ring

omit [NeZero q] in
/-- Full finite focal cancellation is a native 3-D zero by definition. -/
theorem focalCancellation_to_threeDZero (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (hclose : focalClosure χ bank z) : ThreeDZero χ bank z := hclose

omit [NeZero q] in
/-- The harmonic Gram pencil detects every native 3-D zero by a rank drop. -/
theorem threeDZero_harmonicRankDrop (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (mu lam : ℂ) (hlam : lam ≠ mu) (hzero : ThreeDZero χ bank z) :
    FocalRankDrop χ bank z mu lam :=
  (focalClosure_iff_rankDrop χ bank z mu lam hlam).mp hzero

omit [NeZero q] in
/-- A native 3-D zero has simultaneous harmonic and von Neumann Gram rank drops, and an eigenstate. -/
theorem threeDZero_twoGram_eigenstate (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (mu lam : ℂ) (hlam : lam ≠ mu) (hzero : ThreeDZero χ bank z) :
    FocalRankDrop χ bank z mu lam ∧ VonNeumannRankDrop z mu lam ∧
      ∃ ψ : ℂ, ψ ≠ 0 ∧ specOp (vonNeumannOp z) (carrierPoint z) ψ = 0 := by
  refine ⟨threeDZero_harmonicRankDrop χ bank z mu lam hlam hzero,
    vonNeumannGram_rankDrop z mu lam hlam, ?_⟩
  exact (vonNeumannGram_rankDrop_iff_eigenstate z mu lam hlam).mp
    (vonNeumannGram_rankDrop z mu lam hlam)

omit [NeZero q] in
/-- The carrier coordinate of every native 3-D zero lies on the midline. -/
theorem threeDZero_on_midline (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (_ : ThreeDZero χ bank z) :
    (carrierPoint z).re = 1 / 2 := by
  simp [carrierPoint]

end CriticalLinePhasor.ThreeDFocal

#print axioms CriticalLinePhasor.ThreeDFocal.focalClosure_iff_rankDrop
#print axioms CriticalLinePhasor.ThreeDFocal.vonNeumannGram_rankDrop
#print axioms CriticalLinePhasor.ThreeDFocal.vonNeumannGram_rankDrop_iff_eigenstate
#print axioms CriticalLinePhasor.ThreeDFocal.carrier_kernel_realized
#print axioms CriticalLinePhasor.ThreeDFocal.focalCancellation_to_threeDZero
#print axioms CriticalLinePhasor.ThreeDFocal.threeDZero_harmonicRankDrop
#print axioms CriticalLinePhasor.ThreeDFocal.threeDZero_twoGram_eigenstate
#print axioms CriticalLinePhasor.ThreeDFocal.threeDZero_on_midline
