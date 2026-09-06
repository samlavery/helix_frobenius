import RequestProject.HermitianPencil3D
import RequestProject.ThreeDFocalEvent

/-!
# The two-ended spatial pencil and the full analytic fiber

The operator coefficients are the actual geometric feature matrices from
`GeometricPhasorClosure`: B = diag(Q₊*Q₊, Q₋*Q₋), with height and conjugate
coupling blocks in A.  Signed real heights are permitted.  We then lift BOTH
coefficients to the three spatial coordinates and change both by the same carrier matrix.

Independently, the full analytic fiber is evaluated at an arbitrary complex s.
Its harmonic Gram matrix has a nonzero spatial kernel at every L-zero, with no
restriction on Re s in that result.  The kernel and the pencil's metric image are
kept explicit, so a Gram kernel is not silently substituted for a positive-mass state.

Unfolded constructions:
* A = [[Q₊*diag(d)Q₊, C], [C*, Q₋*diag(d)Q₋]], C = Q₊*diag(cell)Q₋.
* P(z) = W*((A ⊗ I₃) - z (B ⊗ I₃))W.
* Fχ(s) = [[1,Lχ(s)],[0,Lχ(s)]], Gχ(s) = Fχ(s)*Fχ(s) ⊗ I₃.

Search commands:
`rg -n 'heightA.*(signed|real)|twoLane.*(signed|mirror)|spatial.*eigenvalue|
Pencil.*mass' RequestProject --glob '*.lean'`
`rg -n 'isHermitian_.*(conjTranspose|diagonal)|IsHermitian.*diagonal|
diagonal.*isHermitian|mulVec.*(conjTranspose|zero_iff)'
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix --glob '*.lean'`

Decompositions: pair the actual pencil equation with its state, or construct the
full fiber Gram kernel first and compute its metric image.  First Lean lines:
`apply spatial_carrier_eigenvalue_real` and
`apply Matrix.exists_mulVec_eq_zero_iff.mpr`.
-/

open Matrix Complex
open scoped BigOperators Kronecker ComplexOrder

namespace CriticalLinePhasor.Pencil3D

open Geometric HarmonicCell

/-- Hermiticity of the height coefficient holds for every signed real height profile. -/
theorem heightA_isHermitian_signed {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (Q : Matrix ι κ ℂ) (d : ι → ℝ) :
    (heightA Q d).IsHermitian := by
  apply Matrix.isHermitian_conjTranspose_mul_mul
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  simp [IsSelfAdjoint]

/-- The conjugate lanes retain the same height profile, as in the native geometric pencil. -/
theorem twoLaneHelixA_isHermitian_signed {N K₁ K₂ : ℕ}
    (Qp : Matrix (Fin N) (Fin K₁) ℂ) (Qm : Matrix (Fin N) (Fin K₂) ℂ)
    (d : Fin N → ℝ) : (twoLaneHelixA Qp Qm d).IsHermitian :=
  twoLaneA_isHermitian _ (heightA_isHermitian_signed Qp d)
    (heightA_isHermitian_signed Qm d)

/-- Reality for the mirrored 3D pencil, including scaled carrier coordinates. -/
theorem twoLane_spatial_eigenvalue_real {N K₁ K₂ : ℕ} {κ : Type*} [Fintype κ]
    (Qp : Matrix (Fin N) (Fin K₁) ℂ) (Qm : Matrix (Fin N) (Fin K₂) ℂ)
    (d : Fin N → ℝ) (W : Matrix ((Fin K₁ ⊕ Fin K₂) × Fin 3) κ ℂ)
    (z : ℂ) (v : κ → ℂ)
    (hv : (carrierChange (spatial (twoLaneB Qp Qm)) W).mulVec v ≠ 0)
    (heig : (carrierChange (spatial (twoLaneHelixA Qp Qm d)) W).mulVec v =
      z • (carrierChange (spatial (twoLaneB Qp Qm)) W).mulVec v) : z.im = 0 :=
  spatial_carrier_eigenvalue_real _ _ (twoLaneHelixA_isHermitian_signed Qp Qm d)
    (twoLaneB_posSemidef Qp Qm) W z v hv heig

variable {q : ℕ} [NeZero q]

/-- The normalized harmonic channel matrix of the full L-function fiber. -/
noncomputable def fullFiberMatrix (χ : DirichletCharacter ℂ q) (s : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  harmonicPencil 1 (DirichletCharacter.LFunction χ s) 0 1

/-- The full fiber's spatial Gram matrix, using the repository's actual spatial lift. -/
noncomputable def fullFiberGram3D (χ : DirichletCharacter ℂ q) (s : ℂ) :
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
  ThreeDFocal.spatialLiftGram ((fullFiberMatrix χ s)ᴴ * fullFiberMatrix χ s)

theorem fullFiberGram3D_posSemidef (χ : DirichletCharacter ℂ q) (s : ℂ) :
    (fullFiberGram3D χ s).PosSemidef :=
  spatial_posSemidef _ (Matrix.posSemidef_conjTranspose_mul_self _)

/-- Exact rank-drop calculation for every complex input of the full analytic fiber. -/
theorem fullFiberGram3D_det (χ : DirichletCharacter ℂ q) (s : ℂ) :
    (fullFiberGram3D χ s).det =
      (star (DirichletCharacter.LFunction χ s) * DirichletCharacter.LFunction χ s) ^ 3 := by
  rw [fullFiberGram3D, ThreeDFocal.spatialLiftGram_det, Matrix.det_mul,
    Matrix.det_conjTranspose]
  simp [fullFiberMatrix, harmonicPencil_det]

/-- Every L-zero supplies a nonzero 3D Gram kernel state, without a real-part assumption. -/
theorem L_zero_fullFiber3D_kernel (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : DirichletCharacter.LFunction χ s = 0) :
    ∃ v : Fin 2 × Fin 3 → ℂ, v ≠ 0 ∧ (fullFiberGram3D χ s).mulVec v = 0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mpr
  rw [fullFiberGram3D_det, hs]
  simp

/-- The Gram kernel has zero mass for that Gram metric. -/
theorem fullFiber3D_kernel_mass (χ : DirichletCharacter ℂ q) (s : ℂ)
    (v : Fin 2 × Fin 3 → ℂ) (hv : (fullFiberGram3D χ s).mulVec v = 0) :
    (star v ⬝ᵥ (fullFiberGram3D χ s).mulVec v).re = 0 := by
  rw [hv, dotProduct_zero, Complex.zero_re]

end CriticalLinePhasor.Pencil3D

#print axioms CriticalLinePhasor.Geometric.twoLaneB_posSemidef
#print axioms CriticalLinePhasor.Geometric.twoLaneA_isHermitian
#print axioms CriticalLinePhasor.ThreeDFocal.spatialLiftGram_det
#print axioms CriticalLinePhasor.Pencil3D.heightA_isHermitian_signed
#print axioms CriticalLinePhasor.Pencil3D.twoLane_spatial_eigenvalue_real
#print axioms CriticalLinePhasor.Pencil3D.fullFiberGram3D_det
#print axioms CriticalLinePhasor.Pencil3D.L_zero_fullFiber3D_kernel
#print axioms CriticalLinePhasor.Pencil3D.fullFiber3D_kernel_mass
