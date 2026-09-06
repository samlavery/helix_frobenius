import RequestProject.ThreeDNativeLaneCoupling

/-!
# The normalized native 3D pencil

Use the actual native lane matrices and the same scalar 1/(N+1) on BOTH
pencil coefficients.  This fixes the reference state's metric mass at one.
Both lanes retain the same physical heights and the conjugate off-diagonal coupling.

Unfolded local target: Im(v*(A_N-z B_N)v) = -Im(z), because A_N and B_N
are Hermitian and v*B_Nv=1.  Thus an approximate spectral capture must
make this full pencil pairing tend to zero; the native scalar coupling has
its separate, proved limit to the L-function.

Decompositions: compute the reference diagonal entry, or pair the full
pencil before taking a limit.  First Lean lines:
`rw [Matrix.smul_mulVec, dotProduct_smul]` and
`rw [pencil_pairing_im]`.

Searches:
`rg -n 'pencil.*(pairing|residual|coerciv)|imag.*pencil|pencil.*imag|
eigen.*mass.*tendsto|tendsto.*pencil.*zero' RequestProject
.lake/packages/mathlib/Mathlib --glob '*.lean'`
`rg -n 'IsHermitian.smul|theorem.*smul|lemma.*smul'
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Hermitian.lean
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean`
-/

open Matrix Complex Filter Topology
open scoped BigOperators Kronecker ComplexOrder

namespace CriticalLinePhasor.Pencil3D

open Geometric SpectralFiber

noncomputable def nativePencilA (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    Matrix ((Fin 1 ⊕ Fin 1) × Fin 3) ((Fin 1 ⊕ Fin 1) × Fin 3) ℂ :=
  (1 / ((N + 1 : ℕ) : ℝ)) •
    spatial (twoLaneHelixA (referenceLane (N + 1)) (nativeFiberLane w s (N + 1))
      (fun i => (i.val + 1 : ℝ)))

noncomputable def nativePencilB (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    Matrix ((Fin 1 ⊕ Fin 1) × Fin 3) ((Fin 1 ⊕ Fin 1) × Fin 3) ℂ :=
  (1 / ((N + 1 : ℕ) : ℝ)) •
    spatial (twoLaneB (referenceLane (N + 1)) (nativeFiberLane w s (N + 1)))

theorem nativePencilA_isHermitian (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    (nativePencilA w s N).IsHermitian :=
  (native_spatial_isHermitian w s (N + 1)).smul (IsSelfAdjoint.all _)

theorem nativePencilB_isHermitian (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    (nativePencilB w s N).IsHermitian :=
  (native_spatial_metric_posSemidef w s (N + 1)).isHermitian.smul (IsSelfAdjoint.all _)

theorem nativePencilB_posDef (w : ℕ → ℂ) (hw : w 1 ≠ 0) (s : ℂ) (N : ℕ) :
    (nativePencilB w s N).PosDef :=
  (native_spatial_metric_posDef w hw s (N + 1) (Nat.succ_pos _)).smul (by positivity)

/-- Unconditional metric positivity for the zeta fiber's actual eta configuration. -/
theorem eta_nativePencilB_posDef (s : ℂ) (N : ℕ) :
    (nativePencilB etaW s N).PosDef :=
  nativePencilB_posDef etaW (by norm_num [etaW]) s N

/-- Unconditional metric positivity for every Dirichlet-character fiber. -/
theorem character_nativePencilB_posDef {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (N : ℕ) :
    (nativePencilB (fun n => χ (n : ZMod q)) s N).PosDef :=
  nativePencilB_posDef _ (by simp) s N

theorem nativePencilB_reference_mass (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    star referenceState ⬝ᵥ (nativePencilB w s N).mulVec referenceState = 1 := by
  rw [nativePencilB, Matrix.smul_mulVec, dotProduct_smul, referenceState_metric_mass]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_natCast]
  exact div_mul_cancel₀ 1 (by exact_mod_cast Nat.succ_ne_zero N)

/-- Exact normalized pencil pairing, including the full complex spectral parameter. -/
theorem nativePencil_pairing_im (w : ℕ → ℂ) (s z : ℂ) (N : ℕ) :
    (star referenceState ⬝ᵥ
      (nativePencilA w s N - z • nativePencilB w s N).mulVec referenceState).im = -z.im := by
  rw [pencil_pairing_im _ _ (nativePencilA_isHermitian w s N)
    (nativePencilB_isHermitian w s N), nativePencilB_reference_mass]
  simp

end CriticalLinePhasor.Pencil3D

#print axioms CriticalLinePhasor.Pencil3D.nativePencilA_isHermitian
#print axioms CriticalLinePhasor.Pencil3D.nativePencilB_posDef
#print axioms CriticalLinePhasor.Pencil3D.eta_nativePencilB_posDef
#print axioms CriticalLinePhasor.Pencil3D.character_nativePencilB_posDef
#print axioms CriticalLinePhasor.Pencil3D.nativePencilB_reference_mass
#print axioms CriticalLinePhasor.Pencil3D.nativePencil_pairing_im
