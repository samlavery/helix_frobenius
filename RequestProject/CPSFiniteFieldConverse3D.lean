import RequestProject.CPSBasicIdentityMultiWinding

/-!
# A finite-field CPS converse theorem in three dimensions

For a finite field, a one-parameter transvection is an additive winding cell.  Equality of the
complete character-twist family for that cell and its translate forces transvection invariance by
finite Fourier separation.  Together with diagonal-clock invariance, matrix generation gives full
`GL(n)` invariance of the readout.
-/

namespace CriticalLinePhasor.ThreeDConverse

/-- The general-linear element associated with a one-parameter transvection. -/
noncomputable def transvectionGL
    {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    (i j : n) (hij : i ≠ j) (c : K) : Matrix.GeneralLinearGroup n K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
    (by rw [Matrix.det_transvection_of_ne i j hij c]; exact one_ne_zero)

/-- The zero winding parameter is the identity linear move. -/
theorem transvectionGL_zero
    {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    (i j : n) (hij : i ≠ j) : transvectionGL i j hij (0 : K) = 1 := by
  ext a b
  simp [transvectionGL]

/-- Addition of winding parameters is multiplication of their transvections. -/
theorem transvectionGL_add
    {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    (i j : n) (hij : i ≠ j) (c d : K) :
    transvectionGL i j hij (c + d) =
      transvectionGL i j hij c * transvectionGL i j hij d := by
  ext a b
  change Matrix.transvection i j (c + d) a b =
    (Matrix.transvection i j c * Matrix.transvection i j d) a b
  rw [Matrix.transvection_mul_transvection_same i j hij]

/-- The complete additive-twist identity on a one-parameter winding cell forces invariance under
the corresponding transvection. -/
theorem transvection_readout_invariant_of_all_twists
    {n K X : Type*} [Fintype n] [DecidableEq n] [Field K] [Finite K]
    [MulAction (Matrix.GeneralLinearGroup n K) X]
    (readout : X → ℂ) (i j : n) (hij : i ≠ j) (d : K) (x : X)
    (hTwist : ∀ character : AddChar K ℂ,
      finiteAbelianTwistReadout K
          (fun c => readout (transvectionGL i j hij (c + d) • x)) character =
        finiteAbelianTwistReadout K
          (fun c => readout (transvectionGL i j hij c • x)) character) :
    readout (transvectionGL i j hij d • x) = readout x := by
  have hcell :
      (fun c => readout (transvectionGL i j hij (c + d) • x)) =
        (fun c => readout (transvectionGL i j hij c • x)) :=
    finiteAbelianCell_eq_of_all_twists_eq hTwist
  have hzero := congrFun hcell 0
  simpa [transvectionGL_zero] using hzero

/-- All one-parameter twisted basic identities supply invariance under every transvection
structure used by the rank-n carrier generator theorem. -/
theorem all_transvection_readout_invariant_of_all_twists
    {n K X : Type*} [Fintype n] [DecidableEq n] [Field K] [Finite K]
    [MulAction (Matrix.GeneralLinearGroup n K) X]
    (readout : X → ℂ)
    (hTwist : ∀ (i j : n) (hij : i ≠ j) (d : K) (x : X)
        (character : AddChar K ℂ),
      finiteAbelianTwistReadout K
          (fun c => readout (transvectionGL i j hij (c + d) • x)) character =
        finiteAbelianTwistReadout K
          (fun c => readout (transvectionGL i j hij c • x)) character) :
    ∀ (t : Matrix.TransvectionStruct n K) (x : X),
      readout
          (Matrix.GeneralLinearGroup.mkOfDetNeZero t.toMatrix (by simp) • x) =
        readout x := by
  intro t x
  rcases t with ⟨i, j, hij, d⟩
  exact transvection_readout_invariant_of_all_twists
    readout i j hij d x (hTwist i j hij d x)

/-- **Finite-field 3D CPS converse theorem.** Diagonal completion-clock identities and the complete
family of additive twisted basic identities imply invariance of the readout under every element of
`GL(n, K)`. -/
theorem cpsFiniteField3D_readout_invariant
    {n K X : Type*} [Fintype n] [DecidableEq n] [Field K] [Finite K]
    [MulAction (Matrix.GeneralLinearGroup n K) X]
    (readout : X → ℂ)
    (hdiag : ∀ (D : n → K) (hD : Matrix.det (Matrix.diagonal D) ≠ 0) (x : X),
      readout
          (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal D) hD • x) =
        readout x)
    (hTwist : ∀ (i j : n) (hij : i ≠ j) (d : K) (x : X)
        (character : AddChar K ℂ),
      finiteAbelianTwistReadout K
          (fun c => readout (transvectionGL i j hij (c + d) • x)) character =
        finiteAbelianTwistReadout K
          (fun c => readout (transvectionGL i j hij c • x)) character)
    (g : Matrix.GeneralLinearGroup n K) (x : X) :
    readout (g • x) = readout x := by
  apply cps3D_readout_invariant readout hdiag
  exact all_transvection_readout_invariant_of_all_twists readout hTwist

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.transvectionGL_add
#print axioms CriticalLinePhasor.ThreeDConverse.transvection_readout_invariant_of_all_twists
#print axioms CriticalLinePhasor.ThreeDConverse.all_transvection_readout_invariant_of_all_twists
#print axioms CriticalLinePhasor.ThreeDConverse.cpsFiniteField3D_readout_invariant
