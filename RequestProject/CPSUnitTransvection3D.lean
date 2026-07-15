import RequestProject.CPSFiniteFieldConverse3D

/-!
# Unit transvections generate every transvection in the 3D CPS carrier

A coordinate dilation on the source axis and its reciprocal dilation on the target axis
conjugate the unit winding cell to an arbitrary nonzero winding cell.  Consequently, diagonal
clock invariance and invariance under unit transvections imply invariance under every
transvection.
-/

namespace CriticalLinePhasor.ThreeDConverse

/-- The diagonal carrier move which scales exactly coordinate `i` by `q`. -/
noncomputable def coordinateScaleGL
    {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    (i : n) (q : K) (hq : q ≠ 0) : Matrix.GeneralLinearGroup n K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal (Pi.mulSingle i q)) (by
      rw [Matrix.det_diagonal, Fintype.prod_pi_mulSingle']
      exact hq)

/-- Scaling the `i`-axis by `q`, applying the unit `(i,j)` winding, and scaling the `i`-axis
back by `q⁻¹` is the winding with parameter `q`. -/
theorem coordinateScaleGL_mul_transvectionGL_mul_coordinateScaleGL_inv
    {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    (i j : n) (hij : i ≠ j) (q : K) (hq : q ≠ 0) :
    coordinateScaleGL i q hq * transvectionGL i j hij (1 : K) *
        coordinateScaleGL i q⁻¹ (inv_ne_zero hq) =
      transvectionGL i j hij q := by
  ext a b
  by_cases hai : a = i
  · subst a
    by_cases hbi : b = i
    · subst b
      simp [coordinateScaleGL, transvectionGL, Matrix.transvection, Ne.symm hij, hq]
    · by_cases hbj : b = j
      · subst b
        simp [coordinateScaleGL, transvectionGL, Matrix.transvection, hij]
      · simp [coordinateScaleGL, transvectionGL, Matrix.transvection,
          Ne.symm hbi, Ne.symm hbj]
  · by_cases hab : a = b
    · subst b
      simp [coordinateScaleGL, transvectionGL, Matrix.transvection, Ne.symm hai]
    · simp [coordinateScaleGL, transvectionGL, Matrix.transvection, Ne.symm hai, hab]

/-- Diagonal-clock invariance and the unit winding identity imply invariance under every winding
parameter. -/
theorem all_transvection_readout_invariant_of_unit
    {n K X : Type*} [Fintype n] [DecidableEq n] [Field K]
    [MulAction (Matrix.GeneralLinearGroup n K) X]
    (readout : X → ℂ)
    (hdiag : ∀ (D : n → K) (hD : Matrix.det (Matrix.diagonal D) ≠ 0) (x : X),
      readout
          (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal D) hD • x) =
        readout x)
    (hunit : ∀ (i j : n) (hij : i ≠ j) (x : X),
      readout (transvectionGL i j hij (1 : K) • x) = readout x) :
    ∀ (i j : n) (hij : i ≠ j) (q : K) (x : X),
      readout (transvectionGL i j hij q • x) = readout x := by
  intro i j hij q x
  by_cases hq : q = 0
  · subst q
    simp [transvectionGL_zero]
  · rw [← coordinateScaleGL_mul_transvectionGL_mul_coordinateScaleGL_inv i j hij q hq]
    simp only [mul_smul]
    calc
      readout (coordinateScaleGL i q hq •
          transvectionGL i j hij (1 : K) • coordinateScaleGL i q⁻¹ (inv_ne_zero hq) • x) =
          readout (transvectionGL i j hij (1 : K) •
            coordinateScaleGL i q⁻¹ (inv_ne_zero hq) • x) := by
        simpa [coordinateScaleGL] using
          hdiag (Pi.mulSingle i q) (by
            rw [Matrix.det_diagonal, Fintype.prod_pi_mulSingle']
            exact hq)
            (transvectionGL i j hij (1 : K) •
              coordinateScaleGL i q⁻¹ (inv_ne_zero hq) • x)
      _ = readout (coordinateScaleGL i q⁻¹ (inv_ne_zero hq) • x) :=
        hunit i j hij _
      _ = readout x := by
        simpa [coordinateScaleGL] using
          hdiag (Pi.mulSingle i q⁻¹) (by
            rw [Matrix.det_diagonal, Fintype.prod_pi_mulSingle']
            exact inv_ne_zero hq) x

/-- **Unit-winding 3D CPS converse.** Diagonal carrier clocks and the single unit winding in every
off-diagonal direction generate readout invariance under the full general linear group. -/
theorem cps3D_readout_invariant_of_unit
    {n K X : Type*} [Fintype n] [DecidableEq n] [Field K]
    [MulAction (Matrix.GeneralLinearGroup n K) X]
    (readout : X → ℂ)
    (hdiag : ∀ (D : n → K) (hD : Matrix.det (Matrix.diagonal D) ≠ 0) (x : X),
      readout
          (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal D) hD • x) =
        readout x)
    (hunit : ∀ (i j : n) (hij : i ≠ j) (x : X),
      readout (transvectionGL i j hij (1 : K) • x) = readout x)
    (g : Matrix.GeneralLinearGroup n K) (x : X) :
    readout (g • x) = readout x := by
  apply cps3D_readout_invariant readout hdiag
  intro t y
  rcases t with ⟨i, j, hij, q⟩
  exact all_transvection_readout_invariant_of_unit readout hdiag hunit i j hij q y

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.coordinateScaleGL_mul_transvectionGL_mul_coordinateScaleGL_inv
#print axioms CriticalLinePhasor.ThreeDConverse.all_transvection_readout_invariant_of_unit
#print axioms CriticalLinePhasor.ThreeDConverse.cps3D_readout_invariant_of_unit
