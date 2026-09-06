import RequestProject.ThreeDNativePencilLimit
import RequestProject.FrobeniusSimilitude

/-!
# Frobenius on the native positive 3D metric

Unfolded target: F = diag(u, conjugate(u)) tensor I_3, where
u = exp(-i y log n).  Prove det F = 1 and F* B_N F = B_N for the
actual normalized native metric.  The two scalar lane masses may differ.

What would I do without a prior expectation? Compute the two diagonal
metric entries and the two off-diagonal coupling entries separately.
Two decompositions: use diagonal matrix multiplication, starting with
`rw [Matrix.diagonal_conjTranspose]`; or lift the two-lane identity,
starting with `simp only [spatial, Matrix.conjTranspose_kronecker]`.

Search commands (repo and Mathlib):
`rg -n -i 'frobenius.*(metric|gram|preserv|conserv|unitar|bounded)|
(metric|gram|unitar|bounded).*frobenius|det.*one.*(isometry|unitar)|
(unitar|isometry).*det.*one' RequestProject --glob '*.lean'`
`rg -n -i 'diagonal.*(conjTranspose|unitary)|unitary.*diagonal|
kronecker.*(conjTranspose|mul)|conjTranspose.*kronecker'
.lake/packages/mathlib/Mathlib --glob '*.lean'`
Semantic searches: LeanSearch, "diagonal matrix conjugate transpose
multiplication preserves a diagonal Hermitian form for complex entries
of norm one"; Loogle, `Matrix.diagonal, Matrix.conjTranspose`.

For the shared prime-power phase:
`rg -n 'mellinSpin.*(mul|pow)|frobeniusBlock.*(mul|pow)|spin.*prime.*pow|
spin.*(mul|pow)' RequestProject --glob '*.lean'`
`rg -n 'log_pow|exp_nat_mul|exp_mul_nat|pow_kronecker|kronecker_pow|diagonal_pow'
.lake/packages/mathlib/Mathlib --glob '*.lean'`
LeanSearch: "complex exponential natural number power equals exponential
of natural number times input"; Loogle: `Complex.exp, HPow.hPow`.
Decompositions: multiply the site operators (`rw [mellinSpin_mul]`), or
expand the common logarithmic phase (`rw [Real.log_pow]`).
-/

open Matrix Complex
open scoped BigOperators Kronecker ComplexOrder

namespace CriticalLinePhasor.Pencil3D

open Geometric FrobeniusSimilitude LFunctionPhasor

noncomputable def laneDiagonal (u v : ℂ) :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  Matrix.diagonal (Sum.elim (fun _ => u) (fun _ => v))

theorem laneDiagonal_det (u v : ℂ) : (laneDiagonal u v).det = u * v := by
  simp [laneDiagonal, Matrix.det_diagonal, Fintype.prod_sum_type]

theorem laneDiagonal_unitary {u v : ℂ} (hu : star u * u = 1) (hv : star v * v = 1) :
    (laneDiagonal u v)ᴴ * laneDiagonal u v = 1 := by
  change (starRingEnd ℂ) u * u = 1 at hu
  change (starRingEnd ℂ) v * v = 1 at hv
  rw [laneDiagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  cases i <;> simp [hu, hv]

theorem laneDiagonal_metric_preserved {N : ℕ}
    (Qp Qm : Matrix (Fin N) (Fin 1) ℂ) {u v : ℂ}
    (hu : star u * u = 1) (hv : star v * v = 1) :
    (laneDiagonal u v)ᴴ * twoLaneB Qp Qm * laneDiagonal u v = twoLaneB Qp Qm := by
  change (starRingEnd ℂ) u * u = 1 at hu
  change (starRingEnd ℂ) v * v = 1 at hv
  rw [laneDiagonal, Matrix.diagonal_conjTranspose, twoLaneB_eq_blockDiag]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc, mul_left_comm, hu, hv]

noncomputable def nativeFrobenius (y : ℝ) (n : ℕ) :
    Matrix ((Fin 1 ⊕ Fin 1) × Fin 3) ((Fin 1 ⊕ Fin 1) × Fin 3) ℂ :=
  spatial (laneDiagonal (mellinSpin y n) (star (mellinSpin y n)))

theorem mellinSpin_pow (y : ℝ) (n k : ℕ) :
    mellinSpin y (n ^ k) = mellinSpin y n ^ k := by
  simp only [mellinSpin, Nat.cast_pow, Real.log_pow, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem laneDiagonal_mul (u v a b : ℂ) :
    laneDiagonal (u * a) (v * b) = laneDiagonal u v * laneDiagonal a b := by
  rw [laneDiagonal, laneDiagonal, laneDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  cases i <;> rfl

theorem nativeFrobenius_mul (y : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    nativeFrobenius y (m * n) = nativeFrobenius y m * nativeFrobenius y n := by
  simp only [nativeFrobenius, mellinSpin_mul y m n hm hn, star_mul,
    spatial, ← Matrix.mul_kronecker_mul, Matrix.one_mul, ← laneDiagonal_mul, mul_comm]

/-- Every prime-power operator is a power of the SAME base-prime operator at the SAME height. -/
theorem nativeFrobenius_pow (y : ℝ) (n k : ℕ) :
    nativeFrobenius y (n ^ k) = nativeFrobenius y n ^ k := by
  induction k with
  | zero => simp [nativeFrobenius, mellinSpin, spatial, laneDiagonal]
  | succ k ih =>
    rw [pow_succ (nativeFrobenius y n), ← ih]
    simp only [nativeFrobenius, mellinSpin_pow]
    simp only [pow_succ, star_mul, spatial,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, ← laneDiagonal_mul, mul_comm]

theorem nativeFrobenius_det_one (y : ℝ) (n : ℕ) :
    (nativeFrobenius y n).det = 1 := by
  simp [nativeFrobenius, spatial, Matrix.det_kronecker, laneDiagonal_det,
    ← starRingEnd_apply, spin_mul_conj]

theorem nativeFrobenius_unitary (y : ℝ) (n : ℕ) :
    (nativeFrobenius y n)ᴴ * nativeFrobenius y n = 1 := by
  have hu : star (mellinSpin y n) * mellinSpin y n = 1 := by
    simpa [mul_comm] using spin_mul_conj y n
  have hv : star (star (mellinSpin y n)) * star (mellinSpin y n) = 1 := by
    simpa using spin_mul_conj y n
  simp only [nativeFrobenius, spatial, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, laneDiagonal_unitary hu hv,
    Matrix.one_mul, Matrix.one_kronecker_one]

theorem nativeFrobenius_metric_preserved (w : ℕ → ℂ) (s : ℂ) (N : ℕ)
    (y : ℝ) (n : ℕ) :
    (nativeFrobenius y n)ᴴ * nativePencilB w s N * nativeFrobenius y n =
      nativePencilB w s N := by
  have hu : star (mellinSpin y n) * mellinSpin y n = 1 := by
    simpa [mul_comm] using spin_mul_conj y n
  have hv : star (star (mellinSpin y n)) * star (mellinSpin y n) = 1 := by
    simpa using spin_mul_conj y n
  simp only [nativeFrobenius, nativePencilB, spatial, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, laneDiagonal_metric_preserved _ _ hu hv]

theorem spatial_laneDiagonal_reference (u v : ℂ) :
    (spatial (laneDiagonal u v)).mulVec referenceState = u • referenceState := by
  ext ⟨i, j⟩
  rcases i with i | i <;> fin_cases i <;> fin_cases j <;>
    simp [spatial, laneDiagonal, referenceState, Matrix.mulVec, dotProduct,
      Matrix.kroneckerMap_apply, Pi.single_apply, Matrix.diagonal_apply, Matrix.one_apply]

theorem carrierChange_pairing {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι ι ℂ) (W : Matrix ι κ ℂ) (v : κ → ℂ) :
    star v ⬝ᵥ (carrierChange B W).mulVec v =
      star (W.mulVec v) ⬝ᵥ B.mulVec (W.mulVec v) := by
  simp only [carrierChange, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul]

/-- One fixed native metric controls the whole prime-power tower at a common height. -/
theorem nativeFrobenius_tower_mass (w : ℕ → ℂ) (s : ℂ) (N : ℕ)
    (y : ℝ) (n k : ℕ) (v : (Fin 1 ⊕ Fin 1) × Fin 3 → ℂ) :
    star ((nativeFrobenius y n ^ k).mulVec v) ⬝ᵥ
      (nativePencilB w s N).mulVec ((nativeFrobenius y n ^ k).mulVec v) =
        star v ⬝ᵥ (nativePencilB w s N).mulVec v := by
  rw [← nativeFrobenius_pow, ← carrierChange_pairing]
  change star v ⬝ᵥ
    ((nativeFrobenius y (n ^ k))ᴴ * nativePencilB w s N *
      nativeFrobenius y (n ^ k)).mulVec v = _
  rw [nativeFrobenius_metric_preserved]

/-- Exact radial accounting for BOTH reciprocal and conjugate lane choices. -/
theorem native_laneDiagonal_reference_mass (w : ℕ → ℂ) (s : ℂ) (N : ℕ) (u v : ℂ) :
    star referenceState ⬝ᵥ
      (carrierChange (nativePencilB w s N) (spatial (laneDiagonal u v))).mulVec
        referenceState = star u * u := by
  rw [carrierChange_pairing, spatial_laneDiagonal_reference]
  simp only [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    nativePencilB_reference_mass, smul_eq_mul, mul_one]
  exact mul_comm _ _

/-- Reciprocal carrier scaling preserves the determinant at every nonzero radius. -/
theorem nativeReciprocal_det_one {u : ℂ} (hu : u ≠ 0) :
    (spatial (laneDiagonal u u⁻¹)).det = 1 := by
  simp [spatial, Matrix.det_kronecker, laneDiagonal_det, mul_inv_cancel₀ hu]

/-- Its metric action retains the radius explicitly, including after the 3D lift. -/
theorem nativeReciprocal_reference_mass (w : ℕ → ℂ) (s : ℂ) (N : ℕ) (u : ℂ) :
    star referenceState ⬝ᵥ
      (carrierChange (nativePencilB w s N) (spatial (laneDiagonal u u⁻¹))).mulVec
        referenceState = (‖u‖ ^ 2 : ℝ) := by
  rw [native_laneDiagonal_reference_mass]
  change (starRingEnd ℂ) u * u = _
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem native_metric_isometry_radius_one (w : ℕ → ℂ) (s : ℂ) (N : ℕ) (u v : ℂ)
    (hF : carrierChange (nativePencilB w s N) (spatial (laneDiagonal u v)) =
      nativePencilB w s N) : ‖u‖ = 1 := by
  have hm := native_laneDiagonal_reference_mass w s N u v
  rw [hF, nativePencilB_reference_mass] at hm
  have hsq : ‖u‖ ^ 2 = 1 := by
    have h := congrArg Complex.re hm.symm
    simpa only [← starRingEnd_apply, mul_comm ((starRingEnd ℂ) u), Complex.mul_conj,
      Complex.ofReal_re, Complex.one_re, Complex.normSq_eq_norm_sq] using h
  nlinarith [norm_nonneg u]

theorem nativeFrobenius_pencil_pairing_im (w : ℕ → ℂ) (s z : ℂ) (N : ℕ)
    (y : ℝ) (n : ℕ) :
    (star referenceState ⬝ᵥ
      (carrierChange (nativePencilA w s N - z • nativePencilB w s N)
        (nativeFrobenius y n)).mulVec referenceState).im = -z.im := by
  rw [carrierChange_pencil]
  have hB : carrierChange (nativePencilB w s N) (nativeFrobenius y n) =
      nativePencilB w s N := nativeFrobenius_metric_preserved w s N y n
  rw [hB, pencil_pairing_im _ _
    (carrierChange_isHermitian _ (nativePencilA_isHermitian w s N) _)
    (nativePencilB_isHermitian w s N), nativePencilB_reference_mass]
  simp

end CriticalLinePhasor.Pencil3D

#print axioms CriticalLinePhasor.FrobeniusSimilitude.frobeniusBlock_det_one
#print axioms CriticalLinePhasor.FrobeniusSimilitude.frobeniusBlock_unitary
#print axioms CriticalLinePhasor.Pencil3D.nativeFrobenius_det_one
#print axioms CriticalLinePhasor.Pencil3D.nativeFrobenius_mul
#print axioms CriticalLinePhasor.Pencil3D.nativeFrobenius_pow
#print axioms CriticalLinePhasor.Pencil3D.nativeFrobenius_unitary
#print axioms CriticalLinePhasor.Pencil3D.nativeFrobenius_metric_preserved
#print axioms CriticalLinePhasor.Pencil3D.nativeFrobenius_tower_mass
#print axioms CriticalLinePhasor.Pencil3D.native_laneDiagonal_reference_mass
#print axioms CriticalLinePhasor.Pencil3D.nativeReciprocal_det_one
#print axioms CriticalLinePhasor.Pencil3D.nativeReciprocal_reference_mass
#print axioms CriticalLinePhasor.Pencil3D.native_metric_isometry_radius_one
#print axioms CriticalLinePhasor.Pencil3D.nativeFrobenius_pencil_pairing_im
