import Mathlib

/-!
# Spatial pencils and carrier changes

Unfolded local target: for complex matrices A and B, A* = A, B* = B and
A v = z B v imply Im z = 0 when Re(v* B v) > 0.  The spatial pencil is
(A ⊗ I₃) - z (B ⊗ I₃).  A carrier change W acts on BOTH coefficients by
congruence, giving W* (A - z B) W; W may include scales and mirrored lanes.

What would I do without a prior expectation? Compute the imaginary part of
the pencil pairing, and compute the metric mass of the actual cancellation vector.
Two decompositions and their first Lean lines:
* Pairing: `have hAz := hA.im_star_dotProduct_mulVec_self v`.
* Gram feature map: `rw [Matrix.conjTranspose_mul_self_mulVec_eq_zero]`.

Searches performed before construction:
`rg -n 'eigen(height|value).*real.*(nonzero|mass|semidef)|gram.*pencil.*real|
pencil.*congruence|congruence.*pencil|metric.*(nonnull|nonzero)|
spatialLift.*mulVec|twoLane.*warp|warp.*twoLane' RequestProject
.lake/packages/mathlib/Mathlib --glob '*.lean'`
`rg -n 'mulVec.*kronecker|kronecker.*mulVec|posSemidef.*kronecker|
IsHermitian.*kronecker|star_dotProduct_mulVec|dotProduct_mulVec.*(zero|re)'
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix
.lake/packages/mathlib/Mathlib/Analysis/Matrix --glob '*.lean'`
LeanSearch: positive semidefinite Hermitian generalized eigenvalue with positive metric form.
Loogle: `Matrix.PosSemidef, Matrix.mulVec`.
-/

open Matrix Complex
open scoped BigOperators Kronecker ComplexOrder

namespace CriticalLinePhasor.Pencil3D

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Reality uses the mass of the particular state, allowing a degenerate metric elsewhere. -/
theorem eigenvalue_real_of_mass_pos (A B : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (z : ℂ) (v : ι → ℂ)
    (hmass : 0 < (star v ⬝ᵥ B.mulVec v).re)
    (heig : A.mulVec v = z • B.mulVec v) : z.im = 0 := by
  have hAz := hA.im_star_dotProduct_mulVec_self v
  have hBz := hB.im_star_dotProduct_mulVec_self v
  change (star v ⬝ᵥ A.mulVec v).im = 0 at hAz
  change (star v ⬝ᵥ B.mulVec v).im = 0 at hBz
  rw [heig, dotProduct_smul, smul_eq_mul, Complex.mul_im, hBz] at hAz
  nlinarith

/-- For a positive semidefinite metric, nonzero metric image gives positive mass. -/
theorem mass_pos_of_metric_image_ne_zero (B : Matrix ι ι ℂ) (hB : B.PosSemidef)
    (v : ι → ℂ) (hv : B.mulVec v ≠ 0) : 0 < (star v ⬝ᵥ B.mulVec v).re := by
  have hn := hB.re_dotProduct_nonneg v
  have hi := hB.isHermitian.im_star_dotProduct_mulVec_self v
  change 0 ≤ (star v ⬝ᵥ B.mulVec v).re at hn
  change (star v ⬝ᵥ B.mulVec v).im = 0 at hi
  by_contra h
  have hr : (star v ⬝ᵥ B.mulVec v).re = 0 := by linarith
  apply hv
  apply (hB.dotProduct_mulVec_zero_iff (x := v)).mp
  exact Complex.ext hr hi

/-- The generalized eigenvalue is real for every state outside the metric kernel. -/
theorem eigenvalue_real_of_metric_image_ne_zero (A B : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hB : B.PosSemidef) (z : ℂ) (v : ι → ℂ)
    (hv : B.mulVec v ≠ 0) (heig : A.mulVec v = z • B.mulVec v) : z.im = 0 :=
  eigenvalue_real_of_mass_pos A B hA hB.isHermitian z v
    (mass_pos_of_metric_image_ne_zero B hB v hv) heig

/-- The spatial lift of a matrix, with three spatial coordinates for every lane. -/
noncomputable def spatial (A : Matrix ι ι ℂ) : Matrix (ι × Fin 3) (ι × Fin 3) ℂ :=
  A ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)

omit [Fintype ι] in
theorem spatial_isHermitian (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (spatial A).IsHermitian := by
  change (A ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))ᴴ = _
  rw [Matrix.conjTranspose_kronecker, hA.eq, Matrix.conjTranspose_one]
  rfl

theorem spatial_posSemidef (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    (spatial B).PosSemidef :=
  hB.kronecker Matrix.PosSemidef.one

/-- Carrier changes act simultaneously on the operator coefficient and its metric. -/
noncomputable def carrierChange (A : Matrix ι ι ℂ) (W : Matrix ι κ ℂ) : Matrix κ κ ℂ :=
  Wᴴ * A * W

omit [Fintype κ] in
theorem carrierChange_pencil (A B : Matrix ι ι ℂ) (W : Matrix ι κ ℂ) (z : ℂ) :
    carrierChange (A - z • B) W = carrierChange A W - z • carrierChange B W := by
  simp only [carrierChange, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul]

omit [Fintype κ] in
theorem carrierChange_isHermitian (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (W : Matrix ι κ ℂ) : (carrierChange A W).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_mul W hA

theorem carrierChange_posSemidef (B : Matrix ι ι ℂ) (hB : B.PosSemidef)
    (W : Matrix ι κ ℂ) : (carrierChange B W).PosSemidef :=
  hB.conjTranspose_mul_mul_same W

/-- Spatial lifting and arbitrary carrier scales preserve reality on positive-mass states. -/
theorem spatial_carrier_eigenvalue_real (A B : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hB : B.PosSemidef) (W : Matrix (ι × Fin 3) κ ℂ)
    (z : ℂ) (v : κ → ℂ) (hv : (carrierChange (spatial B) W).mulVec v ≠ 0)
    (heig : (carrierChange (spatial A) W).mulVec v =
      z • (carrierChange (spatial B) W).mulVec v) : z.im = 0 :=
  eigenvalue_real_of_metric_image_ne_zero _ _
    (carrierChange_isHermitian _ (spatial_isHermitian A hA) W)
    (carrierChange_posSemidef _ (spatial_posSemidef B hB) W) z v hv heig

/-- A feature cancellation is in the common kernel of the Gram metric and height coefficient. -/
theorem feature_cancellation_common_kernel (Q : Matrix ι κ ℂ) (D : Matrix ι ι ℂ)
    (v : κ → ℂ) (hv : Q.mulVec v = 0) :
    (Qᴴ * Q).mulVec v = 0 ∧ (Qᴴ * D * Q).mulVec v = 0 := by
  constructor <;> simp only [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

/-- A common-kernel vector satisfies the pencil equation at every complex parameter. -/
theorem feature_cancellation_pencil (Q : Matrix ι κ ℂ) (D : Matrix ι ι ℂ)
    (v : κ → ℂ) (hv : Q.mulVec v = 0) (z : ℂ) :
    (Qᴴ * D * Q).mulVec v = z • (Qᴴ * Q).mulVec v := by
  obtain ⟨hB, hA⟩ := feature_cancellation_common_kernel Q D v hv
  rw [hB, hA, smul_zero]

/-- Carrier congruence preserves a zero feature image when the changed state has that image. -/
theorem carrier_feature_cancellation (Q : Matrix ι κ ℂ) (W : Matrix κ κ ℂ)
    (v : κ → ℂ) (hv : Q.mulVec (W.mulVec v) = 0) :
    (carrierChange (Qᴴ * Q) W).mulVec v = 0 := by
  unfold carrierChange
  simp only [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

/-- The imaginary part of the full pencil pairing, before imposing a kernel equation. -/
theorem pencil_pairing_im (A B : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (z : ℂ) (v : ι → ℂ) :
    (star v ⬝ᵥ (A - z • B).mulVec v).im =
      -z.im * (star v ⬝ᵥ B.mulVec v).re := by
  have hAi := hA.im_star_dotProduct_mulVec_self v
  have hBi := hB.im_star_dotProduct_mulVec_self v
  change (star v ⬝ᵥ A.mulVec v).im = 0 at hAi
  change (star v ⬝ᵥ B.mulVec v).im = 0 at hBi
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, Complex.sub_im, Complex.mul_im, hAi, hBi]
  ring

/-- Approximate pencil kernels also give reality, provided their limiting metric mass is positive.
The finite state space is allowed to vary with the stage. -/
theorem eigenvalue_real_of_pencil_limit {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (A B : (n : ℕ) → Matrix (ι n) (ι n) ℂ)
    (hA : ∀ n, (A n).IsHermitian) (hB : ∀ n, (B n).IsHermitian)
    (z : ℂ) (v : (n : ℕ) → ι n → ℂ) (m : ℝ) (hm : 0 < m)
    (hmass : Filter.Tendsto (fun n => (star (v n) ⬝ᵥ (B n).mulVec (v n)).re)
      Filter.atTop (nhds m))
    (hres : Filter.Tendsto
      (fun n => (star (v n) ⬝ᵥ (A n - z • B n).mulVec (v n)).im)
      Filter.atTop (nhds 0)) : z.im = 0 := by
  have hlimit := hmass.const_mul (-z.im)
  have hres' : Filter.Tendsto
      (fun n => -z.im * (star (v n) ⬝ᵥ (B n).mulVec (v n)).re)
      Filter.atTop (nhds 0) := by
    simpa only [pencil_pairing_im _ _ (hA _) (hB _)] using hres
  have heq := tendsto_nhds_unique hlimit hres'
  nlinarith

end CriticalLinePhasor.Pencil3D

#print axioms CriticalLinePhasor.Pencil3D.eigenvalue_real_of_mass_pos
#print axioms CriticalLinePhasor.Pencil3D.eigenvalue_real_of_metric_image_ne_zero
#print axioms CriticalLinePhasor.Pencil3D.carrierChange_pencil
#print axioms CriticalLinePhasor.Pencil3D.spatial_carrier_eigenvalue_real
#print axioms CriticalLinePhasor.Pencil3D.feature_cancellation_common_kernel
#print axioms CriticalLinePhasor.Pencil3D.feature_cancellation_pencil
#print axioms CriticalLinePhasor.Pencil3D.carrier_feature_cancellation
#print axioms CriticalLinePhasor.Pencil3D.pencil_pairing_im
#print axioms CriticalLinePhasor.Pencil3D.eigenvalue_real_of_pencil_limit
