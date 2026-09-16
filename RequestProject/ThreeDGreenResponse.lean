import RequestProject.HermitianPencil3D

/-!
# Green responses before the chart readout

Unfolded construction: P(z) = A - z B, u(z) = P(z)⁻¹ b,
m(z) = b* u(z). A is Hermitian and B is positive definite.
The source b, both pencil coefficients, and the state are retained.
The target identity is Im m(z) = Im z · u(z)* B u(z).
For carrier coordinates x = W v, the transformed data are
(W* A W, W* B W, W* b); the scalar response is unchanged.
These statements concern the operator response, before any identification
with the arithmetic logarithmic derivative.

What would I do without a prior expectation? Solve the full pencil and
pair its equation with the response, retaining all three spatial components.
Two decompositions tried below: `apply Matrix.exists_mulVec_eq_zero_iff.mpr`
for nonsingularity, and `have h := pencil_pairing_im A B hA hB z u`
for the response identity. The first is used contrapositively.

Search commands, before construction (repo and Mathlib):
`rg -n -i 'green.*(response|pencil|herglotz)|weyl.*(matrix|pencil|resolvent)|
resolvent.*(pairing|im|pos)|response.*logDeriv|logDeriv.*response|
matrixCoefficient.*log' RequestProject .lake/packages/mathlib/Mathlib --glob '*.lean'`
`rg -n 'nonsing_inv_mul|mul_nonsing_inv|exists_mulVec_eq_zero_iff|
star_dotProduct|dotProduct_star|star_mulVec|conjTranspose.*mulVec'
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix --glob '*.lean'`
LeanSearch: Hermitian matrix resolvent with positive imaginary part.
Loogle: `Matrix.mul_nonsing_inv`; `"abs_im_le_norm"`.
-/

open Matrix Complex Filter Topology
open scoped ComplexOrder

namespace CriticalLinePhasor.Pencil3D.Green

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def state (A B : Matrix ι ι ℂ) (b : ι → ℂ) (z : ℂ) : ι → ℂ :=
  (A - z • B)⁻¹.mulVec b

noncomputable def response (A B : Matrix ι ι ℂ) (b : ι → ℂ) (z : ℂ) : ℂ :=
  star b ⬝ᵥ state A B b z

theorem pencil_det_ne_zero (A B : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hB : B.PosDef) {z : ℂ} (hz : z.im ≠ 0) : (A - z • B).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, heq⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have heig : A.mulVec v = z • B.mulVec v := by
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, sub_eq_zero] using heq
  exact hz (eigenvalue_real_of_mass_pos A B hA hB.isHermitian z v
    (hB.dotProduct_mulVec_pos hv).1 heig)

theorem state_solves (A B : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hB : B.PosDef) (b : ι → ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    (A - z • B).mulVec (state A B b z) = b := by
  rw [state, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (pencil_det_ne_zero A B hA hB hz)),
    Matrix.one_mulVec]

theorem solution_unique (A B : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hB : B.PosDef) (b : ι → ℂ) {z : ℂ} (hz : z.im ≠ 0)
    (u : ι → ℂ) (hu : (A - z • B).mulVec u = b) : u = state A B b z := by
  rw [state, ← hu, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (pencil_det_ne_zero A B hA hB hz)),
    Matrix.one_mulVec]

omit [DecidableEq ι] in
theorem solution_response_im (A B : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (b u : ι → ℂ) (z : ℂ)
    (hu : (A - z • B).mulVec u = b) :
    (star b ⬝ᵥ u).im = z.im * (star u ⬝ᵥ B.mulVec u).re := by
  have h := pencil_pairing_im A B hA hB z u
  rw [hu, star_dotProduct u b] at h
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

theorem response_im (A B : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hB : B.PosDef) (b : ι → ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    (response A B b z).im = z.im *
      (star (state A B b z) ⬝ᵥ B.mulVec (state A B b z)).re :=
  solution_response_im A B hA hB.isHermitian b _ z (state_solves A B hA hB b hz)

theorem response_im_nonneg (A B : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hB : B.PosDef) (b : ι → ℂ) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (response A B b z).im := by
  rw [response_im A B hA hB b hz.ne']
  exact mul_nonneg hz.le (hB.posSemidef.re_dotProduct_nonneg _)

theorem response_im_pos (A B : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hB : B.PosDef) (b : ι → ℂ) (hb : b ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    0 < (response A B b z).im := by
  have hu : state A B b z ≠ 0 := by
    intro hu
    have heq := state_solves A B hA hB b hz.ne'
    rw [hu, Matrix.mulVec_zero] at heq
    exact hb heq.symm
  rw [response_im A B hA hB b hz.ne']
  exact mul_pos hz (hB.dotProduct_mulVec_pos hu).1

/-- The response is independent of invertible carrier coordinates when the source
and both coefficients are transported together. Scales need not be unitary. -/
theorem carrier_response (A B W : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hB : B.PosDef) (hW : IsUnit W) (b : ι → ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    response (carrierChange A W) (carrierChange B W) (Wᴴ.mulVec b) z =
      response A B b z := by
  have hBW : (carrierChange B W).PosDef :=
    hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hW)
  have hAW := carrierChange_isHermitian A hA W
  have hsol := state_solves _ _ hAW hBW (Wᴴ.mulVec b) hz
  rw [← carrierChange_pencil, carrierChange] at hsol
  simp only [← Matrix.mulVec_mulVec] at hsol
  have hWi : Function.Injective Wᴴ.mulVec :=
    Matrix.mulVec_injective_of_isUnit hW.star
  have hstate := solution_unique A B hA hB b hz _ (hWi hsol)
  unfold response
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
    ← Matrix.dotProduct_mulVec, hstate]

/-- The two-point Green identity keeps the same operator and source at both points. -/
theorem response_difference (A B : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hB : B.PosDef) (b : ι → ℂ) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    response A B b z - star (response A B b w) =
      (z - star w) *
        (star (state A B b w) ⬝ᵥ B.mulVec (state A B b z)) := by
  have hzsol := state_solves A B hA hB b hz
  have hwsol := state_solves A B hA hB b hw
  have hleft : response A B b z =
      star (state A B b w) ⬝ᵥ (A - star w • B).mulVec (state A B b z) := by
    calc
      _ = star ((A - w • B).mulVec (state A B b w)) ⬝ᵥ state A B b z := by
        rw [hwsol]; rfl
      _ = _ := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
          Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hA.eq, hB.isHermitian.eq]
  have hright : star (response A B b w) =
      star (state A B b w) ⬝ᵥ (A - z • B).mulVec (state A B b z) := by
    rw [hzsol]
    exact (star_dotProduct _ _).symm
  rw [hleft, hright]
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul]
  ring

/-- The full response kernel on any finite set of points in the upper half-plane. -/
noncomputable def responseKernel {κ : Type*} (A B : Matrix ι ι ℂ) (b : ι → ℂ)
    (z : κ → ℂ) : Matrix κ κ ℂ := fun i j =>
  (response A B b (z j) - star (response A B b (z i))) / (z j - star (z i))

theorem responseKernel_gram {κ : Type*} [Fintype κ]
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.PosDef)
    (b : ι → ℂ) (z : κ → ℂ) (hz : ∀ i, 0 < (z i).im) :
    responseKernel A B b z =
      (Matrix.of fun k i => state A B b (z i) k)ᴴ * B *
        (Matrix.of fun k i => state A B b (z i) k) := by
  ext i j
  have hne : z j - star (z i) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at hi
    linarith [hz i, hz j]
  rw [responseKernel, response_difference A B hA hB b (hz j).ne' (hz i).ne',
    mul_div_cancel_left₀ _ hne, Matrix.dotProduct_mulVec]
  rfl

theorem responseKernel_posSemidef {κ : Type*} [Fintype κ]
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.PosDef)
    (b : ι → ℂ) (z : κ → ℂ) (hz : ∀ i, 0 < (z i).im) :
    (responseKernel A B b z).PosSemidef := by
  rw [responseKernel_gram A B hA hB b z hz]
  exact hB.posSemidef.conjTranspose_mul_mul_same _

/-- Positivity passes to a finite scalar limit, with dimensions allowed to vary. -/
theorem limit_im_nonneg {κ : ℕ → Type*} [∀ n, Fintype (κ n)]
    [∀ n, DecidableEq (κ n)] (A B : (n : ℕ) → Matrix (κ n) (κ n) ℂ)
    (hA : ∀ n, (A n).IsHermitian) (hB : ∀ n, (B n).PosDef)
    (b : (n : ℕ) → κ n → ℂ) {z L : ℂ} (hz : 0 < z.im)
    (hlim : Tendsto (fun n => response (A n) (B n) (b n) z) atTop (𝓝 L)) :
    0 ≤ L.im := by
  exact ge_of_tendsto (Complex.continuous_im.tendsto L |>.comp hlim)
    (Filter.Eventually.of_forall (fun n => response_im_nonneg _ _ (hA n) (hB n) _ hz))

end CriticalLinePhasor.Pencil3D.Green

#print axioms CriticalLinePhasor.Pencil3D.eigenvalue_real_of_mass_pos
#print axioms CriticalLinePhasor.Pencil3D.pencil_pairing_im
#print axioms CriticalLinePhasor.Pencil3D.Green.pencil_det_ne_zero
#print axioms CriticalLinePhasor.Pencil3D.Green.response_im
#print axioms CriticalLinePhasor.Pencil3D.Green.response_im_pos
#print axioms CriticalLinePhasor.Pencil3D.Green.carrier_response
#print axioms CriticalLinePhasor.Pencil3D.Green.response_difference
#print axioms CriticalLinePhasor.Pencil3D.Green.responseKernel_posSemidef
#print axioms CriticalLinePhasor.Pencil3D.Green.limit_im_nonneg
