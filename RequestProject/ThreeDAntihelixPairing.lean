import RequestProject.ThreeDNativeFrobenius

/-!
# Scaled anti-helix exchange and its positive pairing

Unfolded construction: J swaps the two lanes, D(u)=diag(u,u^-1),
R(u)=D(u)J.  For u != 0, R(u)^2=I.  Its invariant metric is
G(u)=I+R(u)* R(u), where * denotes conjugate transpose.
The spatial operator and metric are both tensored with I_3.

What would I do without a prior expectation? Average a positive metric
over the order-two exchange, then explicitly check the product of the
unscaled and scaled exchanges in the SAME metric.
Two decompositions: direct lane entries (`ext i j`), and the involution
identity (`rw [Matrix.mul_add, Matrix.add_mul]`).

Search commands (both RequestProject and .lake/packages/mathlib/Mathlib):
`rg -n -i 'rosati|reversor|reversible|involution.*(metric|posDef)|
metric.*involution|trace.*(dual|negative)|dual.*trace' --glob '*.lean'`
`rg -n 'PosDef.*add|theorem add|lemma add|conjTranspose_mul_self'
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean`
LeanSearch: "positive definite matrix plus positive semidefinite matrix
is positive definite"; Loogle: `Matrix.PosDef, HAdd.hAdd`.

The finite-field comparison uses the positive Rosati trace form and the
weighted adjoint identity separately: J. S. Milne, Abelian Varieties,
Theorem 17.3 and Lemma 19.2, https://www.jmilne.org/math/xnotes/AVs.pdf.
No finite-field theorem is assumed in the constructions below.
-/

open Matrix Complex
open scoped BigOperators Kronecker ComplexOrder

namespace CriticalLinePhasor.Pencil3D

noncomputable def laneSwap : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks 0 1 1 0

theorem laneSwap_sq : laneSwap * laneSwap = 1 := by
  simp [laneSwap, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem laneSwap_isHermitian : laneSwap.IsHermitian := by
  change laneSwapᴴ = laneSwap
  simp [laneSwap, Matrix.fromBlocks_conjTranspose]

theorem laneSwap_diagonal (u v : ℂ) :
    laneSwap * laneDiagonal u v = laneDiagonal v u * laneSwap := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [laneSwap, laneDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

noncomputable def scaledLaneSwap (u : ℂ) :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  laneDiagonal u u⁻¹ * laneSwap

theorem scaledLaneSwap_sq {u : ℂ} (hu : u ≠ 0) :
    scaledLaneSwap u * scaledLaneSwap u = 1 := by
  unfold scaledLaneSwap
  calc
    _ = laneDiagonal u u⁻¹ * (laneSwap * laneDiagonal u u⁻¹) * laneSwap := by
      noncomm_ring
    _ = laneDiagonal u u⁻¹ * (laneDiagonal u⁻¹ u * laneSwap) * laneSwap := by
      rw [laneSwap_diagonal]
    _ = (laneDiagonal u u⁻¹ * laneDiagonal u⁻¹ u) * (laneSwap * laneSwap) := by
      noncomm_ring
    _ = 1 := by rw [← laneDiagonal_mul, laneSwap_sq]; simp [hu, laneDiagonal]

noncomputable def exchangeMetric (u : ℂ) :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  1 + (scaledLaneSwap u)ᴴ * scaledLaneSwap u

theorem exchangeMetric_posDef (u : ℂ) : (exchangeMetric u).PosDef := by
  exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _)

theorem exchangeMetric_preserved {u : ℂ} (hu : u ≠ 0) :
    (scaledLaneSwap u)ᴴ * exchangeMetric u * scaledLaneSwap u = exchangeMetric u := by
  have hR := scaledLaneSwap_sq hu
  have hRt : (scaledLaneSwap u)ᴴ * (scaledLaneSwap u)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hR, Matrix.conjTranspose_one]
  simp only [exchangeMetric, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
  calc
    _ = (scaledLaneSwap u)ᴴ * scaledLaneSwap u +
        ((scaledLaneSwap u)ᴴ * (scaledLaneSwap u)ᴴ) *
          (scaledLaneSwap u * scaledLaneSwap u) := by noncomm_ring
    _ = _ := by rw [hRt, hR]; simp [add_comm]

theorem spatial_exchangeMetric_posDef (u : ℂ) : (spatial (exchangeMetric u)).PosDef :=
  (exchangeMetric_posDef u).kronecker Matrix.PosDef.one

theorem spatial_exchangeMetric_preserved {u : ℂ} (hu : u ≠ 0) :
    (spatial (scaledLaneSwap u))ᴴ * spatial (exchangeMetric u) *
      spatial (scaledLaneSwap u) = spatial (exchangeMetric u) := by
  simp only [spatial, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, exchangeMetric_preserved hu]

theorem exchangeMetric_closed_form (u : ℂ) :
    exchangeMetric u = laneDiagonal (1 + star u⁻¹ * u⁻¹) (1 + star u * u) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [exchangeMetric, scaledLaneSwap, laneSwap, laneDiagonal, Matrix.mul_apply,
      Matrix.conjTranspose_apply]

/-- The two exchanges compose to the full reciprocal carrier, with its radius retained. -/
theorem scaledLaneSwap_mul_laneSwap (u : ℂ) :
    scaledLaneSwap u * laneSwap = laneDiagonal u u⁻¹ := by
  rw [scaledLaneSwap, Matrix.mul_assoc, laneSwap_sq, Matrix.mul_one]

/-- Full carrier transport carries one end's positive metric to the other end's metric. -/
theorem reciprocal_exchangeMetric_transport {u : ℂ} (hu : u ≠ 0) :
    (laneDiagonal u u⁻¹)ᴴ * exchangeMetric u * laneDiagonal u u⁻¹ =
      exchangeMetric u⁻¹ := by
  rw [exchangeMetric_closed_form, exchangeMetric_closed_form]
  simp only [laneDiagonal, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, inv_inv]
  congr 1
  funext i
  cases i <;> simp [star_inv₀, hu, mul_add, add_mul, mul_left_comm, mul_comm, add_comm]

theorem exchangeMetric_trace_inverse (u : ℂ) :
    (exchangeMetric u⁻¹).trace = (exchangeMetric u).trace := by
  simp [exchangeMetric_closed_form, laneDiagonal, Matrix.trace_diagonal,
    Fintype.sum_sum_type, add_comm]

theorem exchangeMetric_trace_pos (u : ℂ) : 0 < (exchangeMetric u).trace.re := by
  have h := (exchangeMetric_posDef u).trace_pos
  exact h.1

/-- The two ends have the same total positive metric weight. -/
theorem reciprocal_exchangeMetric_trace {u : ℂ} (hu : u ≠ 0) :
    ((laneDiagonal u u⁻¹)ᴴ * exchangeMetric u * laneDiagonal u u⁻¹).trace =
      (exchangeMetric u).trace := by
  rw [reciprocal_exchangeMetric_transport hu, exchangeMetric_trace_inverse]

/-- The anti-linear scaled exchange on the two spatial lanes. -/
noncomputable def antihelixConjugate (r : ℝ)
    (v : (Fin 1 ⊕ Fin 1) × Fin 3 → ℂ) : (Fin 1 ⊕ Fin 1) × Fin 3 → ℂ
  | (Sum.inl _, j) => (r : ℂ) * star (v (Sum.inr 0, j))
  | (Sum.inr _, j) => (r : ℂ)⁻¹ * star (v (Sum.inl 0, j))

theorem antihelixConjugate_matrix (r : ℝ) (v : (Fin 1 ⊕ Fin 1) × Fin 3 → ℂ) :
    antihelixConjugate r v = (spatial (scaledLaneSwap r)).mulVec (star v) := by
  ext ⟨i, j⟩
  rcases i with i | i <;> fin_cases i <;> fin_cases j <;>
    simp [antihelixConjugate, spatial, scaledLaneSwap, laneSwap, laneDiagonal,
      Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Fintype.sum_sum_type, Fin.sum_univ_three]

theorem antihelixConjugate_involutive {r : ℝ} (hr : r ≠ 0) :
    Function.Involutive (antihelixConjugate r) := by
  intro v
  ext ⟨i, j⟩
  rcases i with i | i <;> fin_cases i <;>
    simp [antihelixConjugate, hr]

theorem spatial_exchangeMetric_ofReal (r : ℝ) :
    spatial (exchangeMetric r) = Matrix.diagonal
      (fun ij : (Fin 1 ⊕ Fin 1) × Fin 3 =>
        Sum.elim (fun _ => ((1 + r⁻¹ ^ 2 : ℝ) : ℂ))
          (fun _ => ((1 + r ^ 2 : ℝ) : ℂ)) ij.1) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [spatial, exchangeMetric_closed_form, laneDiagonal, Matrix.kroneckerMap_apply, pow_two]

theorem real_diagonal_conjugate_pairing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (v : ι → ℂ) :
    star (star v) ⬝ᵥ (Matrix.diagonal (fun i => (b i : ℂ))).mulVec (star v) =
      star v ⬝ᵥ (Matrix.diagonal (fun i => (b i : ℂ))).mulVec v := by
  simp only [star_star, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem antihelixConjugate_mass {r : ℝ} (hr : r ≠ 0)
    (v : (Fin 1 ⊕ Fin 1) × Fin 3 → ℂ) :
    star (antihelixConjugate r v) ⬝ᵥ
      (spatial (exchangeMetric r)).mulVec (antihelixConjugate r v) =
        star v ⬝ᵥ (spatial (exchangeMetric r)).mulVec v := by
  rw [antihelixConjugate_matrix, ← carrierChange_pairing]
  change star (star v) ⬝ᵥ
    ((spatial (scaledLaneSwap r))ᴴ * spatial (exchangeMetric r) *
      spatial (scaledLaneSwap r)).mulVec (star v) = _
  rw [spatial_exchangeMetric_preserved (by exact_mod_cast hr), spatial_exchangeMetric_ofReal]
  convert real_diagonal_conjugate_pairing
    (fun ij : (Fin 1 ⊕ Fin 1) × Fin 3 =>
      Sum.elim (fun _ => (1 + r⁻¹ ^ 2)) (fun _ => (1 + r ^ 2)) ij.1) v using 1 <;>
    congr 1 <;> ext ⟨i, j⟩ <;> cases i <;> rfl

/-- Adjoint for the bilinear exchange pairing; positivity is checked separately. -/
noncomputable def exchangeAdjoint (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) :=
  laneSwap * A.transpose * laneSwap

theorem exchangeAdjoint_diagonal (u v : ℂ) :
    exchangeAdjoint (laneDiagonal u v) = laneDiagonal v u := by
  have ht : (laneDiagonal u v).transpose = laneDiagonal u v := by simp [laneDiagonal]
  rw [exchangeAdjoint, ht, laneSwap_diagonal, Matrix.mul_assoc, laneSwap_sq, Matrix.mul_one]

/-- The first Laurent difference of the radial transport and its inverse. -/
noncomputable def radialDifference (r : ℝ) :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  laneDiagonal ((r - r⁻¹ : ℝ) : ℂ) (-((r - r⁻¹ : ℝ) : ℂ))

theorem radialDifference_eq_transport_sub_inverse (r : ℝ) :
    radialDifference r = laneDiagonal (r : ℂ) (r : ℂ)⁻¹ -
      laneDiagonal (r : ℂ)⁻¹ (r : ℂ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [radialDifference, laneDiagonal]

/-- Exact 3D trace of the exchange-adjoint square of the first radial difference. -/
theorem radialDifference_exchange_trace (r : ℝ) :
    ((spatial (radialDifference r) *
      spatial (exchangeAdjoint (radialDifference r))).trace).re = -6 * (r - r⁻¹) ^ 2 := by
  unfold radialDifference
  rw [exchangeAdjoint_diagonal]
  simp [spatial, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
    laneDiagonal, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal, Fintype.sum_sum_type]
  ring

/-- The ordinary positive Gram trace of the SAME difference, with the sign explicit. -/
theorem radialDifference_gram_trace (r : ℝ) :
    (((spatial (radialDifference r))ᴴ * spatial (radialDifference r)).trace).re =
      6 * (r - r⁻¹) ^ 2 := by
  simp [spatial, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.trace_kronecker, radialDifference, laneDiagonal, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Fintype.sum_sum_type]
  ring

theorem radius_one_of_exchange_trace_nonneg {r : ℝ} (hr : 0 < r)
    (htrace : 0 ≤ ((spatial (radialDifference r) *
      spatial (exchangeAdjoint (radialDifference r))).trace).re) : r = 1 := by
  rw [radialDifference_exchange_trace] at htrace
  have heq : r - r⁻¹ = 0 := by nlinarith [sq_nonneg (r - r⁻¹)]
  have hi : r = r⁻¹ := sub_eq_zero.mp heq
  have hs : r * r = 1 := by
    calc r * r = r * r⁻¹ := by rw [← hi]
         _ = 1 := mul_inv_cancel₀ hr.ne'
  nlinarith

end CriticalLinePhasor.Pencil3D

#print axioms CriticalLinePhasor.Pencil3D.scaledLaneSwap_sq
#print axioms CriticalLinePhasor.Pencil3D.exchangeMetric_posDef
#print axioms CriticalLinePhasor.Pencil3D.spatial_exchangeMetric_preserved
#print axioms CriticalLinePhasor.Pencil3D.reciprocal_exchangeMetric_transport
#print axioms CriticalLinePhasor.Pencil3D.antihelixConjugate_involutive
#print axioms CriticalLinePhasor.Pencil3D.antihelixConjugate_mass
#print axioms CriticalLinePhasor.Pencil3D.radialDifference_exchange_trace
#print axioms CriticalLinePhasor.Pencil3D.radialDifference_gram_trace
#print axioms CriticalLinePhasor.Pencil3D.radius_one_of_exchange_trace_nonneg
