import RequestProject.WeilDuality
import Mathlib.Analysis.SpecificLimits.Normed

/-!
The tensor-power argument with a polynomial prefactor, retaining jet multiplicity.

Unfolded target: if B > 0 and |alpha|^(2k) <= C (1+k^p) B^k for all natural k,
then |alpha|^2 <= B. A nilpotent jet contribution can therefore be retained.
DC is k=0; the exponential scale is B, and the polynomial factor records the
finite Taylor shift. The proof divides by |alpha|^(2k) and uses geometric decay.

Searches: `rg -n 'polynomial.*purity|purity.*polynomial|polynomial.*cup|cup.*polynomial'
RequestProject .lake/packages/mathlib/Mathlib`; `rg -n 'HasEigenvector.*pow|
HasEigenvalue.*pow|pow_apply.*eigen|apply_pow.*eigen|mem_eigenspace.*pow'
.lake/packages/mathlib/Mathlib/LinearAlgebra/Eigenspace`.
Strategies: divide by the excessive eigenvalue power; alternatively bound the
polynomial by each slightly larger exponential scale. The first is implemented.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.WeilDuality

theorem tensor_power_purity_of_polynomial {α : ℂ} {B C : ℝ} (hB : 0 < B) (p : ℕ)
    (h : ∀ k : ℕ, ‖α‖ ^ (2 * k) ≤ C * (1 + (k : ℝ) ^ p) * B ^ k) :
    ‖α‖ ^ 2 ≤ B := by
  by_contra hgt
  have hα : B < ‖α‖ ^ 2 := lt_of_not_ge hgt
  have hα0 : 0 < ‖α‖ ^ 2 := hB.trans hα
  have hr0 : 0 ≤ B / ‖α‖ ^ 2 := div_nonneg hB.le hα0.le
  have hr1 : B / ‖α‖ ^ 2 < 1 := (div_lt_one hα0).mpr hα
  have hlim : Tendsto (fun k : ℕ => C * (1 + (k : ℝ) ^ p) * (B / ‖α‖ ^ 2) ^ k)
      atTop (𝓝 0) := by
    have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hp := tendsto_pow_const_mul_const_pow_of_lt_one p hr0 hr1
    convert (h0.add hp).const_mul C using 1 <;> simp [mul_add, add_mul, mul_assoc]
  have hge (k : ℕ) : 1 ≤ C * (1 + (k : ℝ) ^ p) * (B / ‖α‖ ^ 2) ^ k := by
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hα0 k), one_mul]
    simpa only [pow_mul] using h k
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim (Filter.Eventually.of_forall hge)
  norm_num at hbad

/-- A polynomial prefactor in the actual transport norm suffices on an eigenvector. -/
theorem cup_polynomial_growth_gives_purity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →ₗ[ℂ] E) {α : ℂ} {v : E} (hv0 : v ≠ 0) (hev : T v = α • v)
    {B C : ℝ} (hB : 0 < B) (p : ℕ)
    (hgrow : ∀ k : ℕ, ‖(T ^ k) v‖ ^ 2 ≤ C * (1 + (k : ℝ) ^ p) * B ^ k * ‖v‖ ^ 2) :
    ‖α‖ ^ 2 ≤ B := by
  apply tensor_power_purity_of_polynomial (C := C) hB p
  intro k
  have hv : Module.End.HasEigenvector T α v := ⟨Module.End.mem_eigenspace_iff.mpr hev, hv0⟩
  have h := hgrow k
  rw [hv.pow_apply k, norm_smul, norm_pow, mul_pow, ← pow_mul, mul_comm k 2] at h
  exact le_of_mul_le_mul_right h (sq_pos_of_pos (norm_pos_iff.mpr hv0))

/-- Duality closes purity with polynomial growth allowed on both strands. -/
theorem purity_from_polynomial_castelnuovo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →ₗ[ℂ] E) {α β : ℂ} {v w : E} (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (hev : T v = α • v) (hew : T w = β • w)
    {B Cα Cβ : ℝ} (hB : 0 < B) (pα pβ : ℕ) (hdet : α * β = (B : ℂ))
    (hgrowα : ∀ k : ℕ,
      ‖(T ^ k) v‖ ^ 2 ≤ Cα * (1 + (k : ℝ) ^ pα) * B ^ k * ‖v‖ ^ 2)
    (hgrowβ : ∀ k : ℕ,
      ‖(T ^ k) w‖ ^ 2 ≤ Cβ * (1 + (k : ℝ) ^ pβ) * B ^ k * ‖w‖ ^ 2) :
    ‖α‖ = Real.sqrt B ∧ ‖β‖ = Real.sqrt B := by
  obtain ⟨hα, hβ⟩ := duality_forces_purity hB hdet
    (cup_polynomial_growth_gives_purity T hv0 hev hB pα hgrowα)
    (cup_polynomial_growth_gives_purity T hw0 hew hB pβ hgrowβ)
  constructor
  · rw [← hα, Real.sqrt_sq (norm_nonneg α)]
  · rw [← hβ, Real.sqrt_sq (norm_nonneg β)]

#print axioms tensor_power_purity_of_polynomial
#print axioms cup_polynomial_growth_gives_purity
#print axioms purity_from_polynomial_castelnuovo

end CriticalLinePhasor.WeilDuality
