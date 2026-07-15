import RequestProject.GlobalHelixTensorEulerSource
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Polynomial bounds for the local tensor-Euler fibers

Before a scalar Mellin readout, the local Euler coefficient is the radial/phase projection of a
finite product of geometric power-series fibers.  Expanding that product over the finite-support
antidiagonal shows that the coefficient is a sum of unit-norm phases.  Its norm is therefore at
most a multichoose number, hence at most a fixed power of the exponent height.
-/

open Complex Finset
open scoped BigOperators

namespace CriticalLinePhasor.GlobalHelix

/-- The one-channel formal geometric series with phase step `w`. -/
noncomputable def geometricPowerSeries (w : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => w ^ n)

@[simp] theorem coeff_geometricPowerSeries (w : ℂ) (n : ℕ) :
    PowerSeries.coeff n (geometricPowerSeries w) = w ^ n := by
  simp [geometricPowerSeries]

/-- One channel of the local Euler numerator cancels its geometric-series fiber. -/
theorem geometricPowerSeries_mul_one_sub_C_mul_X (w : ℂ) :
    geometricPowerSeries w * (1 - PowerSeries.C w * PowerSeries.X) = 1 := by
  have h := congrArg (PowerSeries.rescale w)
    (PowerSeries.mk_one_mul_one_sub_eq_one ℂ)
  simpa [geometricPowerSeries, PowerSeries.rescale_mk,
    PowerSeries.rescale_X] using h

theorem one_sub_C_mul_X_inv_eq_geometricPowerSeries (w : ℂ) :
    (1 - PowerSeries.C w * PowerSeries.X)⁻¹ = geometricPowerSeries w := by
  apply (PowerSeries.inv_eq_iff_mul_eq_one (φ := geometricPowerSeries w) (by simp)).2
  exact geometricPowerSeries_mul_one_sub_C_mul_X w

@[simp] theorem polynomialEulerFactor_coe (w : ℂ) :
    (((1 - Polynomial.C w * Polynomial.X : Polynomial ℂ) : PowerSeries ℂ)) =
      1 - PowerSeries.C w * PowerSeries.X := by
  simp

/-- The full local Euler series is the product of its one-channel geometric series. -/
theorem localEulerSeries_eq_prod_geometric {ι : Type*} [Fintype ι]
    (W : FiniteWeightFiber ι) :
    localEulerSeries W = ∏ i, geometricPowerSeries (W.weight i) := by
  unfold localEulerSeries
  apply (PowerSeries.inv_eq_iff_mul_eq_one
    (φ := ∏ i, geometricPowerSeries (W.weight i)) (by
      rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero]
      unfold localEulerPolynomial
      change (Polynomial.evalRingHom 0)
        (∏ i, (1 - Polynomial.C (W.weight i) * Polynomial.X)) ≠ 0
      rw [map_prod]
      simp)).2
  rw [show (((localEulerPolynomial W : Polynomial ℂ) : PowerSeries ℂ)) =
      ∏ i, (1 - PowerSeries.C (W.weight i) * PowerSeries.X) by
    unfold localEulerPolynomial
    change Polynomial.coeToPowerSeries.ringHom
      (∏ i, (1 - Polynomial.C (W.weight i) * Polynomial.X)) = _
    rw [map_prod]
    simp]
  rw [← Finset.prod_mul_distrib]
  simp [geometricPowerSeries_mul_one_sub_C_mul_X]

/-- Exact finite-support expansion of a local Euler coefficient. -/
theorem localEulerCoeff_eq_finsuppAntidiag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : FiniteWeightFiber ι) (n : ℕ) :
    localEulerCoeff W n =
      ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) n,
        ∏ i, W.weight i ^ l i := by
  classical
  unfold localEulerCoeff
  rw [localEulerSeries_eq_prod_geometric W]
  simpa using
    (PowerSeries.coeff_prod
      (fun i => geometricPowerSeries (W.weight i)) n (Finset.univ : Finset ι))

/-- Triangle inequality after the 3D radial/phase fibers are expanded. -/
theorem norm_localEulerCoeff_le_card_finsuppAntidiag
    {ι : Type*} [Fintype ι] [DecidableEq ι] (W : FiniteWeightFiber ι) (n : ℕ) :
    ‖localEulerCoeff W n‖ ≤
      #(Finset.finsuppAntidiag (Finset.univ : Finset ι) n) := by
  classical
  rw [localEulerCoeff_eq_finsuppAntidiag]
  calc
    ‖∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) n,
        ∏ i, W.weight i ^ l i‖
        ≤ ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) n,
            ‖∏ i, W.weight i ^ l i‖ := norm_sum_le _ _
    _ = ∑ _l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) n, 1 := by
      apply Finset.sum_congr rfl
      intro l hl
      simp [norm_prod, W.unit]
    _ = #(Finset.finsuppAntidiag (Finset.univ : Finset ι) n) := by simp

theorem norm_localEulerCoeff_le_multichoose
    {ι : Type*} [Fintype ι] [DecidableEq ι] (W : FiniteWeightFiber ι) (n : ℕ) :
    ‖localEulerCoeff W n‖ ≤ (Fintype.card ι).multichoose n := by
  classical
  simpa [Finset.card_finsuppAntidiag_nat_eq_multichoose] using
    norm_localEulerCoeff_le_card_finsuppAntidiag W n

/-- A uniform polynomial majorant for multichoose numbers. -/
theorem multichoose_le_add_one_pow (d n : ℕ) :
    d.multichoose n ≤ (n + 1) ^ d := by
  cases d with
  | zero =>
      cases n <;> simp
  | succ k =>
      calc
        (k + 1).multichoose n = (n + k).choose k := by
          rw [Nat.multichoose_eq]
          have hsub : k + 1 + n - 1 = n + k := by omega
          rw [hsub]
          exact Nat.choose_symm_add
        _ ≤ (n + 1) ^ k := Nat.choose_add_le_add_one_pow n k
        _ ≤ (n + 1) ^ (k + 1) := by
          exact Nat.pow_le_pow_right (by omega) (Nat.le_succ k)

/-- Polynomial growth of every local tensor-Euler coefficient. -/
theorem norm_localEulerCoeff_le_add_one_pow
    {ι : Type*} [Fintype ι] (W : FiniteWeightFiber ι) (n : ℕ) :
    ‖localEulerCoeff W n‖ ≤ ((n + 1) ^ Fintype.card ι : ℕ) := by
  classical
  calc
    ‖localEulerCoeff W n‖ ≤ ((Fintype.card ι).multichoose n : ℕ) :=
      norm_localEulerCoeff_le_multichoose W n
    _ ≤ ((n + 1) ^ Fintype.card ι : ℕ) := by
      exact_mod_cast multichoose_le_add_one_pow (Fintype.card ι) n

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.geometricPowerSeries_mul_one_sub_C_mul_X
#print axioms CriticalLinePhasor.GlobalHelix.localEulerSeries_eq_prod_geometric
#print axioms CriticalLinePhasor.GlobalHelix.localEulerCoeff_eq_finsuppAntidiag
#print axioms CriticalLinePhasor.GlobalHelix.norm_localEulerCoeff_le_add_one_pow
