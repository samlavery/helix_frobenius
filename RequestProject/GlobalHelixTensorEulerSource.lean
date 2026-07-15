import RequestProject.GlobalHelixClebschGordanBank
import RequestProject.GlobalHelixCoefficientFiber
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Roots

/-!
# The tensor Euler bank as a 3D helix source

The local tensor coefficients are defined before taking any one-dimensional analytic readout.
Their source point is the three-coordinate fiber

`(‖aₙ‖, arg aₙ, log (qⁿ x))`.

The first two coordinates reconstruct the complete-homogeneous Euler coefficient, and the third
reconstructs its multiplicative height.  The Clebsch--Gordan splitting is then proved first for the
finite local polynomial, transported to its formal reciprocal series, and finally read coefficient
by coefficient as the exact antidiagonal convolution.
-/

open Complex Finset
open scoped BigOperators

namespace CriticalLinePhasor.GlobalHelix

open ConeProjection

/-- The finite local Euler numerator as an actual polynomial. -/
noncomputable def localEulerPolynomial {ι : Type*} [Fintype ι]
    (W : FiniteWeightFiber ι) : Polynomial ℂ :=
  ∏ i, (1 - Polynomial.C (W.weight i) * Polynomial.X)

/-- Evaluating the polynomial recovers the local numerator already stored in the weight fiber. -/
theorem localEulerPolynomial_eval {ι : Type*} [Fintype ι]
    (W : FiniteWeightFiber ι) (X : ℂ) :
    Polynomial.eval X (localEulerPolynomial W) = W.localPoly X := by
  unfold localEulerPolynomial FiniteWeightFiber.localPoly
  change (Polynomial.evalRingHom X)
      (∏ i, (1 - Polynomial.C (W.weight i) * Polynomial.X)) =
    ∏ i, (1 - W.weight i * X)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp

/-- The twisted Clebsch--Gordan identity lifted from pointwise local factors to polynomials. -/
theorem tensorSymTwist_localEulerPolynomial_eq_mul
    {κ : Type*} [Fintype κ] {r : ℕ} (hr : 2 ≤ r)
    (α : ℂ) (hα : ‖α‖ = 1) (Wτ : FiniteWeightFiber κ) :
    localEulerPolynomial
      (FiniteWeightFiber.tensorFiber
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.symFiber 1 α hα)
          (FiniteWeightFiber.symFiber (r - 1) α hα)) Wτ) =
      localEulerPolynomial
        (FiniteWeightFiber.tensorFiber (FiniteWeightFiber.symFiber r α hα) Wτ) *
      localEulerPolynomial
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.symFiber (r - 2) α hα) Wτ) := by
  apply Polynomial.funext
  intro X
  rw [Polynomial.eval_mul]
  simp only [localEulerPolynomial_eval]
  exact tensorSymTwist_localPoly_eq_mul hr α hα Wτ X

/-- The formal local Euler factor, defined as the reciprocal of the polynomial numerator. -/
noncomputable def localEulerSeries {ι : Type*} [Fintype ι]
    (W : FiniteWeightFiber ι) : PowerSeries ℂ :=
  ((localEulerPolynomial W : Polynomial ℂ) : PowerSeries ℂ)⁻¹

/-- The `n`th coefficient of the formal local Euler factor. -/
noncomputable def localEulerCoeff {ι : Type*} [Fintype ι]
    (W : FiniteWeightFiber ι) (n : ℕ) : ℂ :=
  PowerSeries.coeff n (localEulerSeries W)

/-- The twisted Clebsch--Gordan identity for the complete formal Euler series. -/
theorem tensorSymTwist_localEulerSeries_eq_mul
    {κ : Type*} [Fintype κ] {r : ℕ} (hr : 2 ≤ r)
    (α : ℂ) (hα : ‖α‖ = 1) (Wτ : FiniteWeightFiber κ) :
    localEulerSeries
      (FiniteWeightFiber.tensorFiber
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.symFiber 1 α hα)
          (FiniteWeightFiber.symFiber (r - 1) α hα)) Wτ) =
      localEulerSeries
        (FiniteWeightFiber.tensorFiber (FiniteWeightFiber.symFiber r α hα) Wτ) *
      localEulerSeries
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.symFiber (r - 2) α hα) Wτ) := by
  unfold localEulerSeries
  rw [tensorSymTwist_localEulerPolynomial_eq_mul hr α hα Wτ]
  rw [Polynomial.coe_mul, PowerSeries.mul_inv_rev]
  ring

/-- Coefficient-level Clebsch--Gordan splitting: the tensor-step coefficient is the exact
antidiagonal convolution of the `Sym^r` and `Sym^(r-2)` twisted coefficients. -/
theorem tensorSymTwist_localEulerCoeff_eq_antidiagonal
    {κ : Type*} [Fintype κ] {r : ℕ} (hr : 2 ≤ r)
    (α : ℂ) (hα : ‖α‖ = 1) (Wτ : FiniteWeightFiber κ) (n : ℕ) :
    localEulerCoeff
      (FiniteWeightFiber.tensorFiber
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.symFiber 1 α hα)
          (FiniteWeightFiber.symFiber (r - 1) α hα)) Wτ) n =
      ∑ p ∈ Finset.antidiagonal n,
        localEulerCoeff
          (FiniteWeightFiber.tensorFiber (FiniteWeightFiber.symFiber r α hα) Wτ) p.1 *
        localEulerCoeff
          (FiniteWeightFiber.tensorFiber
            (FiniteWeightFiber.symFiber (r - 2) α hα) Wτ) p.2 := by
  unfold localEulerCoeff
  rw [tensorSymTwist_localEulerSeries_eq_mul hr α hα Wτ]
  exact PowerSeries.coeff_mul n _ _

/-- The primary 3D source point for the `n`th local tensor-Euler coefficient at residue scale `q`. -/
noncomputable def tensorEulerCoefficientFiber {ι : Type*} [Fintype ι]
    (W : FiniteWeightFiber ι) (q : ℝ) (n : ℕ) (x : ℝ) : Fiber :=
  (‖localEulerCoeff W n‖, Complex.arg (localEulerCoeff W n),
    Real.log (q ^ n * x))

/-- The radial/phase coordinates of the 3D source reconstruct the Euler coefficient exactly. -/
theorem fiberPhasor_tensorEulerCoefficientFiber {ι : Type*} [Fintype ι]
    (W : FiniteWeightFiber ι) (q : ℝ) (n : ℕ) (x : ℝ) :
    fiberPhasor (tensorEulerCoefficientFiber W q n x) = localEulerCoeff W n := by
  simpa [fiberPhasor, tensorEulerCoefficientFiber, radial,
    phase, mul_comm] using
    Complex.norm_mul_exp_arg_mul_I (localEulerCoeff W n)

/-- The height coordinate of the 3D source reconstructs the prime-power scale `qⁿx`. -/
theorem multiplicativeHeight_tensorEulerCoefficientFiber
    {ι : Type*} [Fintype ι] (W : FiniteWeightFiber ι)
    {q : ℝ} (hq : 0 < q) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    multiplicativeHeight (tensorEulerCoefficientFiber W q n x) = q ^ n * x := by
  unfold multiplicativeHeight heightEncode tensorEulerCoefficientFiber height
  rw [Real.exp_log]
  positivity

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.localEulerPolynomial_eval
#print axioms CriticalLinePhasor.GlobalHelix.tensorSymTwist_localEulerPolynomial_eq_mul
#print axioms CriticalLinePhasor.GlobalHelix.tensorSymTwist_localEulerSeries_eq_mul
#print axioms CriticalLinePhasor.GlobalHelix.tensorSymTwist_localEulerCoeff_eq_antidiagonal
#print axioms CriticalLinePhasor.GlobalHelix.fiberPhasor_tensorEulerCoefficientFiber
#print axioms CriticalLinePhasor.GlobalHelix.multiplicativeHeight_tensorEulerCoefficientFiber
