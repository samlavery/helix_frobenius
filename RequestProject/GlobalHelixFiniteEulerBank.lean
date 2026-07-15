import RequestProject.GlobalHelixTensorEulerSource
import Mathlib.Data.Nat.Factorization.Defs

/-!
# Finite global tensor-Euler banks on the 3D helix

A finite set of places is assembled in its native exponent-vector coordinates.  The coefficient
is the product of the local formal Euler coefficients and its height is the product of the local
prime-power heights.  Both are stored directly in a single 3D helix fiber.  Natural-number
factorization is provided only as a later arithmetic projection of this source.
-/

open Complex Finset
open scoped BigOperators

namespace CriticalLinePhasor.GlobalHelix

open ConeProjection

/-- The coefficient at a finite-place exponent vector. -/
noncomputable def finiteEulerCoeff
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (k : V → ℕ) : ℂ :=
  ∏ v ∈ S, localEulerCoeff (W v) (k v)

/-- The natural-number projection obtained by reading the exponent of each labelled prime. -/
noncomputable def arithmeticEulerCoeff
    {V ι : Type*} [Fintype V] [Fintype ι]
    (p : V → ℕ) (W : V → FiniteWeightFiber ι) (n : ℕ) : ℂ :=
  ∏ v, localEulerCoeff (W v) (n.factorization (p v))

/-- Multiplicative height of a finite-place exponent vector. -/
noncomputable def finiteEulerHeight
    {V : Type*} (S : Finset V) (q : V → ℝ) (k : V → ℕ) : ℝ :=
  ∏ v ∈ S, q v ^ k v

/-- The primary 3D global source point for a finite Euler coefficient. -/
noncomputable def finiteTensorEulerCoefficientFiber
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (k : V → ℕ) (x : ℝ) : Fiber :=
  (‖finiteEulerCoeff S W k‖, Complex.arg (finiteEulerCoeff S W k),
    Real.log (finiteEulerHeight S q k * x))

/-- The first two coordinates reconstruct the finite Euler coefficient exactly. -/
theorem fiberPhasor_finiteTensorEulerCoefficientFiber
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (k : V → ℕ) (x : ℝ) :
    fiberPhasor (finiteTensorEulerCoefficientFiber S W q k x) =
      finiteEulerCoeff S W k := by
  simpa [fiberPhasor, finiteTensorEulerCoefficientFiber, radial,
    phase, mul_comm] using
    Complex.norm_mul_exp_arg_mul_I (finiteEulerCoeff S W k)

/-- Positivity of every residue scale makes the finite Euler height positive. -/
theorem finiteEulerHeight_pos
    {V : Type*} (S : Finset V) (q : V → ℝ)
    (hq : ∀ v ∈ S, 0 < q v) (k : V → ℕ) :
    0 < finiteEulerHeight S q k := by
  unfold finiteEulerHeight
  exact Finset.prod_pos fun v hv => pow_pos (hq v hv) _

/-- The third coordinate reconstructs the full multiplicative prime-power height. -/
theorem multiplicativeHeight_finiteTensorEulerCoefficientFiber
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (hq : ∀ v ∈ S, 0 < q v) (k : V → ℕ) {x : ℝ} (hx : 0 < x) :
    multiplicativeHeight (finiteTensorEulerCoefficientFiber S W q k x) =
      finiteEulerHeight S q k * x := by
  unfold multiplicativeHeight heightEncode finiteTensorEulerCoefficientFiber height
  rw [Real.exp_log]
  exact mul_pos (finiteEulerHeight_pos S q hq k) hx

/-- Placewise coefficient-level Clebsch--Gordan splitting of the finite global bank. -/
theorem finiteTensorSymTwistEulerCoeff_eq_prod_antidiagonal
    {V κ : Type*} [Fintype κ] (S : Finset V)
    {r : ℕ} (hr : 2 ≤ r) (α : V → ℂ) (hα : ∀ v, ‖α v‖ = 1)
    (Wτ : V → FiniteWeightFiber κ) (k : V → ℕ) :
    finiteEulerCoeff S
      (fun v => FiniteWeightFiber.tensorFiber
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.symFiber 1 (α v) (hα v))
          (FiniteWeightFiber.symFiber (r - 1) (α v) (hα v))) (Wτ v)) k =
      ∏ v ∈ S, ∑ p ∈ Finset.antidiagonal (k v),
        localEulerCoeff
          (FiniteWeightFiber.tensorFiber
            (FiniteWeightFiber.symFiber r (α v) (hα v)) (Wτ v)) p.1 *
        localEulerCoeff
          (FiniteWeightFiber.tensorFiber
            (FiniteWeightFiber.symFiber (r - 2) (α v) (hα v)) (Wτ v)) p.2 := by
  unfold finiteEulerCoeff
  apply Finset.prod_congr rfl
  intro v _
  exact tensorSymTwist_localEulerCoeff_eq_antidiagonal
    hr (α v) (hα v) (Wτ v) (k v)

/-- A scalar kernel readout of the 3D finite Euler bank. -/
noncomputable def finiteTensorEulerBankReadout
    {V ι : Type*} [Fintype V] [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' k : V → ℕ,
    fiberPhasor (finiteTensorEulerCoefficientFiber S W q k x) *
      g (multiplicativeHeight (finiteTensorEulerCoefficientFiber S W q k x))

/-- Projection of the 3D bank is exactly the expected coefficient/kernel expansion. -/
theorem finiteTensorEulerBankReadout_eq
    {V ι : Type*} [Fintype V] [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (hq : ∀ v ∈ S, 0 < q v) (g : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    finiteTensorEulerBankReadout S W q g x =
      ∑' k : V → ℕ, finiteEulerCoeff S W k * g (finiteEulerHeight S q k * x) := by
  unfold finiteTensorEulerBankReadout
  apply tsum_congr
  intro k
  rw [fiberPhasor_finiteTensorEulerCoefficientFiber,
    multiplicativeHeight_finiteTensorEulerCoefficientFiber S W q hq k hx]

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.fiberPhasor_finiteTensorEulerCoefficientFiber
#print axioms CriticalLinePhasor.GlobalHelix.finiteEulerHeight_pos
#print axioms CriticalLinePhasor.GlobalHelix.multiplicativeHeight_finiteTensorEulerCoefficientFiber
#print axioms CriticalLinePhasor.GlobalHelix.finiteTensorSymTwistEulerCoeff_eq_prod_antidiagonal
#print axioms CriticalLinePhasor.GlobalHelix.finiteTensorEulerBankReadout_eq
