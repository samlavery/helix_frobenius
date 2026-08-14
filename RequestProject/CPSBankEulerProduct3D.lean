import RequestProject.CPSLocalEulerSum3D
import RequestProject.CPSEdgeProductAssembly3D
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# The Euler product for a tempered bank

Assembly of the identification `LSeries A = bankEulerReadout w` on the readout half-plane, from
three compiled pieces:

* the local sum `∑' e, h_e(w p) z ^ e = ∏ i (1 - z · w p i)⁻¹`  (`CPSLocalEulerSum3D`);
* absolute convergence of the bank series there  (`CPSTemperedBankAbscissa3D`);
* the primewise summability of the Euler logarithms  (`summable_bank_neg_log`).

Mathlib's `IsMultiplicative.eulerProduct_hasProd` turns the first two into a `HasProd` over primes
with value `LSeries A s`; `HasSum.cexp` turns the third into a `HasProd` with value
`bankEulerReadout w s`; the two families agree factor by factor because `exp (∑ -log u) = ∏ u⁻¹`.
Uniqueness of `HasProd` closes it.

Two consequences drop out for free and are recorded: the bank series **never vanishes** on the
readout half-plane (an exponential does not vanish), and therefore the tower's entire continuation
does not vanish there either once it has been descended (`CPSContinuationDescent3D`).  Nothing in
this file is an estimate; the abscissa is a chart datum for the projected series, not a gate on the
carrier.
-/

open Complex

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.CarrierTheta

/-- `n ↦ n ^ (-s)` as an arithmetic function. -/
noncomputable def cpowArith {s : ℂ} (hs : s ≠ 0) : ArithmeticFunction ℂ where
  toFun n := (n : ℂ) ^ (-s)
  map_zero' := by
    simp only [Nat.cast_zero]
    exact Complex.zero_cpow (neg_ne_zero.mpr hs)

@[simp] theorem cpowArith_apply {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    cpowArith hs n = (n : ℂ) ^ (-s) := rfl

theorem isMultiplicative_cpowArith {s : ℂ} (hs : s ≠ 0) :
    (cpowArith hs).IsMultiplicative := by
  constructor
  · simp [cpowArith_apply]
  · intro m n _
    have h := map_mul (riemannZetaSummandHom (s := s) hs) m n
    simp only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk] at h
    simpa [cpowArith_apply] using h

/-- The summand of the bank Dirichlet series, as an arithmetic function. -/
noncomputable def bankSummand {ι : Type*} [Fintype ι] (w : Nat.Primes → ι → ℂ)
    {s : ℂ} (hs : s ≠ 0) : ArithmeticFunction ℂ :=
  (coefficientArithmetic (radialGlobalSatakeCoeff w)).pmul (cpowArith hs)

theorem bankSummand_apply {ι : Type*} [Fintype ι] (w : Nat.Primes → ι → ℂ)
    {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    bankSummand w hs n =
      coefficientArithmetic (radialGlobalSatakeCoeff w) n * (n : ℂ) ^ (-s) := rfl

theorem isMultiplicative_bankSummand {ι : Type*} [Fintype ι] (w : Nat.Primes → ι → ℂ)
    {s : ℂ} (hs : s ≠ 0) : (bankSummand w hs).IsMultiplicative :=
  (CriticalLinePhasor.TransportClosure.isMultiplicative_bankArithmetic w).pmul
    (isMultiplicative_cpowArith hs)

/-- The summand is exactly the `LSeries` term. -/
theorem bankSummand_eq_term {ι : Type*} [Fintype ι] (w : Nat.Primes → ι → ℂ)
    {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    bankSummand w hs n =
      LSeries.term (⇑(coefficientArithmetic (radialGlobalSatakeCoeff w))) s n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [bankSummand_apply, LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

/-- At a prime, the local Euler factor is the reciprocal Satake polynomial. -/
theorem tsum_bankSummand_prime_pow {ι : Type*} [Fintype ι] (w : Nat.Primes → ι → ℂ)
    (hw : ∀ p i, ‖w p i‖ = 1) {s : ℂ} (hs : 1 < s.re) (hs0 : s ≠ 0) (p : Nat.Primes) :
    (∑' e : ℕ, bankSummand w hs0 ((p : ℕ) ^ e)) =
      ∏ i, (1 - (p : ℂ) ^ (-s) * w p i)⁻¹ := by
  have hznorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_natCast_cpow_of_re_ne_zero _ (re_neg_ne_zero_of_one_lt_re hs)]
    refine Real.rpow_lt_one_of_one_lt_of_neg ?_ ?_
    · exact_mod_cast p.2.one_lt
    · simp only [Complex.neg_re]
      linarith
  have hterm : ∀ e : ℕ, bankSummand w hs0 ((p : ℕ) ^ e) =
      radialLocalEulerCoeff (w p) e * ((p : ℂ) ^ (-s)) ^ e := by
    intro e
    have h1 : coefficientArithmetic (radialGlobalSatakeCoeff w) ((p : ℕ) ^ e) =
        radialLocalEulerCoeff (w p) e :=
      CriticalLinePhasor.TransportClosure.bankArithmetic_prime_pow w p.2 e
    have h2 : ((((p : ℕ) ^ e : ℕ)) : ℂ) ^ (-s) = ((p : ℂ) ^ (-s)) ^ e := by
      have h := map_pow (riemannZetaSummandHom (s := s) hs0) ((p : ℕ)) e
      simp only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk] at h
      exact_mod_cast h
    rw [bankSummand_apply, h1, h2]
  rw [tsum_congr hterm]
  rw [localEuler_tsum_fintype (w p) (fun i => le_of_eq (hw p i)) hznorm]
  exact Finset.prod_congr rfl fun i _ => by rw [mul_comm]

/-- **The Euler product for a tempered bank.**  On the readout half-plane the bank Dirichlet
series is the exponential of the primewise Euler logarithm. -/
theorem LSeries_bankArithmetic_eq_bankEulerReadout {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) (hw : ∀ p i, ‖w p i‖ = 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (⇑(coefficientArithmetic (radialGlobalSatakeCoeff w))) s =
      bankEulerReadout w s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp only [Complex.zero_re] at hs
    linarith
  -- the Euler product side
  have hsum : Summable (‖bankSummand w hs0 ·‖) := by
    have := (bankArithmetic_LSeriesSummable_of_tempered w hw hs).norm
    refine this.congr fun n => ?_
    rw [bankSummand_eq_term]
  have hEuler := (isMultiplicative_bankSummand w hs0).eulerProduct_hasProd hsum
  -- the exponential side
  have hlogsum : Summable fun p : Nat.Primes =>
      ∑ i, -Complex.log (1 - (p : ℂ) ^ (-s) * w p i) := summable_bank_neg_log hw hs
  have hExp := hlogsum.hasSum.cexp
  -- the two families agree
  have hfam : ∀ p : Nat.Primes,
      (∑' e : ℕ, bankSummand w hs0 ((p : ℕ) ^ e)) =
        (Complex.exp ∘ fun p : Nat.Primes =>
          ∑ i, -Complex.log (1 - (p : ℂ) ^ (-s) * w p i)) p := by
    intro p
    have hznorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_natCast_cpow_of_re_ne_zero _ (re_neg_ne_zero_of_one_lt_re hs)]
      refine Real.rpow_lt_one_of_one_lt_of_neg ?_ ?_
      · exact_mod_cast p.2.one_lt
      · simp only [Complex.neg_re]
        linarith
    have hne : ∀ i, (1 : ℂ) - (p : ℂ) ^ (-s) * w p i ≠ 0 := by
      intro i hzero
      have : (p : ℂ) ^ (-s) * w p i = 1 := by
        have := sub_eq_zero.mp hzero
        exact this.symm
      have hnorm : ‖(p : ℂ) ^ (-s) * w p i‖ = 1 := by rw [this, norm_one]
      rw [norm_mul, hw p i, mul_one] at hnorm
      rw [hnorm] at hznorm
      exact lt_irrefl 1 hznorm
    rw [tsum_bankSummand_prime_pow w hw hs hs0 p]
    simp only [Function.comp_apply, Complex.exp_sum]
    exact Finset.prod_congr rfl fun i _ => by
      rw [Complex.exp_neg, Complex.exp_log (hne i)]
  -- conclude by uniqueness of the product
  have hEuler' : HasProd (Complex.exp ∘ fun p : Nat.Primes =>
      ∑ i, -Complex.log (1 - (p : ℂ) ^ (-s) * w p i))
      (∑' n, bankSummand w hs0 n) := by
    refine (hEuler.congr_fun ?_)
    intro p
    exact (hfam p).symm
  have hval := hEuler'.unique hExp
  have hgoal : bankEulerReadout w s =
      Complex.exp (∑' p : Nat.Primes,
        ∑ i, -Complex.log (1 - (p : ℂ) ^ (-s) * w p i)) := rfl
  rw [hgoal, ← hval]
  exact tsum_congr fun n => (bankSummand_eq_term w hs0 n).symm

/-- The bank Dirichlet series does not vanish on the readout half-plane: it is an exponential. -/
theorem LSeries_bankArithmetic_ne_zero {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) (hw : ∀ p i, ‖w p i‖ = 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (⇑(coefficientArithmetic (radialGlobalSatakeCoeff w))) s ≠ 0 := by
  rw [LSeries_bankArithmetic_eq_bankEulerReadout w hw hs]
  exact Complex.exp_ne_zero _

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.tsum_bankSummand_prime_pow
#print axioms CriticalLinePhasor.ThreeDConverse.LSeries_bankArithmetic_eq_bankEulerReadout
#print axioms CriticalLinePhasor.ThreeDConverse.LSeries_bankArithmetic_ne_zero
