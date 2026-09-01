import RequestProject.BankNoTransient

/-!
# The centered bank with one clock per prime

`primeToothCenteredTerm` already contains a geometric series over every
positive multiple of its clock length.  Therefore the Euler-compatible bank
uses only the exponent-one tooth `(r, 0)` for each prime position `r`.

Search audit:

```
rg -n -i 'prime(Tooth|Clock)Centered|centered.*prime' \
  RequestProject --glob '*.lean'
rg -n 'hasSum_geometric|tsum_geometric|exp_nat_mul|map_pow' \
  .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n 'LSeries_vonMangoldt|tsum_eq_tsum_primes.*prime_powers' \
  .lake/packages/mathlib/Mathlib RequestProject --glob '*.lean'
rg -n 'vonMangoldt_apply_(pow|prime)|nth_count|count_nth' \
  .lake/packages/mathlib/Mathlib --glob '*.lean'
```
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.BankNoTransient

open CriticalLinePhasor.PrimeClockOrdering

open scoped ArithmeticFunction

/-- The canonical enumeration of primes is an equivalence. -/
noncomputable def toothPrimeEquiv : ℕ ≃ Nat.Primes where
  toFun := toothPrime
  invFun p := Nat.count Nat.Prime p
  left_inv r := by
    exact Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime r
  right_inv p := by
    apply Subtype.ext
    exact Nat.nth_count p.prop

@[simp]
theorem toothPrimeEquiv_apply (r : ℕ) :
    toothPrimeEquiv r = toothPrime r := rfl

/-- Powers of the exponent-one disk point are exactly the prime-power disk
points. -/
theorem primeToothDiskPoint_first_pow
    (α : Nat.Primes → ℂ) (r k : ℕ) (s : ℂ) :
    primeToothDiskPoint α (r, 0) s ^ (k + 1) =
      primeToothDiskPoint α (r, k) s := by
  simp only [primeToothDiskPoint, primeToothFace, primeToothLength,
    toothExponent, zero_add, Nat.cast_one, one_mul, pow_one]
  rw [mul_pow, ← map_pow, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The finite centered bank containing one geometric clock per prime. -/
def primeClockCenteredBank (α : Nat.Primes → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  -∑ r ∈ Finset.range N, primeToothCenteredTerm α (r, 0) s

/-- One prime clock expands into its prime powers, each with the single
von Mangoldt weight `log p`. -/
theorem primeClockCenteredTerm_hasSum_primePowers
    (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    (r : ℕ) {s : ℂ} (hs : s.re < 1 / 2) :
    HasSum
      (fun k : ℕ => ((Real.log (toothPrime r : ℕ) : ℝ) : ℂ) *
        primeToothDiskPoint α (r, k) s)
      (primeToothCenteredTerm α (r, 0) s) := by
  have h := primeToothCenteredTerm_hasSum α hα (r, 0) hs
  have heq :
      (fun k : ℕ => ((Real.log (toothPrime r : ℕ) : ℝ) : ℂ) *
        primeToothDiskPoint α (r, k) s) =
      (fun k : ℕ => ((primeToothLength (r, 0) : ℝ) : ℂ) *
        primeToothDiskPoint α (r, 0) s ^ (k + 1)) := by
    funext k
    rw [primeToothDiskPoint_first_pow]
    simp [primeToothLength, toothExponent]
  rw [heq]
  exact h

/-- In its half-plane of absolute convergence, the von Mangoldt L-series is
the double sum over primes and positive exponents. -/
theorem LSeries_vonMangoldt_eq_tsum_primePowers {u : ℂ}
    (hu : 1 < u.re) :
    LSeries (fun n : ℕ =>
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) u =
      ∑' (p : Nat.Primes) (k : ℕ),
        ((Real.log (p : ℕ) : ℝ) : ℂ) /
          ((((p : ℕ) ^ (k + 1) : ℕ) : ℂ) ^ u) := by
  rw [LSeries_def₀ (by simp)]
  let f : ℕ → ℂ := fun n =>
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) ^ u
  have hsum : Summable f := by
    have h := ArithmeticFunction.LSeriesSummable_vonMangoldt hu
    rw [LSeriesSummable] at h
    refine h.congr ?_
    intro n
    rw [LSeries.term_def₀ (by simp)]
    simp [f, Complex.cpow_neg, div_eq_mul_inv]
  have hsupp : Function.support f ⊆ {n | IsPrimePow n} := by
    intro n hn
    have hΛ : ArithmeticFunction.vonMangoldt n ≠ 0 := by
      intro hz
      exact hn (by simp [f, hz])
    exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
  rw [show (∑' n : ℕ,
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) ^ u) =
      ∑' n : ℕ, f n from rfl]
  rw [tsum_eq_tsum_primes_of_support_subset_prime_powers hsum hsupp]
  apply tsum_congr
  intro p
  apply tsum_congr
  intro k
  simp [f, ArithmeticFunction.vonMangoldt_apply_pow,
    ArithmeticFunction.vonMangoldt_apply_prime p.prop]

/-- A unit-face disk point is the exponential Dirichlet mode at the
reflected parameter `1/2 - s`. -/
theorem primeToothDiskPoint_one_eq_exp (i : PrimeTooth) (s : ℂ) :
    primeToothDiskPoint (fun _ => 1) i s =
      Complex.exp (-((1 / 2 : ℂ) - s) * primeToothLength i) := by
  simp only [primeToothDiskPoint, primeToothFace, one_pow, map_one,
    one_mul, CriticalLinePhasor.HilbertPolya.spectralCoord]
  congr 1
  calc
    Complex.I * (primeToothLength i : ℂ) *
          (-Complex.I * (s - 1 / 2)) =
        -(Complex.I * Complex.I) * (primeToothLength i : ℂ) *
          (s - 1 / 2) := by ring
    _ = -((1 / 2 : ℂ) - s) * primeToothLength i := by
      rw [Complex.I_mul_I]
      ring

/-- The same chart identity in the complex-power form used by L-series. -/
theorem primeToothDiskPoint_one_eq_cpow (i : PrimeTooth) (s : ℂ) :
    primeToothDiskPoint (fun _ => 1) i s =
      ((toothNat i : ℕ) : ℂ) ^ (-((1 / 2 : ℂ) - s)) := by
  rw [primeToothDiskPoint_one_eq_exp]
  rw [primeToothLength_eq_log_toothNat]
  rw [Complex.cpow_def]
  simp only [Nat.cast_eq_zero]
  rw [if_neg (ne_of_gt
    (lt_of_lt_of_le zero_lt_two (toothNat_two_le i)))]
  rw [Complex.natCast_log]
  congr 1
  ring

/-- The reflected von Mangoldt L-series is exactly the infinite
prime-tooth disk readout. -/
theorem LSeries_vonMangoldt_reflected_eq_primeToothDiskPoint {s : ℂ}
    (hs : 1 < ((1 / 2 : ℂ) - s).re) :
    LSeries (fun n : ℕ =>
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        ((1 / 2 : ℂ) - s) =
      ∑' (r : ℕ) (k : ℕ),
        ((Real.log (toothPrime r : ℕ) : ℝ) : ℂ) *
          primeToothDiskPoint (fun _ => 1) (r, k) s := by
  rw [LSeries_vonMangoldt_eq_tsum_primePowers hs]
  rw [← toothPrimeEquiv.tsum_eq]
  apply tsum_congr
  intro r
  apply tsum_congr
  intro k
  rw [primeToothDiskPoint_one_eq_cpow]
  change
    ((Real.log (toothPrime r : ℕ) : ℝ) : ℂ) /
        ((((toothPrime r : ℕ) ^ (k + 1) : ℕ) : ℂ) ^
          ((1 / 2 : ℂ) - s)) =
      ((Real.log (toothPrime r : ℕ) : ℝ) : ℂ) *
        (((toothNat (r, k) : ℕ) : ℂ) ^
          (-((1 / 2 : ℂ) - s)))
  rw [Complex.cpow_neg]
  simp [toothNat, toothExponent, div_eq_mul_inv]

/-- Absolute summability of all prime-power disk modes in the Euler
half-plane. -/
theorem summable_primeToothDiskPoint_one {s : ℂ}
    (hs : 1 < ((1 / 2 : ℂ) - s).re) :
    Summable fun i : PrimeTooth =>
      ((Real.log (toothPrime i.1 : ℕ) : ℝ) : ℂ) *
        primeToothDiskPoint (fun _ => 1) i s := by
  let u : ℂ := (1 / 2 : ℂ) - s
  let f : ℕ → ℂ := fun n =>
    LSeries.term (fun m : ℕ =>
      ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) u n
  have hsum : Summable f := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hinj : Function.Injective toothNat := by
    intro i j hij
    apply primeToothEtaIndex_injective
    simp [primeToothEtaIndex, hij]
  have hcomp : Summable (fun i : PrimeTooth => f (toothNat i)) :=
    hsum.comp_injective hinj
  refine hcomp.congr ?_
  intro i
  change
    LSeries.term (fun m : ℕ =>
      ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) u (toothNat i) =
      ((Real.log (toothPrime i.1 : ℕ) : ℝ) : ℂ) *
        primeToothDiskPoint (fun _ => 1) i s
  rw [LSeries.term_of_ne_zero
    (ne_of_gt (lt_of_lt_of_le zero_lt_two (toothNat_two_le i)))]
  rw [primeToothDiskPoint_one_eq_cpow]
  rw [Complex.cpow_neg]
  rw [show ArithmeticFunction.vonMangoldt (toothNat i) =
      Real.log (toothPrime i.1 : ℕ) by
    rw [toothNat,
      ArithmeticFunction.vonMangoldt_apply_pow (toothExponent_pos i).ne',
      ArithmeticFunction.vonMangoldt_apply_prime (toothPrime i.1).prop]]
  simp [u, div_eq_mul_inv]

/-- The finite one-clock-per-prime bank converges to the negative von
Mangoldt L-series in the Euler half-plane. -/
theorem primeClockCenteredBank_tendsto_neg_LSeries {s : ℂ}
    (hs : 1 < ((1 / 2 : ℂ) - s).re) :
    Tendsto (fun N => primeClockCenteredBank (fun _ => 1) N s) atTop
      (nhds (-LSeries (fun n : ℕ =>
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        ((1 / 2 : ℂ) - s))) := by
  let g : PrimeTooth → ℂ := fun i =>
    ((Real.log (toothPrime i.1 : ℕ) : ℝ) : ℂ) *
      primeToothDiskPoint (fun _ => 1) i s
  have hg : Summable g := summable_primeToothDiskPoint_one hs
  have hsleft : s.re < 1 / 2 := by
    norm_num [Complex.sub_re, Complex.div_re] at hs
    linarith
  have hinner (r : ℕ) :
      ∑' k : ℕ, g (r, k) =
        primeToothCenteredTerm (fun _ => 1) (r, 0) s := by
    exact (primeClockCenteredTerm_hasSum_primePowers
      (fun _ => 1) (by simp) r hsleft).tsum_eq
  have houter : Summable fun r : ℕ =>
      primeToothCenteredTerm (fun _ => 1) (r, 0) s := by
    refine hg.prod.congr ?_
    intro r
    exact hinner r
  have hvalue :
      ∑' r : ℕ, primeToothCenteredTerm (fun _ => 1) (r, 0) s =
        LSeries (fun n : ℕ =>
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          ((1 / 2 : ℂ) - s) := by
    calc
      _ = ∑' r : ℕ, ∑' k : ℕ, g (r, k) := by
        apply tsum_congr
        intro r
        exact (hinner r).symm
      _ = LSeries (fun n : ℕ =>
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          ((1 / 2 : ℂ) - s) :=
        (LSeries_vonMangoldt_reflected_eq_primeToothDiskPoint hs).symm
  have hhas : HasSum
      (fun r : ℕ => primeToothCenteredTerm (fun _ => 1) (r, 0) s)
      (LSeries (fun n : ℕ =>
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        ((1 / 2 : ℂ) - s)) := by
    rw [← hvalue]
    exact houter.hasSum
  simpa [primeClockCenteredBank, Finset.sum_neg_distrib] using
    hhas.neg.tendsto_sum_nat

/-- In the same half-plane, the bank limit is the reflected Riemann-zeta
logarithmic derivative. -/
theorem primeClockCenteredBank_tendsto_zetaLogDeriv {s : ℂ}
    (hs : 1 < ((1 / 2 : ℂ) - s).re) :
    Tendsto (fun N => primeClockCenteredBank (fun _ => 1) N s) atTop
      (nhds (logDeriv riemannZeta ((1 / 2 : ℂ) - s))) := by
  have h := primeClockCenteredBank_tendsto_neg_LSeries hs
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
    at h
  have heq :
      -(-deriv riemannZeta ((1 / 2 : ℂ) - s) /
          riemannZeta ((1 / 2 : ℂ) - s)) =
        deriv riemannZeta ((1 / 2 : ℂ) - s) /
          riemannZeta ((1 / 2 : ℂ) - s) := by ring
  rw [heq] at h
  simpa only [logDeriv_apply] using h

/-- The completed carrier needed to change the reflected zeta readout into
the completed xi readout in this chart. -/
def xiCarrierCorrection (s : ℂ) : ℂ :=
  logDeriv ZD.riemannXi s -
    logDeriv riemannZeta ((1 / 2 : ℂ) - s)

/-- Adding the completed carrier gives the xi logarithmic derivative in the
absolute-convergence region. -/
theorem primeClockCenteredBank_add_carrier_tendsto_xi {s : ℂ}
    (hs : 1 < ((1 / 2 : ℂ) - s).re) :
    Tendsto
      (fun N => primeClockCenteredBank (fun _ => 1) N s +
        xiCarrierCorrection s)
      atTop (nhds (logDeriv ZD.riemannXi s)) := by
  have hc : Tendsto (fun _ : ℕ => xiCarrierCorrection s) atTop
      (nhds (xiCarrierCorrection s)) := tendsto_const_nhds
  have h := (primeClockCenteredBank_tendsto_zetaLogDeriv hs).add hc
  simpa [xiCarrierCorrection] using h

/-- The completed carrier is constant in the rank, so it cancels exactly
from the pointwise convergence question. -/
theorem primeClockCenteredBank_add_carrier_tendsto_xi_iff (s : ℂ) :
    Tendsto
        (fun N => primeClockCenteredBank (fun _ => 1) N s +
          xiCarrierCorrection s)
        atTop (nhds (logDeriv ZD.riemannXi s)) ↔
      Tendsto (fun N => primeClockCenteredBank (fun _ => 1) N s)
        atTop
          (nhds (logDeriv riemannZeta ((1 / 2 : ℂ) - s))) := by
  constructor
  · intro h
    have hc : Tendsto (fun _ : ℕ => -xiCarrierCorrection s) atTop
        (nhds (-xiCarrierCorrection s)) := tendsto_const_nhds
    have hadd := h.add hc
    have hfun :
        (fun N => primeClockCenteredBank (fun _ => 1) N s +
          xiCarrierCorrection s + -xiCarrierCorrection s) =
        fun N => primeClockCenteredBank (fun _ => 1) N s := by
      funext N
      ring
    rw [hfun] at hadd
    have hlim :
        logDeriv ZD.riemannXi s + -xiCarrierCorrection s =
          logDeriv riemannZeta ((1 / 2 : ℂ) - s) := by
      simp [xiCarrierCorrection]
    rw [hlim] at hadd
    exact hadd
  · intro h
    have hc : Tendsto (fun _ : ℕ => xiCarrierCorrection s) atTop
        (nhds (xiCarrierCorrection s)) := tendsto_const_nhds
    have hadd := h.add hc
    have hlim :
        logDeriv riemannZeta ((1 / 2 : ℂ) - s) +
            xiCarrierCorrection s =
          logDeriv ZD.riemannXi s := by
      simp [xiCarrierCorrection]
    rw [hlim] at hadd
    exact hadd

/-- The revised pointwise residual with one clock per prime. -/
def PrimeClockCenteredNoTransient (α : Nat.Primes → ℂ) (A : ℝ) : Prop :=
  ∀ s : ℂ, 1269 / 2 < |s.im| →
    A / (Real.log |s.im|) ^ 9 < s.re → s.re < 1 / 2 →
    Tendsto (fun N => primeClockCenteredBank α N s)
      atTop (𝓝 (logDeriv ZD.riemannXi s))

end CriticalLinePhasor.BankNoTransient

#print axioms CriticalLinePhasor.BankNoTransient.primeToothDiskPoint_first_pow
#print axioms CriticalLinePhasor.BankNoTransient.primeClockCenteredTerm_hasSum_primePowers
#print axioms CriticalLinePhasor.BankNoTransient.LSeries_vonMangoldt_eq_tsum_primePowers
#print axioms CriticalLinePhasor.BankNoTransient.primeToothDiskPoint_one_eq_cpow
#print axioms
  CriticalLinePhasor.BankNoTransient.LSeries_vonMangoldt_reflected_eq_primeToothDiskPoint
#print axioms CriticalLinePhasor.BankNoTransient.summable_primeToothDiskPoint_one
#print axioms CriticalLinePhasor.BankNoTransient.primeClockCenteredBank_tendsto_neg_LSeries
#print axioms CriticalLinePhasor.BankNoTransient.primeClockCenteredBank_tendsto_zetaLogDeriv
#print axioms CriticalLinePhasor.BankNoTransient.primeClockCenteredBank_add_carrier_tendsto_xi
#print axioms
  CriticalLinePhasor.BankNoTransient.primeClockCenteredBank_add_carrier_tendsto_xi_iff
#print axioms CriticalLinePhasor.BankNoTransient.PrimeClockCenteredNoTransient
