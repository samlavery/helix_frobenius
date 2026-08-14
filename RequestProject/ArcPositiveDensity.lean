import RequestProject.QuarticMajorant

/-!
# Positive density in an arc, from finitely many ranks

`MajorantDensity` gives the one-sided *upper* bounds: a degree-`≤ R` character combination
dominating an indicator caps the density of the corresponding set of Satake angles.  This file
supplies the other side, which is the one that carries arithmetic content.

A degree-`≤ R` combination lying **below** an indicator forces the density of that arc to be at
least the combination's constant term.  Unlike the majorant side, a minorant with positive
constant term need not exist: for a short arc every degree-`≤ R` minorant of its indicator has
constant term `≤ 0`, and the bound is vacuous.  Where a positive one does exist, the conclusion is
a genuine *lower* bound on how often the Satake angle visits the arc — the shape of Serre's
partial equidistribution.

Two explicit minorants are constructed, both with exactly rational coefficients:

* **Rank two.**  `P(x) = x(x + 1)/2` lies below `1_{x ≥ 0}` on `[-1, 1]` and has
  `∫ P dμ_ST = 1/8`.  So cancellation at `r ≤ 2` alone forces
  **at least `1/8` of primes to satisfy `a_p ≥ 0`** (true value `1/2`).
* **Rank four.**  `P(x) = (x + 1)(3x + 1)²(2x − 1)/32` lies below `1_{x ≥ 1/2}` on `[-1, 1]` and
  has `∫ P dμ_ST = 1/32`.  So cancellation at `r ≤ 4` forces
  **at least `1/32` of primes to satisfy `a_p ≥ 1`**, i.e. `θ_p ∈ [0, π/3]` (true value
  `0.1955`).

Both are the exact optima of the corresponding linear program over degree-`≤ R` minorants, found
numerically and then identified in closed form; the `1` at `x = 1` and the double root are the
active constraints.

**Scope.**  Cancellation at the stated ranks is a hypothesis here, as everywhere in this thread.
For a Maass form the ranks `r ≤ 4` are the classical record (`Sym²` Gelbart--Jacquet, `Sym³` and
`Sym⁴` Kim--Shahidi); nothing in this file supplies them, and nothing here bears on ranks beyond
four.  Full equidistribution needs every rank and is not obtained.
-/

open Filter Topology Polynomial Polynomial.Chebyshev

namespace CriticalLinePhasor.PartialSerre

open CriticalLinePhasor.SatoTateCarrier3D CriticalLinePhasor.GeneralSeed
open CriticalLinePhasor.MaassSatoTate

/-! ## The minorant interface -/

/-- **The minorant bound.**  If a degree-`≤ R` character combination is dominated by `g` on the
Satake angles, the prime average of `g` is eventually above the combination's constant term.

Mirror of `majorant_prime_average_le`; the two together bracket every degree-`≤ R` observable. -/
theorem minorant_prime_average_ge (F : ArithmeticSatakePrimeFamily) (R : ℕ)
    (hcanc : ∀ r : ℕ, 1 ≤ r → r ≤ R →
      Tendsto (fun n => arithmeticSymmetricPowerPrimeAverage F r n) atTop (𝓝 0))
    (c : ℕ → ℝ) (g : ℝ → ℝ)
    (hmin : ∀ p : Nat.Primes,
      ∑ r ∈ Finset.range (R + 1), c r * (U ℝ (r : ℤ)).eval (Real.cos (F.angle p))
        ≤ g (F.angle p))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      c 0 - ε < (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i : Fin (n + 1), g (F.angle (nthPrime i)) := by
  have hobs := partial_serre F R hcanc c
  have hev : ∀ᶠ n : ℕ in atTop, c 0 - ε < polyObservableAverage F c R n :=
    hobs.eventually_const_lt (by linarith)
  filter_upwards [hev] with n hn
  refine lt_of_lt_of_le hn ?_
  rw [polyObservableAverage_eq]
  have hpos : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpos.le
  exact Finset.sum_le_sum fun i _ => hmin (nthPrime i)


/-! ## Rank two: a positive proportion of nonnegative coefficients -/

/-- The rank-two minorant `x(x+1)/2` in the character basis. -/
noncomputable def nonnegArcCoeff : ℕ → ℝ
  | 0 => 1 / 8
  | 1 => 1 / 4
  | 2 => 1 / 8
  | _ => 0

/-- The character combination is the quadratic `x(x+1)/2`. -/
lemma nonnegArcCoeff_eval (x : ℝ) :
    ∑ r ∈ Finset.range 3, nonnegArcCoeff r * (U ℝ (r : ℤ)).eval x = x * (x + 1) / 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nonnegArcCoeff, U_eval_zero_real, U_eval_one_real, U_eval_two_real]
  ring

/-- **`x(x+1)/2` lies below the indicator of `x ≥ 0` on `[-1, 1]`.**  Below the arc it is
nonpositive because the two factors have opposite signs; inside it is at most `1`, attained at
`x = 1`. -/
lemma nonnegArcCoeff_minorant {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    ∑ r ∈ Finset.range 3, nonnegArcCoeff r * (U ℝ (r : ℤ)).eval x
      ≤ (if (0 : ℝ) ≤ x then (1 : ℝ) else 0) := by
  rw [nonnegArcCoeff_eval]
  split_ifs with h
  · nlinarith
  · rw [not_le] at h
    nlinarith

/-- **★ Rank two forces a positive proportion of nonnegative Hecke coefficients.**

Cancellation at `r ≤ 2` alone — for a Maass form, the `Sym²` Rankin--Selberg statement — puts at
least `1/8` of the primes in the half `cos θ_p ≥ 0`, i.e. `a_p ≥ 0`.  The Sato--Tate value is
`1/2`; this is the part of it that two ranks already force. -/
theorem nonneg_coefficient_positive_density (F : ArithmeticSatakePrimeFamily)
    (hcanc : ∀ r : ℕ, 1 ≤ r → r ≤ 2 →
      Tendsto (fun n => arithmeticSymmetricPowerPrimeAverage F r n) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      1 / 8 - ε < (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1),
          (if (0 : ℝ) ≤ Real.cos (F.angle (nthPrime i)) then (1 : ℝ) else 0) := by
  have h := minorant_prime_average_ge F 2 hcanc nonnegArcCoeff
    (fun θ => if (0 : ℝ) ≤ Real.cos θ then (1 : ℝ) else 0)
    (fun p => nonnegArcCoeff_minorant (Real.neg_one_le_cos _) (Real.cos_le_one _)) hε
  simpa [nonnegArcCoeff] using h


/-! ## Rank four: a positive proportion in the arc `θ ≤ π/3` -/

/-- The rank-four minorant `(x+1)(3x+1)²(2x−1)/32` in the character basis. -/
noncomputable def thirdArcCoeff : ℕ → ℝ
  | 0 => 1 / 32
  | 1 => 11 / 128
  | 2 => 25 / 256
  | 3 => 21 / 256
  | 4 => 9 / 256
  | _ => 0

/-- The character combination is the quartic `(x+1)(3x+1)²(2x−1)/32`. -/
lemma thirdArcCoeff_eval (x : ℝ) :
    ∑ r ∈ Finset.range 5, thirdArcCoeff r * (U ℝ (r : ℤ)).eval x
      = (x + 1) * (3 * x + 1) ^ 2 * (2 * x - 1) / 32 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [thirdArcCoeff, U_eval_zero_real, U_eval_one_real, U_eval_two_real,
    U_eval_three_real, U_eval_four_real]
  ring

/-- **The quartic lies below the indicator of `x ≥ 1/2` on `[-1, 1]`.**

Below the arc the double root `(3x+1)²` keeps the sign, so the product is nonpositive.  Inside,
`32 − (x+1)(3x+1)²(2x−1) = (1−x)(18x³ + 39x² + 38x + 33)` and the cubic factor is positive on
`[-1, 1]` — it is `18x²(x+1) + (21x² + 38x + 33)`, a sum of two nonnegative pieces. -/
lemma thirdArcCoeff_minorant {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    ∑ r ∈ Finset.range 5, thirdArcCoeff r * (U ℝ (r : ℤ)).eval x
      ≤ (if (1 / 2 : ℝ) ≤ x then (1 : ℝ) else 0) := by
  rw [thirdArcCoeff_eval]
  split_ifs with h
  · have hcube : (0 : ℝ) < 18 * x ^ 3 + 39 * x ^ 2 + 38 * x + 33 := by
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 18) (sq_nonneg x))
        (by linarith : (0:ℝ) ≤ x + 1), sq_nonneg (21 * x + 19)]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - x) hcube.le]
  · rw [not_le] at h
    have h1 : (0 : ℝ) ≤ (x + 1) * (3 * x + 1) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    nlinarith [mul_nonneg h1 (by linarith : (0:ℝ) ≤ 1 - 2 * x)]

/-- **★ Rank four forces a positive proportion of Satake angles into `[0, π/3]`.**

Cancellation at `r ≤ 4` — for a Maass form, `Sym²` (Gelbart--Jacquet) together with `Sym³` and
`Sym⁴` (Kim--Shahidi) — puts at least `1/32` of the primes in the arc `cos θ_p ≥ 1/2`, i.e.
`a_p ≥ 1`.  The Sato--Tate value is `0.1955`.

This is the first *lower* bound in the thread: every previous density statement here caps how
often the coefficients can be large, and is therefore compatible with the angles never entering
the arc at all.  This one is not. -/
theorem third_arc_positive_density (F : ArithmeticSatakePrimeFamily)
    (hcanc : ∀ r : ℕ, 1 ≤ r → r ≤ 4 →
      Tendsto (fun n => arithmeticSymmetricPowerPrimeAverage F r n) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      1 / 32 - ε < (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1),
          (if (1 / 2 : ℝ) ≤ Real.cos (F.angle (nthPrime i)) then (1 : ℝ) else 0) := by
  have h := minorant_prime_average_ge F 4 hcanc thirdArcCoeff
    (fun θ => if (1 / 2 : ℝ) ≤ Real.cos θ then (1 : ℝ) else 0)
    (fun p => thirdArcCoeff_minorant (Real.neg_one_le_cos _) (Real.cos_le_one _)) hε
  simpa [thirdArcCoeff] using h

end CriticalLinePhasor.PartialSerre

#print axioms CriticalLinePhasor.PartialSerre.minorant_prime_average_ge
#print axioms CriticalLinePhasor.PartialSerre.nonneg_coefficient_positive_density
#print axioms CriticalLinePhasor.PartialSerre.third_arc_positive_density
