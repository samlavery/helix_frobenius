import RequestProject.MajorantDensity

/-!
# A numerical density bound from the rank-≤ 4 record

`majorant_prime_average_le` turns any low-degree nonnegative majorant into a density bound.  This
file supplies an explicit one of degree four — the range in which symmetric-power automorphy is
classically known for Maass forms (Gelbart--Jacquet, Kim--Shahidi) — and reads off the number.

The majorant is `x⁴/t⁴`, which dominates the indicator of `|x| ≥ t` for the trivial reason that
`x⁴ ≥ t⁴` exactly there.  In the character basis

  **`16x⁴ = U₄ + 3·U₂ + 2·U₀`,**

so its constant term is `2/(16t⁴) = 1/(8t⁴)`, giving

  **density`{p : |cos θ_p| ≥ t}` ≤ `1/(8t⁴)`.**

Measured against the truth (`tmp`, this session): at `t = 0.9` the bound is `0.1905` and the
Sato--Tate value is `0.0374`; at `t = 0.8`, `0.3052` against `0.1041`.  So it is a genuine
non-trivial bound, loose by a factor of about five — which is the price of degree four.  Pushing
`t → 1` does not improve it past `1/8`, and that ceiling is exactly the bandwidth limit: no
degree-four nonnegative combination can concentrate more sharply.

**Scope — two conditions, not one.**

* The rank-`≤ 4` cancellation is a hypothesis of the theorem, not an assumption made here, and it
  is what the classical record supplies.
* **Temperedness is assumed structurally.**  These bounds are stated for an
  `ArithmeticSatakePrimeFamily`, and `ArithmeticSatakeTowerAtPrime.radius_one` forces `‖value‖ = 1`
  at every prime — so merely *forming* the family presupposes Ramanujan--Petersson for the form.
  For a Maass form that is **open** (Kim--Sarnak gives only `|a_p| ≤ 2p^{7/64}`), and by
  `temperedness_iff_ceiling` it is exactly the corpus's *other* Sato--Tate input.

So the Maass-side obstruction is not one open frontier but two: Ramanujan for the ceiling, and
`L(Sym^r)` beyond `r = 4` for the cancellation.  Nothing about ranks `> 4`, and nothing
unconditional about any Maass form, is claimed.
-/

open Filter Topology Polynomial Polynomial.Chebyshev

namespace CriticalLinePhasor.PartialSerre

open CriticalLinePhasor.SatoTateCarrier3D CriticalLinePhasor.GeneralSeed
open CriticalLinePhasor.MaassSatoTate

lemma U_eval_zero_real (x : ℝ) : (U ℝ (0 : ℤ)).eval x = 1 := by simp

lemma U_eval_one_real (x : ℝ) : (U ℝ (1 : ℤ)).eval x = 2 * x := by simp [U_one]

lemma U_eval_two_real (x : ℝ) : (U ℝ (2 : ℤ)).eval x = 4 * x ^ 2 - 1 := by
  have h := U_add_one ℝ (1 : ℤ)
  norm_num at h
  rw [h]
  simp [U_one]
  ring

lemma U_eval_three_real (x : ℝ) : (U ℝ (3 : ℤ)).eval x = 8 * x ^ 3 - 4 * x := by
  have h := U_add_one ℝ (2 : ℤ)
  norm_num at h
  rw [h]
  simp [U_eval_two_real, U_one]
  ring

lemma U_eval_four_real (x : ℝ) : (U ℝ (4 : ℤ)).eval x = 16 * x ^ 4 - 12 * x ^ 2 + 1 := by
  have h := U_add_one ℝ (3 : ℤ)
  norm_num at h
  rw [h]
  simp [U_eval_three_real, U_eval_two_real]
  ring

/-- The quartic majorant's coefficients in the character basis. -/
noncomputable def quarticCoeff (t : ℝ) : ℕ → ℝ
  | 0 => 1 / (8 * t ^ 4)
  | 2 => 3 / (16 * t ^ 4)
  | 4 => 1 / (16 * t ^ 4)
  | _ => 0

/-- **The quartic majorant.**  `x⁴/t⁴`, expanded in the character basis. -/
theorem quartic_expansion {t : ℝ} (ht : t ≠ 0) (x : ℝ) :
    ∑ r ∈ Finset.range 5, quarticCoeff t r * (U ℝ (r : ℤ)).eval x
      = x ^ 4 / t ^ 4 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, quarticCoeff]
  norm_num [U_eval_zero_real, U_eval_one_real, U_eval_two_real, U_eval_three_real,
    U_eval_four_real]
  field_simp
  ring

/-- **A numerical density bound from rank ≤ 4.**  Under the classically available cancellation for
`1 ≤ r ≤ 4`, the proportion of primes whose Satake angle has `|cos θ_p| ≥ t` is eventually below
`1/(8t⁴) + ε`. -/
theorem quartic_density_bound (F : ArithmeticSatakePrimeFamily)
    (hcanc : ∀ r : ℕ, 1 ≤ r → r ≤ 4 →
      Tendsto (fun n => arithmeticSymmetricPowerPrimeAverage F r n) atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1),
          (if t ≤ |Real.cos (F.angle (nthPrime i))| then (1 : ℝ) else 0)
        < 1 / (8 * t ^ 4) + ε := by
  have hbound := majorant_prime_average_le F 4 hcanc (quarticCoeff t)
    (fun θ => if t ≤ |Real.cos θ| then (1 : ℝ) else 0) ?_ hε
  · simpa [quarticCoeff] using hbound
  · intro p
    rw [quartic_expansion ht.ne' (Real.cos (F.angle p))]
    by_cases hcase : t ≤ |Real.cos (F.angle p)|
    · rw [if_pos hcase]
      rw [le_div_iff₀ (by positivity)]
      have h1 : t ^ 4 ≤ |Real.cos (F.angle p)| ^ 4 := by
        gcongr
      calc (1 : ℝ) * t ^ 4 = t ^ 4 := one_mul _
        _ ≤ |Real.cos (F.angle p)| ^ 4 := h1
        _ = Real.cos (F.angle p) ^ 4 := by
            rw [← abs_pow, abs_of_nonneg (by positivity)]
    · rw [if_neg hcase]
      positivity


/-! ## The shifted quartic: a free parameter to optimise

`x⁴/t⁴` is the crudest quartic majorant.  The family `(x² − s²)²/(t² − s²)²` majorises the same
indicator for every `0 ≤ s < t` — if `|x| ≥ t` then `x² − s² ≥ t² − s² > 0` — and its constant term

  **`(1/8 − s²/2 + s⁴)/(t² − s²)²`**

is minimised at a nonzero shift.  Measured: at `t = 0.9`, `s = 0` gives `0.1905` and `s ≈ 0.372`
gives `0.1662`; at `t = 0.95`, `0.1535` improves to `0.1280`.  The `s = 0` case recovers
`quartic_density_bound`. -/

/-- The shifted quartic majorant's coefficients. -/
noncomputable def shiftedCoeff (s t : ℝ) : ℕ → ℝ
  | 0 => (1 / 8 - s ^ 2 / 2 + s ^ 4) / (t ^ 2 - s ^ 2) ^ 2
  | 2 => (3 / 16 - s ^ 2 / 2) / (t ^ 2 - s ^ 2) ^ 2
  | 4 => (1 / 16) / (t ^ 2 - s ^ 2) ^ 2
  | _ => 0

theorem shifted_expansion {s t : ℝ} (hst : t ^ 2 - s ^ 2 ≠ 0) (x : ℝ) :
    ∑ r ∈ Finset.range 5, shiftedCoeff s t r * (U ℝ (r : ℤ)).eval x
      = (x ^ 2 - s ^ 2) ^ 2 / (t ^ 2 - s ^ 2) ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, shiftedCoeff]
  norm_num [U_eval_zero_real, U_eval_one_real, U_eval_two_real, U_eval_three_real,
    U_eval_four_real]
  field_simp
  ring

/-- **The shifted density bound.**  For any `0 ≤ s < t`, rank-`≤ 4` cancellation gives
`density{p : |cos θ_p| ≥ t} ≤ (1/8 − s²/2 + s⁴)/(t² − s²)²`, which beats the `s = 0` case. -/
theorem shifted_density_bound (F : ArithmeticSatakePrimeFamily)
    (hcanc : ∀ r : ℕ, 1 ≤ r → r ≤ 4 →
      Tendsto (fun n => arithmeticSymmetricPowerPrimeAverage F r n) atTop (𝓝 0))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1),
          (if t ≤ |Real.cos (F.angle (nthPrime i))| then (1 : ℝ) else 0)
        < (1 / 8 - s ^ 2 / 2 + s ^ 4) / (t ^ 2 - s ^ 2) ^ 2 + ε := by
  have hsq : s ^ 2 < t ^ 2 := by nlinarith
  have hne : t ^ 2 - s ^ 2 ≠ 0 := by nlinarith
  have hpos : (0 : ℝ) < t ^ 2 - s ^ 2 := by linarith
  have hbound := majorant_prime_average_le F 4 hcanc (shiftedCoeff s t)
    (fun θ => if t ≤ |Real.cos θ| then (1 : ℝ) else 0) ?_ hε
  · simpa [shiftedCoeff] using hbound
  · intro p
    rw [shifted_expansion hne (Real.cos (F.angle p))]
    by_cases hcase : t ≤ |Real.cos (F.angle p)|
    · rw [if_pos hcase]
      rw [le_div_iff₀ (by positivity)]
      have hx : t ^ 2 ≤ Real.cos (F.angle p) ^ 2 := by
        have h1 : t ^ 2 ≤ |Real.cos (F.angle p)| ^ 2 := by
          gcongr
          linarith
        rwa [← abs_pow, abs_of_nonneg (by positivity)] at h1
      nlinarith
    · rw [if_neg hcase]
      positivity


/-! ## Higher Chebyshev evaluations

The corpus's cited record reaches rank nine (`PartialSerre`), so majorants of degree up to nine are
available.  These are the remaining explicit evaluations, each one step of the recurrence. -/

lemma U_eval_five_real (x : ℝ) :
    (U ℝ (5 : ℤ)).eval x = 32 * x ^ 5 - 32 * x ^ 3 + 6 * x := by
  have h := U_add_one ℝ (4 : ℤ)
  norm_num at h
  rw [h]
  simp [U_eval_four_real, U_eval_three_real]
  ring

lemma U_eval_six_real (x : ℝ) :
    (U ℝ (6 : ℤ)).eval x = 64 * x ^ 6 - 80 * x ^ 4 + 24 * x ^ 2 - 1 := by
  have h := U_add_one ℝ (5 : ℤ)
  norm_num at h
  rw [h]
  simp [U_eval_five_real, U_eval_four_real]
  ring

lemma U_eval_seven_real (x : ℝ) :
    (U ℝ (7 : ℤ)).eval x = 128 * x ^ 7 - 192 * x ^ 5 + 80 * x ^ 3 - 8 * x := by
  have h := U_add_one ℝ (6 : ℤ)
  norm_num at h
  rw [h]
  simp [U_eval_six_real, U_eval_five_real]
  ring

lemma U_eval_eight_real (x : ℝ) :
    (U ℝ (8 : ℤ)).eval x = 256 * x ^ 8 - 448 * x ^ 6 + 240 * x ^ 4 - 40 * x ^ 2 + 1 := by
  have h := U_add_one ℝ (7 : ℤ)
  norm_num at h
  rw [h]
  simp [U_eval_seven_real, U_eval_six_real]
  ring

/-- **The even monomials in the character basis.**  The constant term of `x^{2m}` is the Catalan
number over `4^m` — which is exactly its Sato--Tate moment. -/
theorem monomial_eight_expansion (x : ℝ) :
    256 * x ^ 8 = (U ℝ (8 : ℤ)).eval x + 7 * (U ℝ (6 : ℤ)).eval x
      + 20 * (U ℝ (4 : ℤ)).eval x + 28 * (U ℝ (2 : ℤ)).eval x
      + 14 * (U ℝ (0 : ℤ)).eval x := by
  rw [U_eval_eight_real, U_eval_six_real, U_eval_four_real, U_eval_two_real, U_eval_zero_real]
  ring

theorem monomial_six_expansion (x : ℝ) :
    64 * x ^ 6 = (U ℝ (6 : ℤ)).eval x + 5 * (U ℝ (4 : ℤ)).eval x
      + 9 * (U ℝ (2 : ℤ)).eval x + 5 * (U ℝ (0 : ℤ)).eval x := by
  rw [U_eval_six_real, U_eval_four_real, U_eval_two_real, U_eval_zero_real]
  ring


/-! ## The degree-eight bound

Two shifts instead of one.  Measured: at `t = 0.9` the optimum is `0.1090` at `(s,u) ≈ (0.22,0.62)`
against the quartic's `0.1662` — a 34% improvement, using the corpus's cited rank-nine record.  The
proved ceiling at this degree is `(4/6)·sin²(π/12) = 0.0447` (degree `8` needs `8+2 < 2n`, so
`n = 6`), so the majorant is within a factor `2.4` of optimal.

Caution, measured: at `t = 0.8` the optimum degenerates to `s = u = 0` and is *worse* than the
quartic (`0.3260` vs `0.3052`).  Higher degree does not automatically help — the family has to be
adapted to `t`. -/

noncomputable def oB (s u : ℝ) : ℝ := -(s ^ 2 + u ^ 2)
noncomputable def oC (s u : ℝ) : ℝ := s ^ 2 * u ^ 2
noncomputable def oD (s u t : ℝ) : ℝ := ((t ^ 2 - s ^ 2) * (t ^ 2 - u ^ 2)) ^ 2

/-- The degree-eight majorant's coefficients in the character basis. -/
noncomputable def octicCoeff (s u t : ℝ) : ℕ → ℝ
  | 0 => (7 / 128 + 5 * oB s u / 32 + (oB s u ^ 2 + 2 * oC s u) / 8
            + oB s u * oC s u / 2 + oC s u ^ 2) / oD s u t
  | 2 => (7 / 64 + 9 * oB s u / 32 + 3 * (oB s u ^ 2 + 2 * oC s u) / 16
            + oB s u * oC s u / 2) / oD s u t
  | 4 => (5 / 64 + 5 * oB s u / 32 + (oB s u ^ 2 + 2 * oC s u) / 16) / oD s u t
  | 6 => (7 / 256 + oB s u / 32) / oD s u t
  | 8 => (1 / 256) / oD s u t
  | _ => 0

theorem octic_expansion {s u t : ℝ} (hD : oD s u t ≠ 0) (x : ℝ) :
    ∑ r ∈ Finset.range 9, octicCoeff s u t r * (U ℝ (r : ℤ)).eval x
      = ((x ^ 2 - s ^ 2) * (x ^ 2 - u ^ 2)) ^ 2 / oD s u t := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, octicCoeff]
  norm_num [U_eval_zero_real, U_eval_one_real, U_eval_two_real, U_eval_three_real,
    U_eval_four_real, U_eval_five_real, U_eval_six_real, U_eval_seven_real,
    U_eval_eight_real, oB, oC]
  field_simp
  ring

/-- **The degree-eight density bound.** -/
theorem octic_density_bound (F : ArithmeticSatakePrimeFamily)
    (hcanc : ∀ r : ℕ, 1 ≤ r → r ≤ 8 →
      Tendsto (fun n => arithmeticSymmetricPowerPrimeAverage F r n) atTop (𝓝 0))
    {s u t : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) (hst : s < t) (hut : u < t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1),
          (if t ≤ |Real.cos (F.angle (nthPrime i))| then (1 : ℝ) else 0)
        < octicCoeff s u t 0 + ε := by
  have hs2 : s ^ 2 < t ^ 2 := by nlinarith
  have hu2 : u ^ 2 < t ^ 2 := by nlinarith
  have hDpos : 0 < oD s u t := by
    rw [oD]; positivity
  have hbound := majorant_prime_average_le F 8 hcanc (octicCoeff s u t)
    (fun θ => if t ≤ |Real.cos θ| then (1 : ℝ) else 0) ?_ hε
  · exact hbound
  · intro p
    rw [octic_expansion hDpos.ne' (Real.cos (F.angle p))]
    by_cases hcase : t ≤ |Real.cos (F.angle p)|
    · rw [if_pos hcase]
      rw [le_div_iff₀ hDpos]
      have hx : t ^ 2 ≤ Real.cos (F.angle p) ^ 2 := by
        have h1 : t ^ 2 ≤ |Real.cos (F.angle p)| ^ 2 := by
          gcongr
          linarith
        rwa [← abs_pow, abs_of_nonneg (by positivity)] at h1
      rw [oD, one_mul]
      have h1 : (t ^ 2 - s ^ 2) ≤ (Real.cos (F.angle p) ^ 2 - s ^ 2) := by linarith
      have h2 : (t ^ 2 - u ^ 2) ≤ (Real.cos (F.angle p) ^ 2 - u ^ 2) := by linarith
      have h3 : (0:ℝ) < (t ^ 2 - s ^ 2) := by linarith
      have h4 : (0:ℝ) < (t ^ 2 - u ^ 2) := by linarith
      gcongr <;> nlinarith [h1, h2, h3, h4]
    · rw [if_neg hcase]
      positivity

end CriticalLinePhasor.PartialSerre

#print axioms CriticalLinePhasor.PartialSerre.quartic_density_bound
#print axioms CriticalLinePhasor.PartialSerre.shifted_density_bound
#print axioms CriticalLinePhasor.PartialSerre.monomial_eight_expansion
#print axioms CriticalLinePhasor.PartialSerre.octic_density_bound
