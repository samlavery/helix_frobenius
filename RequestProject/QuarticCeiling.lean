import RequestProject.SatoTateBlock

/-!
# The degree-four ceiling is real

Last file I optimised the majorant and withdrew a ceiling claim I had not proved.  This file proves
one, and the tool is the quadrature itself.

For `n = 4` the Gauss--Chebyshev rule is exact on `P·(1−X²)` whenever `deg P ≤ 4`, and **all four
weights `1 − x_i²` are positive**.  So the Sato--Tate integral of a nonnegative `P` is bounded
below by any single node's contribution.  Two of the four nodes are `±cos(π/8)`, so if `P` majorises
the indicator of `|x| ≥ t` for some `t ≤ cos(π/8)`, then `P ≥ 1` at both, and

  **`∫_0^π P(cos θ)·sin²θ dθ ≥ (π/2)·sin²(π/8)`,**

i.e. the Sato--Tate-normalised integral is at least `sin²(π/8) = (2 − √2)/4 ≈ 0.1464`.

That is a genuine lower bound over **every** nonnegative degree-≤ 4 majorant, not just the family
I happened to write down.  Against it: my optimised `shifted_density_bound` gives `0.1662` at
`t = 0.9`, so that majorant is within 14% of the best possible at its degree — while the true
Sato--Tate density there is `0.0374`.  **The remaining factor of four is structural**: degree four
cannot see it, no matter which majorant is chosen.  Only higher ranks can, which is the same wall.

**Scope.**  Lower bound for degree `≤ 4`.  No claim about other degrees.
-/

open Polynomial Polynomial.Chebyshev

namespace CriticalLinePhasor.ThreeDConverse

private lemma cos_seven_pi_div_eight :
    Real.cos (7 / 8 * Real.pi) = -Real.cos (1 / 8 * Real.pi) := by
  rw [show (7 / 8 * Real.pi) = Real.pi - 1 / 8 * Real.pi by ring, Real.cos_pi_sub]

private lemma cos_pi_div_eight_nonneg : 0 ≤ Real.cos (1 / 8 * Real.pi) := by
  refine Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], ?_⟩
  nlinarith [Real.pi_pos]

/-- **No nonnegative degree-≤ 4 majorant beats `sin²(π/8)`.** -/
theorem quartic_majorant_lower_bound {t : ℝ} (ht : t ≤ Real.cos (1 / 8 * Real.pi))
    {P : ℝ[X]} (hdeg : (P * (1 - X ^ 2)).degree < 2 * ((4 : ℕ) : WithBot ℕ))
    (hnn : ∀ x : ℝ, |x| ≤ 1 → 0 ≤ P.eval x)
    (hmaj : ∀ x : ℝ, |x| ≤ 1 → t ≤ |x| → 1 ≤ P.eval x) :
    (Real.pi / 2) * Real.sin (1 / 8 * Real.pi) ^ 2
      ≤ ∫ θ in (0:ℝ)..Real.pi, P.eval (Real.cos θ) * Real.sin θ ^ 2 := by
  rw [satoTate_quadrature (by norm_num) hdeg, sumZeroes]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  -- the four nodes
  set c := Real.cos (1 / 8 * Real.pi) with hc
  have habs : ∀ θ : ℝ, |Real.cos θ| ≤ 1 := fun θ => Real.abs_cos_le_one θ
  have hsin : Real.sin (1 / 8 * Real.pi) ^ 2 = 1 - c ^ 2 := by
    have := Real.sin_sq_add_cos_sq (1 / 8 * Real.pi); rw [hc]; linarith
  -- the two extreme nodes carry `P ≥ 1`
  have hP0 : 1 ≤ P.eval (Real.cos (1 / 8 * Real.pi)) := by
    refine hmaj _ (habs _) ?_
    rw [abs_of_nonneg cos_pi_div_eight_nonneg]
    exact ht
  have hP3 : 1 ≤ P.eval (Real.cos (7 / 8 * Real.pi)) := by
    refine hmaj _ (habs _) ?_
    rw [cos_seven_pi_div_eight, abs_neg, abs_of_nonneg cos_pi_div_eight_nonneg]
    exact ht
  -- the two middle nodes are harmless
  have hP1 : 0 ≤ P.eval (Real.cos (3 / 8 * Real.pi)) := hnn _ (habs _)
  have hP2 : 0 ≤ P.eval (Real.cos (5 / 8 * Real.pi)) := hnn _ (habs _)
  have hsq0 : Real.cos (1 / 8 * Real.pi) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (1 / 8 * Real.pi), sq_nonneg (Real.sin (1 / 8 * Real.pi))]
  have hsq1 : Real.cos (3 / 8 * Real.pi) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (3 / 8 * Real.pi), sq_nonneg (Real.sin (3 / 8 * Real.pi))]
  have hsq2 : Real.cos (5 / 8 * Real.pi) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (5 / 8 * Real.pi), sq_nonneg (Real.sin (5 / 8 * Real.pi))]
  have hsq3 : Real.cos (7 / 8 * Real.pi) ^ 2 = c ^ 2 := by
    rw [cos_seven_pi_div_eight, neg_pow, neg_one_pow_two, one_mul]
  rw [hsin]
  have hpi := Real.pi_pos
  have h1c : (0:ℝ) ≤ 1 - c ^ 2 := by rw [← hsin]; positivity
  have e0 : (1 - c ^ 2) ≤ P.eval c * (1 - c ^ 2) := by nlinarith [hP0, h1c]
  have e3 : (1 - c ^ 2)
      ≤ P.eval (Real.cos (7 / 8 * Real.pi)) * (1 - Real.cos (7 / 8 * Real.pi) ^ 2) := by
    rw [hsq3]; nlinarith [hP3, h1c]
  have e1 : 0 ≤ P.eval (Real.cos (3 / 8 * Real.pi)) * (1 - Real.cos (3 / 8 * Real.pi) ^ 2) :=
    mul_nonneg hP1 (by nlinarith [hsq1])
  have e2 : 0 ≤ P.eval (Real.cos (5 / 8 * Real.pi)) * (1 - Real.cos (5 / 8 * Real.pi) ^ 2) :=
    mul_nonneg hP2 (by nlinarith [hsq2])
  nlinarith [e0, e1, e2, e3, hpi, h1c]


/-! ## Every degree, and the universal constant

The same argument runs at any node count.  For `deg P ≤ 2n − 3` the rule is exact (the hypothesis
is `deg(P·(1−X²)) < 2n`, and multiplying by `1−X²` costs two degrees), all `n` weights
are positive, and the two outermost nodes are `±cos(π/2n)`:

  **`∫_0^π P(cos θ)·sin²θ dθ ≥ (2π/n)·sin²(π/2n)`**  whenever `t ≤ cos(π/2n)`.

Normalised, that is `(4/n)·sin²(π/2n) ≈ π²/n³`.  The true Sato--Tate density at the same `t` is
`(4/3π)·(π/2n)³ = π²/6n³`.  **So the bandwidth-limited bound has exactly the right order, and the
loss is a universal factor of 6** — measured: `5.876` at `n = 4`, `5.945` at `6`, `5.980` at `10`,
`5.995` at `20`, `5.999` at `40`.

Higher ranks therefore *do* help, at rate `n⁻³`, and never do better than `6×` the truth by this
route.  The `n = 4` case above is the instance the classical Maass record supplies. -/

theorem majorant_lower_bound {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : t ≤ Real.cos (1 / (2 * (n : ℝ)) * Real.pi))
    {P : ℝ[X]} (hdeg : (P * (1 - X ^ 2)).degree < 2 * (n : WithBot ℕ))
    (hnn : ∀ x : ℝ, |x| ≤ 1 → 0 ≤ P.eval x)
    (hmaj : ∀ x : ℝ, |x| ≤ 1 → t ≤ |x| → 1 ≤ P.eval x) :
    (2 * Real.pi / n) * Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2
      ≤ ∫ θ in (0:ℝ)..Real.pi, P.eval (Real.cos θ) * Real.sin θ ^ 2 := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
  rw [satoTate_quadrature hn0.ne' hdeg, sumZeroes]
  set Q : ℕ → ℝ := fun i =>
    ((P * (1 - X ^ 2)).eval (Real.cos ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi))) with hQ
  -- every node value is nonnegative
  have habs : ∀ θ : ℝ, |Real.cos θ| ≤ 1 := Real.abs_cos_le_one
  have hQnn : ∀ i : ℕ, 0 ≤ Q i := by
    intro i
    rw [hQ]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_pow, Polynomial.eval_X]
    refine mul_nonneg (hnn _ (habs _)) ?_
    nlinarith [Real.sin_sq_add_cos_sq ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi),
      sq_nonneg (Real.sin ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi))]
  -- the two outermost nodes
  have hc0 : (2 * ((0 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi
      = 1 / (2 * (n : ℝ)) * Real.pi := by norm_num
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : (1 : ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub this]
    ring
  have hcn : (2 * ((n - 1 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi
      = Real.pi - 1 / (2 * (n : ℝ)) * Real.pi := by
    rw [hcast]
    field_simp
    ring
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
  have hcpos : 0 ≤ Real.cos (1 / (2 * (n : ℝ)) * Real.pi) := by
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · have hp : (0:ℝ) < 1 / (2 * (n : ℝ)) * Real.pi := by positivity
      linarith [Real.pi_pos]
    · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_pos, hn1]
  have hsin : Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2
      = 1 - Real.cos (1 / (2 * (n : ℝ)) * Real.pi) ^ 2 := by
    have := Real.sin_sq_add_cos_sq (1 / (2 * (n : ℝ)) * Real.pi); linarith
  have hQ0 : Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2 ≤ Q 0 := by
    rw [hQ]
    simp only [hc0, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_pow, Polynomial.eval_X]
    have h1 : 1 ≤ P.eval (Real.cos (1 / (2 * (n : ℝ)) * Real.pi)) := by
      refine hmaj _ (habs _) ?_
      rw [abs_of_nonneg hcpos]; exact ht
    rw [hsin]
    nlinarith [h1, hsin, sq_nonneg (Real.sin (1 / (2 * (n : ℝ)) * Real.pi))]
  have hQn : Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2 ≤ Q (n - 1) := by
    rw [hQ]
    simp only [hcn, Real.cos_pi_sub, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
    have h1 : 1 ≤ P.eval (-Real.cos (1 / (2 * (n : ℝ)) * Real.pi)) := by
      refine hmaj _ (by rw [abs_neg]; exact habs _) ?_
      rw [abs_neg, abs_of_nonneg hcpos]; exact ht
    rw [hsin]
    nlinarith [h1, hsin, sq_nonneg (Real.sin (1 / (2 * (n : ℝ)) * Real.pi))]
  -- collect the two nodes out of the full sum
  have hsub : ({0, n - 1} : Finset ℕ) ⊆ Finset.range n := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  have hne : (0 : ℕ) ≠ n - 1 := by omega
  have hpair : ∑ i ∈ ({0, n - 1} : Finset ℕ), Q i = Q 0 + Q (n - 1) :=
    Finset.sum_pair hne
  have hcollect : Q 0 + Q (n - 1) ≤ ∑ i ∈ Finset.range n, Q i := by
    rw [← hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ =>
      hQnn i
  have hkey : 2 * Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2 ≤ ∑ i ∈ Finset.range n, Q i := by
    linarith [hQ0, hQn, hcollect]
  have hpi : 0 < Real.pi / (n : ℝ) := by positivity
  calc (2 * Real.pi / (n : ℝ)) * Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2
      = (Real.pi / (n : ℝ)) * (2 * Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2) := by ring
    _ ≤ (Real.pi / (n : ℝ)) * ∑ i ∈ Finset.range n, Q i :=
        mul_le_mul_of_nonneg_left hkey hpi.le


/-! ## The ceiling is sharp: the quadrature measure attains it

`majorant_lower_bound` is not merely a bound — it is the **exact** LP value, because the
Gauss--Chebyshev measure itself attains it.  That measure has the same moments as Sato--Tate up to
degree `2n − 3` (`satoTate_quadrature`), and this section shows its mass on `|x| ≥ cos(π/2n)` is
exactly the two outer nodes' weight, `(4/n)·sin²(π/2n)` — because every interior node is strictly
inside.

Consequence: from symmetric-power data up to rank `2n − 3` alone, **no argument whatever** can bound
the density better.  The factor of `6` is not slack in the majorant method; it is the information
content of finitely many moments. -/

/-- **Interior nodes are strictly inside.**  Only `i = 0` and `i = n−1` reach `cos(π/2n)`. -/
theorem interior_node_lt {n : ℕ} (hn : 2 ≤ n) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ n - 2) :
    |Real.cos ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi)|
      < Real.cos (1 / (2 * (n : ℝ)) * Real.pi) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast h1
  have hiR2 : (i : ℝ) ≤ (n : ℝ) - 2 := by
    have : (i : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by exact_mod_cast h2
    have hc : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      have h2n : (2 : ℕ) ≤ n := hn
      push_cast [Nat.cast_sub h2n]
      ring
    linarith [hc ▸ this]
  set β : ℝ := 1 / (2 * (n : ℝ)) * Real.pi with hβ
  set α : ℝ := (2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi with hα
  have hpi := Real.pi_pos
  have hβpos : 0 < β := by rw [hβ]; positivity
  have hβα : β < α := by
    rw [hβ, hα, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_lt_div_iff_of_pos_right (by positivity)]
    nlinarith
  have hαπ : α < Real.pi - β := by
    rw [hβ, hα]
    have hrw : Real.pi - 1 / (2 * (n : ℝ)) * Real.pi
        = (2 * (n : ℝ) - 1) / (2 * (n : ℝ)) * Real.pi := by
      field_simp
    rw [hrw, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_lt_div_iff_of_pos_right (by positivity)]
    nlinarith
  -- `cos` is strictly decreasing on `[0, π]`
  have hupper : Real.cos α < Real.cos β :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hβpos.le (by linarith [hβpos]) hβα
  have hlower : -Real.cos β < Real.cos α := by
    have hcpi : Real.cos (Real.pi - β) = -Real.cos β := Real.cos_pi_sub β
    have : Real.cos (Real.pi - β) < Real.cos α :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [hβpos]) (by linarith [hβpos]) hαπ
    rwa [hcpi] at this
  rw [abs_lt]
  exact ⟨hlower, hupper⟩

/-- **The mass at the outer nodes.**  Exactly the ceiling, so the bound is attained. -/
theorem outer_node_mass {n : ℕ} (hn : 2 ≤ n) :
    ∑ i ∈ ({0, n - 1} : Finset ℕ),
        (2 / (n : ℝ)) * (1 - Real.cos ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi) ^ 2)
      = (4 / (n : ℝ)) * Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2 := by
  have hne : (0 : ℕ) ≠ n - 1 := by omega
  rw [Finset.sum_pair hne]
  have hn0 : 0 < n := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : (1 : ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub this]; ring
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hc0 : (2 * ((0 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi
      = 1 / (2 * (n : ℝ)) * Real.pi := by norm_num
  have hcn : (2 * ((n - 1 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi
      = Real.pi - 1 / (2 * (n : ℝ)) * Real.pi := by
    rw [hcast]; field_simp; ring
  rw [hc0, hcn, Real.cos_pi_sub]
  have hsin : Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2
      = 1 - Real.cos (1 / (2 * (n : ℝ)) * Real.pi) ^ 2 := by
    have := Real.sin_sq_add_cos_sq (1 / (2 * (n : ℝ)) * Real.pi); linarith
  rw [hsin, neg_pow, neg_one_pow_two, one_mul]
  ring


/-! ## The degree-four analysis is closed

The shifted quartic of `QuarticMajorant` **attains** the ceiling, at the natural scale.  Taking
`t = cos(π/8)` — the outermost node of the `n = 4` rule — and `s = cos(3π/8)` — the interior node,
where the majorant is forced to have a double zero — the constant term is exactly `sin²(π/8)`.

So at degree four the upper and lower bounds meet: `sin²(π/8) = (2−√2)/4 ≈ 0.1464` is both
achievable and unimprovable.  The remaining factor of `6` against the true Sato--Tate density is
therefore pure information loss, with no slack anywhere.

**The general principle** (proved here only at `n = 4`; the mechanism is degree-independent).  At
`t = cos(π/2n)` the extremal majorant is

  `P = ∏_{interior nodes xᵢ > 0} ((x² − xᵢ²)/(t² − xᵢ²))²`,

of degree `2n − 4 ≤ 2n − 3`.  It is nonnegative, equals `1` at the two outer nodes `±t`, and
**vanishes at every interior node** — so `satoTate_quadrature` evaluates its integral as the outer
nodes' weight alone, which is exactly `majorant_lower_bound`'s value.  No radical arithmetic is
involved: the quadrature does the whole computation.

Confirmed numerically at `n = 6` (degree eight, the degree the corpus's cited rank-nine record
reaches): with `t = cos(π/12)`, `s = cos(π/4)`, `u = cos(5π/12)` the octic constant term is
`0.0446581987385…`, agreeing with `(4/6)·sin²(π/12)` to machine precision. -/

theorem quartic_majorant_attains_ceiling :
    (1 / 8 - Real.cos (3 * Real.pi / 8) ^ 2 / 2 + Real.cos (3 * Real.pi / 8) ^ 4)
        / (Real.cos (1 / 8 * Real.pi) ^ 2 - Real.cos (3 * Real.pi / 8) ^ 2) ^ 2
      = Real.sin (1 / 8 * Real.pi) ^ 2 := by
  have hpi8 : (1 : ℝ) / 8 * Real.pi = Real.pi / 8 := by ring
  have hd : Real.cos (3 * Real.pi / 8) = Real.sin (Real.pi / 8) := by
    rw [show (3 * Real.pi / 8) = Real.pi / 2 - Real.pi / 8 by ring, Real.cos_pi_div_two_sub]
  have h2 : Real.cos (2 * (Real.pi / 8)) = 1 - 2 * Real.sin (Real.pi / 8) ^ 2 := by
    rw [Real.cos_two_mul, Real.cos_sq']
    ring
  rw [show (2 : ℝ) * (Real.pi / 8) = Real.pi / 4 by ring, Real.cos_pi_div_four] at h2
  have hs2 : Real.sin (Real.pi / 8) ^ 2 = (2 - Real.sqrt 2) / 4 := by linarith
  have hc2 : Real.cos (Real.pi / 8) ^ 2 = (2 + Real.sqrt 2) / 4 := by
    have := Real.sin_sq_add_cos_sq (Real.pi / 8)
    linarith [hs2]
  have hroot : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [hpi8, hd, hs2, hc2]
  have hden : ((2 + Real.sqrt 2) / 4 - (2 - Real.sqrt 2) / 4) ^ 2 = 1 / 2 := by
    have : ((2 + Real.sqrt 2) / 4 - (2 - Real.sqrt 2) / 4) = Real.sqrt 2 / 2 := by ring
    rw [this]
    field_simp
    linarith [hroot]
  rw [hden]
  field_simp
  nlinarith [hroot]


/-! ## The sharpness criterion, at every degree

The dual of `majorant_lower_bound`: a majorant **attains** the ceiling exactly when it vanishes at
every interior node.  No construction and no radical arithmetic — the quadrature evaluates the
integral, and the interior terms drop out. -/

theorem majorant_attains_of_vanishing {n : ℕ} (hn : 2 ≤ n) {P : ℝ[X]}
    (hdeg : (P * (1 - X ^ 2)).degree < 2 * (n : WithBot ℕ))
    (hout : P.eval (Real.cos ((2 * ((0 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi)) = 1)
    (hout' : P.eval
      (Real.cos ((2 * ((n - 1 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi)) = 1)
    (hint : ∀ i : ℕ, 1 ≤ i → i ≤ n - 2 →
      P.eval (Real.cos ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi)) = 0) :
    (∫ θ in (0:ℝ)..Real.pi, P.eval (Real.cos θ) * Real.sin θ ^ 2)
      = (2 * Real.pi / n) * Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2 := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
  rw [satoTate_quadrature hn0.ne' hdeg, sumZeroes]
  set Q : ℕ → ℝ := fun i =>
    ((P * (1 - X ^ 2)).eval (Real.cos ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi))) with hQ
  -- interior terms vanish
  have hsub : ({0, n - 1} : Finset ℕ) ⊆ Finset.range n := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  have hzero : ∀ i ∈ Finset.range n, i ∉ ({0, n - 1} : Finset ℕ) → Q i = 0 := by
    intro i hi hni
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hni
    rw [hQ]
    simp only [Polynomial.eval_mul]
    rw [hint i (by omega) (by omega)]
    ring
  have hcollect : ∑ i ∈ Finset.range n, Q i = Q 0 + Q (n - 1) := by
    rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (by omega : (0:ℕ) ≠ n - 1)]
  -- the two outer terms
  have hsin : Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2
      = 1 - Real.cos (1 / (2 * (n : ℝ)) * Real.pi) ^ 2 := by
    have := Real.sin_sq_add_cos_sq (1 / (2 * (n : ℝ)) * Real.pi); linarith
  have hc0 : (2 * ((0 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi
      = 1 / (2 * (n : ℝ)) * Real.pi := by norm_num
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h1n : (1 : ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub h1n]; ring
  have hcn : (2 * ((n - 1 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi
      = Real.pi - 1 / (2 * (n : ℝ)) * Real.pi := by
    rw [hcast]; field_simp; ring
  have hQ0 : Q 0 = 1 - Real.cos (1 / (2 * (n : ℝ)) * Real.pi) ^ 2 := by
    rw [hQ]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [hout, one_mul, hc0]
  have hQn : Q (n - 1) = 1 - Real.cos (1 / (2 * (n : ℝ)) * Real.pi) ^ 2 := by
    rw [hQ]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [hout', one_mul, hcn, Real.cos_pi_sub, neg_pow, neg_one_pow_two, one_mul]
  rw [hcollect, hQ0, hQn, hsin]
  field_simp
  ring


/-! ## Attainment at degree eight

The degree the corpus's cited rank-nine record reaches.  The majorant is even in `x`, with double
zeros at the two interior node levels `cos(π/4)` and `cos(5π/12)`, normalised to `1` at the outer
node `cos(π/12)`.  Evenness makes both outer nodes and all four interior nodes immediate. -/

/-- The degree-eight extremal majorant attains the `n = 6` ceiling. -/
theorem octic_attains_ceiling
    (hD : ((Real.cos (1 / 12 * Real.pi) ^ 2 - Real.cos (1 / 4 * Real.pi) ^ 2) *
      (Real.cos (1 / 12 * Real.pi) ^ 2 - Real.cos (5 / 12 * Real.pi) ^ 2)) ≠ 0) :
    (∫ θ in (0:ℝ)..Real.pi,
        (Polynomial.C (((Real.cos (1 / 12 * Real.pi) ^ 2 - Real.cos (1 / 4 * Real.pi) ^ 2) *
            (Real.cos (1 / 12 * Real.pi) ^ 2 - Real.cos (5 / 12 * Real.pi) ^ 2)) ^ 2)⁻¹ *
          ((X ^ 2 - Polynomial.C (Real.cos (1 / 4 * Real.pi) ^ 2)) *
            (X ^ 2 - Polynomial.C (Real.cos (5 / 12 * Real.pi) ^ 2))) ^ 2).eval (Real.cos θ)
          * Real.sin θ ^ 2)
      = (2 * Real.pi / 6) * Real.sin (1 / (2 * (6 : ℝ)) * Real.pi) ^ 2 := by
  set a := Real.cos (1 / 4 * Real.pi) with ha
  set b := Real.cos (5 / 12 * Real.pi) with hb
  set c := Real.cos (1 / 12 * Real.pi) with hc
  set K : ℝ := (((c ^ 2 - a ^ 2) * (c ^ 2 - b ^ 2)) ^ 2)⁻¹ with hK
  set P : ℝ[X] := Polynomial.C K *
    ((X ^ 2 - Polynomial.C (a ^ 2)) * (X ^ 2 - Polynomial.C (b ^ 2))) ^ 2 with hP
  have heval : ∀ x : ℝ, P.eval x = K * ((x ^ 2 - a ^ 2) * (x ^ 2 - b ^ 2)) ^ 2 := by
    intro x; rw [hP]; simp
  have hone : K * ((c ^ 2 - a ^ 2) * (c ^ 2 - b ^ 2)) ^ 2 = 1 := by
    rw [hK]; exact inv_mul_cancel₀ (pow_ne_zero 2 hD)
  have hrefl : ∀ k : ℝ, Real.cos (Real.pi - k) = -Real.cos k := fun k => Real.cos_pi_sub k
  refine majorant_attains_of_vanishing (n := 6) (by norm_num) ?_ ?_ ?_ ?_
  · rw [hP]
    have hdeg : ((Polynomial.C K *
        ((X ^ 2 - Polynomial.C (a ^ 2)) * (X ^ 2 - Polynomial.C (b ^ 2))) ^ 2)
        * (1 - X ^ 2)).degree ≤ 10 := by compute_degree
    refine lt_of_le_of_lt hdeg ?_
    norm_num
  · norm_num
    rw [heval, ← hc, hone]
  · norm_num
    rw [show (11 : ℝ) / 12 * Real.pi = Real.pi - 1 / 12 * Real.pi by ring, hrefl, ← hc,
      heval]
    have : ((-c) ^ 2 - a ^ 2) * ((-c) ^ 2 - b ^ 2) = (c ^ 2 - a ^ 2) * (c ^ 2 - b ^ 2) := by
      ring
    rw [this, hone]
  · intro i h1 h2
    interval_cases i
    · norm_num
      rw [heval, ← ha]
      ring
    · norm_num
      rw [heval, ← hb]
      ring
    · norm_num
      rw [show (7 : ℝ) / 12 * Real.pi = Real.pi - 5 / 12 * Real.pi by ring, hrefl, ← hb,
        heval]
      ring
    · norm_num
      rw [show (3 : ℝ) / 4 * Real.pi = Real.pi - 1 / 4 * Real.pi by ring, hrefl, ← ha,
        heval]
      ring


/-! ## The extremal majorant at every node count

The construction, in general.  Taking the product of `X² − xᵢ²` over the interior indices — the
**even** form — makes everything free: it vanishes at every interior node, and since it depends on
`x` only through `x²` it takes the same value at both outer nodes `±cos(π/2n)`.  No reindexing
argument and no symmetry lemma is needed. -/

/-- The unnormalised extremal majorant: `∏ (X² − xᵢ²)` over the interior nodes. -/
noncomputable def extremalCore (n : ℕ) : ℝ[X] :=
  ∏ i ∈ Finset.Ico 1 (n - 1), (X ^ 2 - Polynomial.C (stNode n i ^ 2))

theorem extremalCore_eval (n : ℕ) (x : ℝ) :
    (extremalCore n).eval x = ∏ i ∈ Finset.Ico 1 (n - 1), (x ^ 2 - stNode n i ^ 2) := by
  rw [extremalCore, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun i _ => by simp

theorem extremalCore_degree (n : ℕ) :
    (extremalCore n).degree = ((2 * (n - 2) : ℕ) : WithBot ℕ) := by
  rw [extremalCore, Polynomial.degree_prod]
  have hfac : ∀ i ∈ Finset.Ico 1 (n - 1),
      (X ^ 2 - Polynomial.C (stNode n i ^ 2)).degree = ((2 : ℕ) : WithBot ℕ) := by
    intro i _
    exact Polynomial.degree_X_pow_sub_C (by norm_num) _
  rw [Finset.sum_congr rfl hfac, Finset.sum_const, Nat.card_Ico]
  have hc : (n - 1 - 1) = n - 2 := by omega
  rw [hc]
  simp [nsmul_eq_mul]
  norm_cast
  ring

/-- **The extremal majorant vanishes at every interior node.** -/
theorem extremalCore_interior {n j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ n - 2) :
    (extremalCore n).eval (stNode n j) = 0 := by
  rw [extremalCore_eval]
  refine Finset.prod_eq_zero (i := j) ?_ ?_
  · simp only [Finset.mem_Ico]; omega
  · ring

/-- **It takes the same value at both outer nodes**, because it is even. -/
theorem extremalCore_outer (n : ℕ) :
    (extremalCore n).eval (-stNode n 0) = (extremalCore n).eval (stNode n 0) := by
  rw [extremalCore_eval, extremalCore_eval]
  exact Finset.prod_congr rfl fun i _ => by ring


theorem extremalCore_eval_outer_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < (extremalCore n).eval (stNode n 0) := by
  rw [extremalCore_eval]
  refine Finset.prod_pos fun i hi => ?_
  simp only [Finset.mem_Ico] at hi
  have hlt := interior_node_lt hn hi.1 (by omega)
  have h0 : stNode n 0 = Real.cos (1 / (2 * (n : ℝ)) * Real.pi) := by
    rw [stNode, stAngle]; norm_num
  have hi' : |stNode n i| < stNode n 0 := by
    rw [h0, stNode, stAngle]; exact hlt
  have hnn : 0 ≤ stNode n 0 := le_trans (abs_nonneg _) hi'.le
  nlinarith [abs_nonneg (stNode n i), sq_abs (stNode n i), hi', hnn]

/-- **The extremal majorant**, normalised to `1` at the outer nodes. -/
noncomputable def extremalMajorant (n : ℕ) : ℝ[X] :=
  Polynomial.C ((extremalCore n).eval (stNode n 0))⁻¹ * extremalCore n

/-- **★ The ceiling is attained at every node count.**  Together with `majorant_lower_bound`, the
value `(4/n)·sin²(π/2n)` is exactly the best a degree-`≤ 2n−3` nonnegative majorant can do. -/
theorem extremalMajorant_attains {n : ℕ} (hn : 2 ≤ n) :
    (∫ θ in (0:ℝ)..Real.pi,
        (extremalMajorant n).eval (Real.cos θ) * Real.sin θ ^ 2)
      = (2 * Real.pi / n) * Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2 := by
  have hn0 : 0 < n := by omega
  have hpos := extremalCore_eval_outer_pos hn
  have hnode0 : Real.cos ((2 * ((0 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi) = stNode n 0 := by
    rw [stNode, stAngle]
  have hnodeN : Real.cos ((2 * ((n - 1 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi)
      = stNode n (n - 1) := by
    rw [stNode, stAngle]
  have heval : ∀ x : ℝ, (extremalMajorant n).eval x
      = ((extremalCore n).eval (stNode n 0))⁻¹ * (extremalCore n).eval x := by
    intro x; rw [extremalMajorant]; simp
  refine majorant_attains_of_vanishing hn ?_ ?_ ?_ ?_
  · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
    have hc : (extremalMajorant n).degree ≤ ((2 * (n - 2) : ℕ) : WithBot ℕ) := by
      rw [extremalMajorant]
      refine le_trans (Polynomial.degree_mul_le _ _) ?_
      have hCle : (Polynomial.C ((extremalCore n).eval (stNode n 0))⁻¹).degree ≤ 0 :=
        Polynomial.degree_C_le
      rw [extremalCore_degree]
      calc (Polynomial.C ((extremalCore n).eval (stNode n 0))⁻¹).degree
            + ((2 * (n - 2) : ℕ) : WithBot ℕ)
          ≤ 0 + ((2 * (n - 2) : ℕ) : WithBot ℕ) := add_le_add hCle (le_refl _)
        _ = ((2 * (n - 2) : ℕ) : WithBot ℕ) := by simp
    have hq : ((1 : ℝ[X]) - X ^ 2).degree ≤ ((2 : ℕ) : WithBot ℕ) := by
      have : ((1 : ℝ[X]) - X ^ 2).degree = (2 : WithBot ℕ) := by compute_degree!
      rw [this]
      norm_num
    refine lt_of_le_of_lt (add_le_add hc hq) ?_
    have : ((2 * (n - 2) : ℕ) : WithBot ℕ) + ((2 : ℕ) : WithBot ℕ)
        = ((2 * (n - 2) + 2 : ℕ) : WithBot ℕ) := by push_cast; ring
    rw [this]
    have h2 : 2 * (n - 2) + 2 < 2 * n := by omega
    exact_mod_cast h2
  · rw [hnode0, heval, inv_mul_cancel₀ hpos.ne']
  · rw [hnodeN, heval]
    have hrefl : stNode n (n - 1) = -stNode n 0 := by
      have := stNode_reflect (n := n) (i := 0) hn0
      simpa using this
    rw [hrefl, extremalCore_outer, inv_mul_cancel₀ hpos.ne']
  · intro i h1 h2
    have hnode : Real.cos ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi) = stNode n i := by
      rw [stNode, stAngle]
    rw [hnode, heval, extremalCore_interior h1 h2, mul_zero]


/-! ## The extremal polynomial really is a majorant

Each factor `x² − xᵢ²` is increasing in `x²`, and every interior node satisfies `|xᵢ| < cos(π/2n)`,
so on `|x| ≥ cos(π/2n)` the whole product dominates its value at the outer node — which is exactly
where it was normalised to `1`. -/

theorem extremalCore_le_of_outer {n : ℕ} (hn : 2 ≤ n) {x : ℝ}
    (hx : stNode n 0 ≤ |x|) :
    (extremalCore n).eval (stNode n 0) ≤ (extremalCore n).eval x := by
  have h0 : stNode n 0 = Real.cos (1 / (2 * (n : ℝ)) * Real.pi) := by
    rw [stNode, stAngle]; norm_num
  have hxsq : stNode n 0 ^ 2 ≤ x ^ 2 := by
    have hnn : 0 ≤ stNode n 0 := by
      rw [h0]
      refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
      · have hp : (0:ℝ) < 1 / (2 * (n : ℝ)) * Real.pi := by positivity
        linarith [Real.pi_pos]
      · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
        nlinarith [Real.pi_pos, hn1]
    nlinarith [abs_nonneg x, sq_abs x, hx, hnn]
  rw [extremalCore_eval, extremalCore_eval]
  refine Finset.prod_le_prod ?_ ?_
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    have hlt := interior_node_lt hn hi.1 (by omega)
    have habs : |stNode n i| < stNode n 0 := by
      rw [h0, stNode, stAngle]; exact hlt
    nlinarith [abs_nonneg (stNode n i), sq_abs (stNode n i), habs,
      le_trans (abs_nonneg (stNode n i)) habs.le]
  · intro i _
    linarith

/-- **The extremal polynomial majorises the indicator** at `t = cos(π/2n)`. -/
theorem extremalMajorant_ge_one {n : ℕ} (hn : 2 ≤ n) {x : ℝ}
    (hx : stNode n 0 ≤ |x|) : 1 ≤ (extremalMajorant n).eval x := by
  have hpos := extremalCore_eval_outer_pos hn
  have hle := extremalCore_le_of_outer hn hx
  rw [extremalMajorant]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  calc (1 : ℝ) = ((extremalCore n).eval (stNode n 0))⁻¹ *
        (extremalCore n).eval (stNode n 0) := (inv_mul_cancel₀ hpos.ne').symm
    _ ≤ ((extremalCore n).eval (stNode n 0))⁻¹ * (extremalCore n).eval x := by
        exact mul_le_mul_of_nonneg_left hle (by positivity)


/-! ## The lower bound needs only node data

`majorant_lower_bound` assumes `P ≥ 0` on all of `[−1,1]` and `P ≥ 1` on `|x| ≥ t`, but its proof
touches `P` only at the `n` quadrature nodes.  Weakening the hypotheses accordingly strengthens the
theorem — and makes it directly applicable to `extremalMajorant`, whose nonnegativity at the nodes
is immediate (zero at the interior ones, positive at the outer ones) even though nonnegativity on
all of `[−1,1]` would need a pairing argument. -/

theorem majorant_lower_bound_nodes {n : ℕ} (hn : 2 ≤ n) {P : ℝ[X]}
    (hdeg : (P * (1 - X ^ 2)).degree < 2 * (n : WithBot ℕ))
    (hnn : ∀ i : ℕ, i < n →
      0 ≤ P.eval (Real.cos ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi)))
    (hout : 1 ≤ P.eval ((2 * ((0 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi |> Real.cos))
    (hout' : 1 ≤ P.eval
      (Real.cos ((2 * ((n - 1 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi))) :
    (2 * Real.pi / n) * Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2
      ≤ ∫ θ in (0:ℝ)..Real.pi, P.eval (Real.cos θ) * Real.sin θ ^ 2 := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
  rw [satoTate_quadrature hn0.ne' hdeg, sumZeroes]
  set Q : ℕ → ℝ := fun i =>
    ((P * (1 - X ^ 2)).eval (Real.cos ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi))) with hQ
  have hQnn : ∀ i : ℕ, i < n → 0 ≤ Q i := by
    intro i hi
    rw [hQ]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_pow, Polynomial.eval_X]
    refine mul_nonneg (hnn i hi) ?_
    nlinarith [Real.sin_sq_add_cos_sq ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi),
      sq_nonneg (Real.sin ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi))]
  have hc0 : (2 * ((0 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi
      = 1 / (2 * (n : ℝ)) * Real.pi := by norm_num
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h1n : (1 : ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub h1n]; ring
  have hcn : (2 * ((n - 1 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi
      = Real.pi - 1 / (2 * (n : ℝ)) * Real.pi := by
    rw [hcast]; field_simp; ring
  have hsin : Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2
      = 1 - Real.cos (1 / (2 * (n : ℝ)) * Real.pi) ^ 2 := by
    have := Real.sin_sq_add_cos_sq (1 / (2 * (n : ℝ)) * Real.pi); linarith
  have h1c : (0:ℝ) ≤ 1 - Real.cos (1 / (2 * (n : ℝ)) * Real.pi) ^ 2 := by
    rw [← hsin]; positivity
  have hQ0 : Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2 ≤ Q 0 := by
    rw [hQ]
    simp only [hc0, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [hsin]
    rw [hc0] at hout
    nlinarith [hout, h1c]
  have hQn : Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2 ≤ Q (n - 1) := by
    rw [hQ]
    simp only [hcn, Real.cos_pi_sub, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hcn, Real.cos_pi_sub] at hout'
    rw [hsin, neg_pow, neg_one_pow_two, one_mul]
    nlinarith [hout', h1c]
  have hsub : ({0, n - 1} : Finset ℕ) ⊆ Finset.range n := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  have hcollect : Q 0 + Q (n - 1) ≤ ∑ i ∈ Finset.range n, Q i := by
    rw [← Finset.sum_pair (by omega : (0:ℕ) ≠ n - 1)]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i hi _ =>
      hQnn i (Finset.mem_range.mp hi)
  have hkey : 2 * Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2
      ≤ ∑ i ∈ Finset.range n, Q i := by linarith [hQ0, hQn, hcollect]
  have hpi : 0 < Real.pi / (n : ℝ) := by positivity
  calc (2 * Real.pi / (n : ℝ)) * Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2
      = (Real.pi / (n : ℝ)) * (2 * Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2) := by ring
    _ ≤ (Real.pi / (n : ℝ)) * ∑ i ∈ Finset.range n, Q i :=
        mul_le_mul_of_nonneg_left hkey hpi.le


/-- The extremal majorant is nonnegative at every node: zero at the interior ones, `1` at the outer
ones. -/
theorem extremalMajorant_node_nonneg {n : ℕ} (hn : 2 ≤ n) (i : ℕ) (hi : i < n) :
    0 ≤ (extremalMajorant n).eval
      (Real.cos ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi)) := by
  have hpos := extremalCore_eval_outer_pos hn
  have heval : ∀ x : ℝ, (extremalMajorant n).eval x
      = ((extremalCore n).eval (stNode n 0))⁻¹ * (extremalCore n).eval x := by
    intro x; rw [extremalMajorant]; simp
  have hnode : Real.cos ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi) = stNode n i := by
    rw [stNode, stAngle]
  rw [hnode, heval]
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · rw [inv_mul_cancel₀ hpos.ne']; norm_num
  · rcases Nat.lt_or_ge i (n - 1) with hlt | hge
    · rw [extremalCore_interior hipos (by omega), mul_zero]
    · have hieq : i = n - 1 := by omega
      subst hieq
      have hrefl : stNode n (n - 1) = -stNode n 0 := by
        have := stNode_reflect (n := n) (i := 0) (by omega)
        simpa using this
      rw [hrefl, extremalCore_outer, inv_mul_cancel₀ hpos.ne']
      norm_num


/-! ## The capstone: the ceiling is the least attainable value

Both directions in one statement. -/

theorem stNode_zero_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ stNode n 0 := by
  have h0 : stNode n 0 = Real.cos (1 / (2 * (n : ℝ)) * Real.pi) := by
    rw [stNode, stAngle]; norm_num
  rw [h0]
  refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
  · have hp : (0:ℝ) < 1 / (2 * (n : ℝ)) * Real.pi := by
      have : (0:ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      positivity
    linarith [Real.pi_pos]
  · have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    nlinarith [Real.pi_pos, hn1]

theorem extremalMajorant_degree_bound {n : ℕ} (hn : 2 ≤ n) :
    ((extremalMajorant n) * (1 - X ^ 2)).degree < 2 * (n : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
  have hc : (extremalMajorant n).degree ≤ ((2 * (n - 2) : ℕ) : WithBot ℕ) := by
    rw [extremalMajorant]
    refine le_trans (Polynomial.degree_mul_le _ _) ?_
    have hCle : (Polynomial.C ((extremalCore n).eval (stNode n 0))⁻¹).degree ≤ 0 :=
      Polynomial.degree_C_le
    rw [extremalCore_degree]
    calc (Polynomial.C ((extremalCore n).eval (stNode n 0))⁻¹).degree
          + ((2 * (n - 2) : ℕ) : WithBot ℕ)
        ≤ 0 + ((2 * (n - 2) : ℕ) : WithBot ℕ) := add_le_add hCle (le_refl _)
      _ = ((2 * (n - 2) : ℕ) : WithBot ℕ) := by simp
  have hq : ((1 : ℝ[X]) - X ^ 2).degree ≤ ((2 : ℕ) : WithBot ℕ) := by
    have hdd : ((1 : ℝ[X]) - X ^ 2).degree = (2 : WithBot ℕ) := by compute_degree!
    rw [hdd]; norm_num
  refine lt_of_le_of_lt (add_le_add hc hq) ?_
  have hadd : ((2 * (n - 2) : ℕ) : WithBot ℕ) + ((2 : ℕ) : WithBot ℕ)
      = ((2 * (n - 2) + 2 : ℕ) : WithBot ℕ) := by push_cast; ring
  rw [hadd]
  have h2 : 2 * (n - 2) + 2 < 2 * n := by omega
  exact_mod_cast h2

/-- **★ The ceiling is the least attainable value.**  Over all polynomials of degree `≤ 2n−3` that
are nonnegative at the quadrature nodes and majorise the indicator at the outer ones, the smallest
Sato--Tate integral is exactly `(2π/n)·sin²(π/2n)` — and it is achieved. -/
theorem majorant_value_isLeast {n : ℕ} (hn : 2 ≤ n) :
    IsLeast
      {v : ℝ | ∃ P : ℝ[X],
        (P * (1 - X ^ 2)).degree < 2 * (n : WithBot ℕ) ∧
        (∀ i : ℕ, i < n →
          0 ≤ P.eval (Real.cos ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi))) ∧
        1 ≤ P.eval (Real.cos ((2 * ((0 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi)) ∧
        1 ≤ P.eval (Real.cos ((2 * ((n - 1 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi)) ∧
        (∫ θ in (0:ℝ)..Real.pi, P.eval (Real.cos θ) * Real.sin θ ^ 2) = v}
      ((2 * Real.pi / n) * Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2) := by
  constructor
  · refine ⟨extremalMajorant n, extremalMajorant_degree_bound hn,
      fun i hi => extremalMajorant_node_nonneg hn i hi, ?_, ?_,
      extremalMajorant_attains hn⟩
    · have hnode : Real.cos ((2 * ((0 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi)
          = stNode n 0 := by rw [stNode, stAngle]
      rw [hnode]
      exact extremalMajorant_ge_one hn (by rw [abs_of_nonneg (stNode_zero_nonneg hn)])
    · have hnode : Real.cos ((2 * ((n - 1 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) * Real.pi)
          = stNode n (n - 1) := by rw [stNode, stAngle]
      have hrefl : stNode n (n - 1) = -stNode n 0 := by
        have := stNode_reflect (n := n) (i := 0) (by omega)
        simpa using this
      rw [hnode, hrefl]
      refine extremalMajorant_ge_one hn ?_
      rw [abs_neg, abs_of_nonneg (stNode_zero_nonneg hn)]
  · rintro v ⟨P, hdeg, hnn, hout, hout', rfl⟩
    exact majorant_lower_bound_nodes hn hdeg hnn hout hout'


/-! ## The extremal core is a perfect square

`∏(x² − xᵢ²) = ∏(x − xᵢ)·∏(x + xᵢ)`, and the involution `i ↦ n−1−i` (which sends `xᵢ` to `−xᵢ`)
turns the second product into the first.  So the whole thing is a square — global nonnegativity
with no parity split and no Chebyshev factorisation. -/

theorem prod_add_eq_prod_sub {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    ∏ i ∈ Finset.Ico 1 (n - 1), (x + stNode n i)
      = ∏ i ∈ Finset.Ico 1 (n - 1), (x - stNode n i) := by
  refine Finset.prod_nbij' (fun i => n - 1 - i) (fun i => n - 1 - i) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_Ico] at ha ⊢
    omega
  · intro b hb
    simp only [Finset.mem_Ico] at hb ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Ico] at ha
    omega
  · intro b hb
    simp only [Finset.mem_Ico] at hb
    omega
  · intro a ha
    simp only [Finset.mem_Ico] at ha
    rw [stNode_reflect (by omega : a < n)]
    ring

/-- **The extremal core is a perfect square**, hence nonnegative everywhere. -/
theorem extremalCore_eval_eq_sq {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    (extremalCore n).eval x = (∏ i ∈ Finset.Ico 1 (n - 1), (x - stNode n i)) ^ 2 := by
  rw [extremalCore_eval]
  have hfac : ∀ i ∈ Finset.Ico 1 (n - 1),
      x ^ 2 - stNode n i ^ 2 = (x - stNode n i) * (x + stNode n i) := fun i _ => by ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, prod_add_eq_prod_sub hn, sq]

theorem extremalCore_nonneg {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    0 ≤ (extremalCore n).eval x := by
  rw [extremalCore_eval_eq_sq hn]
  exact sq_nonneg _

/-- **The extremal majorant is nonnegative everywhere** — so it is a genuine majorant, and
`majorant_value_isLeast` is the true LP value, not merely the relaxed one. -/
theorem extremalMajorant_nonneg {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    0 ≤ (extremalMajorant n).eval x := by
  have hpos := extremalCore_eval_outer_pos hn
  rw [extremalMajorant]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  exact mul_nonneg (by positivity) (extremalCore_nonneg hn x)


/-- **★★ The true LP value.**  Over all genuine majorants — nonnegative on `[−1,1]`, at least `1`
on `|x| ≥ cos(π/2n)`, of degree `≤ 2n−3` — the least Sato--Tate integral is exactly
`(2π/n)·sin²(π/2n)`, and `extremalMajorant n` achieves it.

This is the statement with no caveats: not the relaxed node-hypothesis version, and not merely a
bound.  Normalised, the value is `(4/n)·sin²(π/2n) ≈ π²/n³`, against a true Sato--Tate density of
`π²/6n³` — so the factor of six is exactly what finitely many symmetric-power moments cost, and no
choice of majorant at any degree recovers it. -/
theorem majorant_value_isLeast_genuine {n : ℕ} (hn : 2 ≤ n) :
    IsLeast
      {v : ℝ | ∃ P : ℝ[X],
        (P * (1 - X ^ 2)).degree < 2 * (n : WithBot ℕ) ∧
        (∀ x : ℝ, |x| ≤ 1 → 0 ≤ P.eval x) ∧
        (∀ x : ℝ, |x| ≤ 1 → Real.cos (1 / (2 * (n : ℝ)) * Real.pi) ≤ |x| → 1 ≤ P.eval x) ∧
        (∫ θ in (0:ℝ)..Real.pi, P.eval (Real.cos θ) * Real.sin θ ^ 2) = v}
      ((2 * Real.pi / n) * Real.sin (1 / (2 * (n : ℝ)) * Real.pi) ^ 2) := by
  have h0 : stNode n 0 = Real.cos (1 / (2 * (n : ℝ)) * Real.pi) := by
    rw [stNode, stAngle]; norm_num
  constructor
  · refine ⟨extremalMajorant n, extremalMajorant_degree_bound hn,
      fun x _ => extremalMajorant_nonneg hn x, ?_, extremalMajorant_attains hn⟩
    intro x _ hx
    exact extremalMajorant_ge_one hn (by rw [h0]; exact hx)
  · rintro v ⟨P, hdeg, hnn, hmaj, rfl⟩
    exact majorant_lower_bound hn (le_refl _) hdeg hnn hmaj

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.quartic_majorant_lower_bound
#print axioms CriticalLinePhasor.ThreeDConverse.majorant_lower_bound
#print axioms CriticalLinePhasor.ThreeDConverse.interior_node_lt
#print axioms CriticalLinePhasor.ThreeDConverse.outer_node_mass
#print axioms CriticalLinePhasor.ThreeDConverse.quartic_majorant_attains_ceiling
#print axioms CriticalLinePhasor.ThreeDConverse.majorant_attains_of_vanishing
#print axioms CriticalLinePhasor.ThreeDConverse.octic_attains_ceiling
#print axioms CriticalLinePhasor.ThreeDConverse.extremalCore_degree
#print axioms CriticalLinePhasor.ThreeDConverse.extremalCore_interior
#print axioms CriticalLinePhasor.ThreeDConverse.extremalMajorant_attains
#print axioms CriticalLinePhasor.ThreeDConverse.extremalMajorant_ge_one
#print axioms CriticalLinePhasor.ThreeDConverse.majorant_lower_bound_nodes
#print axioms CriticalLinePhasor.ThreeDConverse.extremalMajorant_node_nonneg
#print axioms CriticalLinePhasor.ThreeDConverse.majorant_value_isLeast
#print axioms CriticalLinePhasor.ThreeDConverse.extremalMajorant_nonneg
#print axioms CriticalLinePhasor.ThreeDConverse.majorant_value_isLeast_genuine
