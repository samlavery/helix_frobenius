import RequestProject.MajorantDensity

/-!
# A density bound that does not assume Ramanujan

The majorant bounds of `QuarticMajorant` are stated for an `ArithmeticSatakePrimeFamily`, and
`ArithmeticSatakeTowerAtPrime.radius_one` forces `‖value‖ = 1` — so forming the family already
presupposes Ramanujan--Petersson, which for a Maass form is open.

This file gives a bound that does not.  It takes only the **second moment**

  **`(1/(n+1))·∑_{i≤n} a(p_i)² → 1`,**

which for a Maass form is the Rankin--Selberg statement supplied by `Sym²` automorphy
(Gelbart--Jacquet) — unconditional, and in particular not requiring `|a_p| ≤ 2`.  Chebyshev's
inequality then gives

  **`density{p : |a_p| ≥ λ} ≤ 1/λ²`.**

The coefficients are an arbitrary real sequence: nothing here forces the Satake parameters onto the
unit circle, so the statement survives whatever Kim--Sarnak-type deviation the form may have.

**The trade.**  At `λ = 1.8` (which in the tempered normalisation is `|cos θ_p| ≥ 0.9`) this gives
`0.309`, against the quartic majorant's `0.166` and the true Sato--Tate value `0.037`.  So it is
about twice as weak — and it is the price of dropping an open hypothesis, which is worth paying
when the alternative is a bound that presupposes one of the two things being sought.

**Scope.**  The second moment is a hypothesis, cited not proved.  Nothing about ranks beyond two,
and nothing about equidistribution, is claimed.
-/

open Filter Topology

namespace CriticalLinePhasor.PartialSerre

open CriticalLinePhasor.SatoTateCarrier3D

/-- Coefficients with the Rankin--Selberg second moment, and no unitarity assumption. -/
structure SecondMomentInput where
  a : Nat.Primes → ℝ
  second_moment :
    Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ)) *
      ∑ i : Fin (n + 1), (a (nthPrime i)) ^ 2) atTop (𝓝 1)

/-- **Chebyshev density bound, free of Ramanujan.**  The proportion of primes with `|a_p| ≥ λ` is
eventually below `1/λ² + ε`. -/
theorem secondMoment_density_bound (I : SecondMomentInput) {lam : ℝ} (hlam : 0 < lam)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), (if lam ≤ |I.a (nthPrime i)| then (1 : ℝ) else 0)
        < 1 / lam ^ 2 + ε := by
  have hl2 : (0:ℝ) < lam ^ 2 := by positivity
  -- the scaled second moment converges to `1/lam²`
  have hscaled : Tendsto (fun n : ℕ => (1 / lam ^ 2) *
      ((1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), (I.a (nthPrime i)) ^ 2)) atTop (𝓝 (1 / lam ^ 2)) := by
    have h := I.second_moment.const_mul (1 / lam ^ 2)
    rwa [mul_one] at h
  have hev : ∀ᶠ n : ℕ in atTop, (1 / lam ^ 2) *
      ((1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), (I.a (nthPrime i)) ^ 2) < 1 / lam ^ 2 + ε :=
    hscaled.eventually_lt_const (by linarith)
  filter_upwards [hev] with n hn
  refine lt_of_le_of_lt ?_ hn
  have hpos : (0:ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
  rw [← mul_assoc, mul_comm (1 / lam ^ 2), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hpos.le
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hcase : lam ≤ |I.a (nthPrime i)|
  · rw [if_pos hcase]
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hl2, one_mul]
    have h1 : lam ^ 2 ≤ |I.a (nthPrime i)| ^ 2 := by
      gcongr
    rwa [← abs_pow, abs_of_nonneg (by positivity)] at h1
  · rw [if_neg hcase]
    positivity


/-! ## Any even moment

The same argument at `a^{2m}`.  For a Maass form the `2m`-th moment is governed by the symmetric
powers up to rank `2m`, so `m = 2` is available from the Kim--Shahidi record — and it is the moment
statement, not a pointwise bound, so **temperedness is still not assumed**.

In the tempered normalisation `∫(2cos θ)⁴ dSTdθ = 2`, giving `density{|a_p| ≥ λ} ≤ 2/λ⁴`.  At
`λ = 1.8` that is `0.1905` — the same number as the *unshifted* quartic majorant, but with Ramanujan
dropped.  (The *shifted* quartic reaches `0.166`; a single moment is weaker than the optimal
majorant of the same degree, because it uses only the top coefficient.) -/

theorem moment_density_bound {a : Nat.Primes → ℝ} {m : ℕ} (hm : 1 ≤ m) {M : ℝ}
    (hmom : Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ)) *
      ∑ i : Fin (n + 1), (a (nthPrime i)) ^ (2 * m)) atTop (𝓝 M))
    {lam : ℝ} (hlam : 0 < lam) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), (if lam ≤ |a (nthPrime i)| then (1 : ℝ) else 0)
        < M / lam ^ (2 * m) + ε := by
  have hlam0 : (0:ℝ) ≤ lam := hlam.le
  have hl : (0:ℝ) < lam ^ (2 * m) := by positivity
  have hscaled : Tendsto (fun n : ℕ => (1 / lam ^ (2 * m)) *
      ((1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), (a (nthPrime i)) ^ (2 * m))) atTop
      (𝓝 (M / lam ^ (2 * m))) := by
    have h := hmom.const_mul (1 / lam ^ (2 * m))
    have heq : (1 / lam ^ (2 * m)) * M = M / lam ^ (2 * m) := by ring
    rwa [heq] at h
  have hev : ∀ᶠ n : ℕ in atTop, (1 / lam ^ (2 * m)) *
      ((1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), (a (nthPrime i)) ^ (2 * m)) < M / lam ^ (2 * m) + ε :=
    hscaled.eventually_lt_const (by linarith)
  filter_upwards [hev] with n hn
  refine lt_of_le_of_lt ?_ hn
  have hpos : (0:ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
  rw [← mul_assoc, mul_comm (1 / lam ^ (2 * m)), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hpos.le
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hcase : lam ≤ |a (nthPrime i)|
  · rw [if_pos hcase, one_div, inv_mul_eq_div, le_div_iff₀ hl, one_mul]
    have hnn' : (0:ℝ) ≤ (a (nthPrime i)) ^ (2 * m) := by
      rw [pow_mul]; exact pow_nonneg (sq_nonneg _) m
    have h1 : lam ^ (2 * m) ≤ |a (nthPrime i)| ^ (2 * m) := by gcongr
    rwa [← abs_pow, abs_of_nonneg hnn'] at h1
  · rw [if_neg hcase]
    have hnn : (0:ℝ) ≤ (a (nthPrime i)) ^ (2 * m) := by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) m
    have hinv : (0:ℝ) ≤ 1 / lam ^ (2 * m) := le_of_lt (by positivity)
    exact mul_nonneg hinv hnn


/-! ## The majorant method, without temperedness

A single moment uses only the top coefficient.  Using a whole polynomial in `a²` recovers the full
majorant method — and it still needs no unitarity, because a polynomial majorant that is
nonnegative on **all** of `ℝ` (not merely on `[−2,2]`) works whatever the Satake parameters do.

The shifted quartic `P(a) = (a² − σ²)²/(λ² − σ²)²` is such a majorant for every `0 ≤ σ < λ`, and its
value is `(M₄ − 2σ²M₂ + σ⁴)/(λ² − σ²)²`.  With the Rankin--Selberg values `M₂ = 1`, `M₄ = 2` —
both consequences of `Sym²`/`Sym⁴` automorphy, and both moment statements rather than pointwise
bounds — this gives `0.1662` at `λ = 1.8` (optimal `σ ≈ 0.744`), matching the best degree-four
majorant **with Ramanujan dropped**. -/

theorem poly_moment_density_bound {a : Nat.Primes → ℝ} {R : ℕ} {c M : ℕ → ℝ}
    (hmom : ∀ k, k ≤ R → Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ)) *
      ∑ i : Fin (n + 1), (a (nthPrime i)) ^ (2 * k)) atTop (𝓝 (M k)))
    {lam : ℝ} (hlam : 0 < lam)
    (hmaj : ∀ x : ℝ, lam ≤ |x| → 1 ≤ ∑ k ∈ Finset.range (R + 1), c k * x ^ (2 * k))
    (hnn : ∀ x : ℝ, 0 ≤ ∑ k ∈ Finset.range (R + 1), c k * x ^ (2 * k))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), (if lam ≤ |a (nthPrime i)| then (1 : ℝ) else 0)
        < (∑ k ∈ Finset.range (R + 1), c k * M k) + ε := by
  -- the combined moment converges
  have hcomb : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (R + 1), c k *
      ((1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), (a (nthPrime i)) ^ (2 * k))) atTop
      (𝓝 (∑ k ∈ Finset.range (R + 1), c k * M k)) := by
    refine tendsto_finset_sum _ fun k hk => ?_
    exact (hmom k (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).const_mul (c k)
  have hev : ∀ᶠ n : ℕ in atTop, (∑ k ∈ Finset.range (R + 1), c k *
      ((1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), (a (nthPrime i)) ^ (2 * k)))
      < (∑ k ∈ Finset.range (R + 1), c k * M k) + ε :=
    hcomb.eventually_lt_const (by linarith)
  filter_upwards [hev] with n hn
  refine lt_of_le_of_lt ?_ hn
  have hpos : (0:ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
  -- swap the two sums
  have hswap : (∑ k ∈ Finset.range (R + 1), c k *
      ((1 / ((n + 1 : ℕ) : ℝ)) * ∑ i : Fin (n + 1), (a (nthPrime i)) ^ (2 * k)))
      = (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), ∑ k ∈ Finset.range (R + 1),
          c k * (a (nthPrime i)) ^ (2 * k) := by
    calc (∑ k ∈ Finset.range (R + 1), c k *
        ((1 / ((n + 1 : ℕ) : ℝ)) * ∑ i : Fin (n + 1), (a (nthPrime i)) ^ (2 * k)))
        = ∑ k ∈ Finset.range (R + 1), ∑ i : Fin (n + 1),
            (1 / ((n + 1 : ℕ) : ℝ)) * (c k * (a (nthPrime i)) ^ (2 * k)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i : Fin (n + 1), ∑ k ∈ Finset.range (R + 1),
            (1 / ((n + 1 : ℕ) : ℝ)) * (c k * (a (nthPrime i)) ^ (2 * k)) := Finset.sum_comm
      _ = (1 / ((n + 1 : ℕ) : ℝ)) *
            ∑ i : Fin (n + 1), ∑ k ∈ Finset.range (R + 1),
              c k * (a (nthPrime i)) ^ (2 * k) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  rw [hswap]
  refine mul_le_mul_of_nonneg_left ?_ hpos.le
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hcase : lam ≤ |a (nthPrime i)|
  · rw [if_pos hcase]; exact hmaj _ hcase
  · rw [if_neg hcase]; exact hnn _


/-! ## The closed form at degree four

Optimising the shift gives a clean answer.  With `σ² = (λ²−2)/(λ²−1)` the shifted quartic's value
collapses to

  **`1/(λ⁴ − 2λ² + 2)`**,

using only `M₀ = 1`, `M₂ = 1`, `M₄ = 2` — no temperedness.  At `λ = 1.8` that is `0.16618`.

This is also the **exact** LP optimum for those three moments: the dual extremal measure puts mass
`1/(λ⁴−2λ²+2)` at `±λ` and the rest at `±σ`, and matching `M₂` and `M₄` forces precisely that `σ`.
So `1/(λ⁴ − 2λ² + 2)` is everything the second and fourth moments can say. -/

/-- The shifted quartic majorant, with the shift left free. -/
theorem shifted_quartic_moment_bound {a : Nat.Primes → ℝ}
    (hM : ∀ k, k ≤ 2 → Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ)) *
      ∑ i : Fin (n + 1), (a (nthPrime i)) ^ (2 * k)) atTop
      (𝓝 (if k = 0 then 1 else if k = 1 then 1 else 2)))
    {lam s : ℝ} (hlam0 : 0 < lam) (hs0 : 0 ≤ s) (hsl : s < lam ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), (if lam ≤ |a (nthPrime i)| then (1 : ℝ) else 0)
        < (2 - 2 * s + s ^ 2) / (lam ^ 2 - s) ^ 2 + ε := by
  have hden : (0:ℝ) < (lam ^ 2 - s) ^ 2 := by
    have : (0:ℝ) < lam ^ 2 - s := by linarith
    positivity
  set c : ℕ → ℝ := fun k =>
    if k = 0 then s ^ 2 / (lam ^ 2 - s) ^ 2
    else if k = 1 then -(2 * s) / (lam ^ 2 - s) ^ 2
    else 1 / (lam ^ 2 - s) ^ 2 with hc
  have hexp : ∀ x : ℝ, ∑ k ∈ Finset.range 3, c k * x ^ (2 * k)
      = (x ^ 2 - s) ^ 2 / (lam ^ 2 - s) ^ 2 := by
    intro x
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hc]
    norm_num
    field_simp
    ring
  have hbound := poly_moment_density_bound (a := a) (R := 2) (c := c)
    (M := fun k => if k = 0 then 1 else if k = 1 then 1 else 2) hM hlam0 ?_ ?_ hε
  · refine hbound.mono fun n hn => lt_of_lt_of_le hn ?_
    have hval : (∑ k ∈ Finset.range 3,
        c k * (if k = 0 then (1:ℝ) else if k = 1 then 1 else 2))
        = (2 - 2 * s + s ^ 2) / (lam ^ 2 - s) ^ 2 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hc]
      norm_num
      field_simp
      ring
    linarith [le_of_eq hval]
  · intro x hx
    rw [hexp, le_div_iff₀ hden, one_mul]
    have hx2 : lam ^ 2 ≤ x ^ 2 := by
      have h1 : lam ^ 2 ≤ |x| ^ 2 := by gcongr
      rwa [← abs_pow, abs_of_nonneg (by positivity)] at h1
    nlinarith [hx2, hsl]
  · intro x
    rw [hexp]
    positivity

/-- **The optimal shift, and the closed form.**  At `s = (λ²−2)/(λ²−1)` the bound is
`1/(λ⁴ − 2λ² + 2)`. -/
theorem quartic_shift_identity {lam : ℝ} (hL : 2 < lam ^ 2) :
    (2 - 2 * ((lam ^ 2 - 2) / (lam ^ 2 - 1)) + ((lam ^ 2 - 2) / (lam ^ 2 - 1)) ^ 2)
        / (lam ^ 2 - (lam ^ 2 - 2) / (lam ^ 2 - 1)) ^ 2
      = 1 / (lam ^ 4 - 2 * lam ^ 2 + 2) := by
  set L : ℝ := lam ^ 2 with hLdef
  have h1 : L - 1 ≠ 0 := by nlinarith
  have h2 : (0:ℝ) < L ^ 2 - 2 * L + 2 := by nlinarith [sq_nonneg (L - 1)]
  have hnum : 2 - 2 * ((L - 2) / (L - 1)) + ((L - 2) / (L - 1)) ^ 2
      = (L ^ 2 - 2 * L + 2) / (L - 1) ^ 2 := by field_simp; ring
  have hd : (L - (L - 2) / (L - 1)) = (L ^ 2 - 2 * L + 2) / (L - 1) := by field_simp; ring
  have hpow : lam ^ 4 = L ^ 2 := by rw [hLdef]; ring
  rw [hnum, hd, div_pow, hpow]
  field_simp


/-! ## Degree eight: the full cited record

The two-shift octic, in the moment setting.  With the Catalan moments `M₀…M₈ = 1, 1, 2, 5, 14`
(`∫(2cos θ)^{2m} dST = Cₘ`), which the `r ≤ 9` record supplies, the bound is

  **`(14 − 10(s₁+s₂) + 2((s₁+s₂)² + 2s₁s₂) − 2s₁s₂(s₁+s₂) + s₁²s₂²) / ((λ²−s₁)(λ²−s₂))²`.**

Measured: at `λ = 1.8` the optimum is `0.10896` at `(s₁,s₂) ≈ (0.194, 1.538)` — and an independent
numerical LP over all symmetric measures on `ℝ` with those moments returns `0.108963`, so this is
the exact optimum of the full classical record.  Against a true Sato--Tate density of `0.0374`, a
factor of about `2.9`, with **no temperedness assumed anywhere**. -/

theorem shifted_octic_moment_bound {a : Nat.Primes → ℝ}
    (hM : ∀ k, k ≤ 4 → Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ)) *
      ∑ i : Fin (n + 1), (a (nthPrime i)) ^ (2 * k)) atTop
      (𝓝 (if k = 0 then 1 else if k = 1 then 1 else if k = 2 then 2
            else if k = 3 then 5 else 14)))
    {lam s₁ s₂ : ℝ} (hlam0 : 0 < lam) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (hl₁ : s₁ < lam ^ 2) (hl₂ : s₂ < lam ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), (if lam ≤ |a (nthPrime i)| then (1 : ℝ) else 0)
        < (14 - 10 * (s₁ + s₂) + 2 * ((s₁ + s₂) ^ 2 + 2 * (s₁ * s₂))
            - 2 * (s₁ * s₂) * (s₁ + s₂) + (s₁ * s₂) ^ 2)
            / ((lam ^ 2 - s₁) * (lam ^ 2 - s₂)) ^ 2 + ε := by
  have hd₁ : (0:ℝ) < lam ^ 2 - s₁ := by linarith
  have hd₂ : (0:ℝ) < lam ^ 2 - s₂ := by linarith
  have hden : (0:ℝ) < ((lam ^ 2 - s₁) * (lam ^ 2 - s₂)) ^ 2 := by positivity
  set D : ℝ := ((lam ^ 2 - s₁) * (lam ^ 2 - s₂)) ^ 2 with hD
  set c : ℕ → ℝ := fun k =>
    if k = 0 then (s₁ * s₂) ^ 2 / D
    else if k = 1 then -(2 * (s₁ * s₂) * (s₁ + s₂)) / D
    else if k = 2 then ((s₁ + s₂) ^ 2 + 2 * (s₁ * s₂)) / D
    else if k = 3 then -(2 * (s₁ + s₂)) / D
    else 1 / D with hc
  have hexp : ∀ x : ℝ, ∑ k ∈ Finset.range 5, c k * x ^ (2 * k)
      = ((x ^ 2 - s₁) * (x ^ 2 - s₂)) ^ 2 / D := by
    intro x
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hc]
    norm_num
    rw [hD]
    field_simp
    ring
  have hbound := poly_moment_density_bound (a := a) (R := 4) (c := c)
    (M := fun k => if k = 0 then 1 else if k = 1 then 1 else if k = 2 then 2
            else if k = 3 then 5 else 14) hM hlam0 ?_ ?_ hε
  · refine hbound.mono fun n hn => lt_of_lt_of_le hn ?_
    have hval : (∑ k ∈ Finset.range 5, c k *
        (if k = 0 then (1:ℝ) else if k = 1 then 1 else if k = 2 then 2
          else if k = 3 then 5 else 14))
        = (14 - 10 * (s₁ + s₂) + 2 * ((s₁ + s₂) ^ 2 + 2 * (s₁ * s₂))
            - 2 * (s₁ * s₂) * (s₁ + s₂) + (s₁ * s₂) ^ 2) / D := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hc]
      norm_num
      field_simp
      ring
    linarith [le_of_eq hval]
  · intro x hx
    rw [hexp, le_div_iff₀ hden, one_mul, hD]
    have hx2 : lam ^ 2 ≤ x ^ 2 := by
      have h1 : lam ^ 2 ≤ |x| ^ 2 := by gcongr
      rwa [← abs_pow, abs_of_nonneg (by positivity)] at h1
    have e₁ : lam ^ 2 - s₁ ≤ x ^ 2 - s₁ := by linarith
    have e₂ : lam ^ 2 - s₂ ≤ x ^ 2 - s₂ := by linarith
    have hprod : (lam ^ 2 - s₁) * (lam ^ 2 - s₂) ≤ (x ^ 2 - s₁) * (x ^ 2 - s₂) := by
      nlinarith [hd₁, hd₂, e₁, e₂]
    nlinarith [hprod, mul_pos hd₁ hd₂]
  · intro x
    rw [hexp, hD]
    positivity


/-! ## The other side: lower density bounds

The same moments bound the density from **below**, via minorants instead of majorants: if a
polynomial in `a²` lies below the indicator everywhere on `ℝ`, its moment value is a lower bound
for the density.

Measured (LP over all symmetric measures on `ℝ` with the given moments, 60001-point grid):

| `λ` | from `M₀…M₄` (`r ≤ 4`) | from `M₀…M₈` (`r ≤ 9`) |
| --- | --- | --- |
| `0.5` | `0.3606` | `0.3988` |
| `0.8` | `0.1156` | `0.2376` |
| `1.0` | `0` | `0.1671` |
| `1.4` | `0` | `0.0509` |

So the `r ≤ 9` record forces **at least `16.7%` of primes to have `|a_p| ≥ 1`**, with no
temperedness assumed.  The degree-four record gives nothing past `λ = 1`, because a measure may
send a vanishing mass to infinity — legitimate here, since Kim--Sarnak allows `|a_p| ≤ 2p^{7/64}`,
which is unbounded.

**Scope.**  This is the general tool.  Explicit minorants realising the table are not constructed
here. -/

theorem poly_moment_density_lower_bound {a : Nat.Primes → ℝ} {R : ℕ} {c M : ℕ → ℝ}
    (hmom : ∀ k, k ≤ R → Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ)) *
      ∑ i : Fin (n + 1), (a (nthPrime i)) ^ (2 * k)) atTop (𝓝 (M k)))
    {lam : ℝ}
    (hmin : ∀ x : ℝ, ∑ k ∈ Finset.range (R + 1), c k * x ^ (2 * k)
      ≤ (if lam ≤ |x| then (1 : ℝ) else 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (∑ k ∈ Finset.range (R + 1), c k * M k) - ε
        < (1 / ((n + 1 : ℕ) : ℝ)) *
          ∑ i : Fin (n + 1), (if lam ≤ |a (nthPrime i)| then (1 : ℝ) else 0) := by
  have hcomb : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (R + 1), c k *
      ((1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), (a (nthPrime i)) ^ (2 * k))) atTop
      (𝓝 (∑ k ∈ Finset.range (R + 1), c k * M k)) := by
    refine tendsto_finset_sum _ fun k hk => ?_
    exact (hmom k (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).const_mul (c k)
  have hev : ∀ᶠ n : ℕ in atTop,
      (∑ k ∈ Finset.range (R + 1), c k * M k) - ε
        < ∑ k ∈ Finset.range (R + 1), c k *
          ((1 / ((n + 1 : ℕ) : ℝ)) *
            ∑ i : Fin (n + 1), (a (nthPrime i)) ^ (2 * k)) :=
    hcomb.eventually_const_lt (by linarith)
  filter_upwards [hev] with n hn
  refine lt_of_lt_of_le hn ?_
  have hpos : (0:ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
  have hswap : (∑ k ∈ Finset.range (R + 1), c k *
      ((1 / ((n + 1 : ℕ) : ℝ)) * ∑ i : Fin (n + 1), (a (nthPrime i)) ^ (2 * k)))
      = (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), ∑ k ∈ Finset.range (R + 1),
          c k * (a (nthPrime i)) ^ (2 * k) := by
    calc (∑ k ∈ Finset.range (R + 1), c k *
        ((1 / ((n + 1 : ℕ) : ℝ)) * ∑ i : Fin (n + 1), (a (nthPrime i)) ^ (2 * k)))
        = ∑ k ∈ Finset.range (R + 1), ∑ i : Fin (n + 1),
            (1 / ((n + 1 : ℕ) : ℝ)) * (c k * (a (nthPrime i)) ^ (2 * k)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i : Fin (n + 1), ∑ k ∈ Finset.range (R + 1),
            (1 / ((n + 1 : ℕ) : ℝ)) * (c k * (a (nthPrime i)) ^ (2 * k)) := Finset.sum_comm
      _ = (1 / ((n + 1 : ℕ) : ℝ)) *
            ∑ i : Fin (n + 1), ∑ k ∈ Finset.range (R + 1),
              c k * (a (nthPrime i)) ^ (2 * k) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  rw [hswap]
  refine mul_le_mul_of_nonneg_left ?_ hpos.le
  exact Finset.sum_le_sum fun i _ => hmin _

end CriticalLinePhasor.PartialSerre

#print axioms CriticalLinePhasor.PartialSerre.secondMoment_density_bound
#print axioms CriticalLinePhasor.PartialSerre.moment_density_bound
#print axioms CriticalLinePhasor.PartialSerre.poly_moment_density_bound
#print axioms CriticalLinePhasor.PartialSerre.shifted_quartic_moment_bound
#print axioms CriticalLinePhasor.PartialSerre.quartic_shift_identity
#print axioms CriticalLinePhasor.PartialSerre.shifted_octic_moment_bound
#print axioms CriticalLinePhasor.PartialSerre.poly_moment_density_lower_bound
