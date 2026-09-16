import RequestProject.ZeroEnclosure

/-!
# A count of one from a non-vanishing derivative

`unique_event_of_count_eq_one` consumes `zeroCount a b = 1`, and until now the only route to that
hypothesis was a counting routine (`CountRoutine`).  This file supplies a second route that needs
no count at all.

## Why not a density bound

The obvious alternative — "a short interval holds at most two events" — is not the easier road it
looks.  `zeroCount a b ≤ 2` for a bracket of width `w` amounts to `|S(b) − S(a)| ≤ 2 − w·log(t/2π)/2π`,
which is the same `S`-variation problem as the coarse-clock gate, not a weaker one; and Jensen's
formula on a disc gives `O(log t)` events, not two.

## What works instead

A **non-vanishing derivative** on the bracket.  It is a pointwise, computable condition rather than
an asymptotic estimate, and it gives everything at once:

* at most one event, by Rolle — two zeros of the readout would force `u′` to vanish between them;
* at least one, by the intermediate value theorem from the sign change;
* and the event is SIMPLE, because a zero with non-vanishing derivative has analytic order one.

Hence `zeroCount a b = 1` exactly, with no count routine, no density estimate, and no hypothesis
about zeros elsewhere.
-/

open Complex

namespace CriticalLinePhasor.CarrierParity

/-- The readout as a function of the ordinate. -/
noncomputable def xiRe (t : ℝ) : ℝ := (xiEntire (t : ℂ)).re

theorem hasDerivAt_xiRe (t : ℝ) : HasDerivAt xiRe (deriv xiEntire (t : ℂ)).re t :=
  ((xiEntire_differentiable ((t : ℝ) : ℂ)).hasDerivAt).real_of_complex

theorem deriv_xiRe (t : ℝ) : deriv xiRe t = (deriv xiEntire (t : ℂ)).re :=
  (hasDerivAt_xiRe t).deriv

theorem continuous_xiRe : Continuous xiRe := xiEntire_continuous_ofReal

/-- **At most one event**, by Rolle: two zeros would force the derivative to vanish between them. -/
theorem subsingleton_zeros_of_deriv_ne_zero {a b : ℝ}
    (hd : ∀ t ∈ Set.Icc a b, (deriv xiEntire (t : ℂ)).re ≠ 0)
    {t₁ t₂ : ℝ} (h₁ : t₁ ∈ Set.Icc a b) (h₂ : t₂ ∈ Set.Icc a b)
    (hz₁ : xiRe t₁ = 0) (hz₂ : xiRe t₂ = 0) : t₁ = t₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨c, hc, hderiv⟩ := exists_deriv_eq_zero hlt continuous_xiRe.continuousOn
      (hz₁.trans hz₂.symm)
    exact hd c ⟨le_trans h₁.1 (le_of_lt hc.1), le_trans (le_of_lt hc.2) h₂.2⟩
      (by rwa [deriv_xiRe] at hderiv)
  · obtain ⟨c, hc, hderiv⟩ := exists_deriv_eq_zero hlt continuous_xiRe.continuousOn
      (hz₂.trans hz₁.symm)
    exact hd c ⟨le_trans h₂.1 (le_of_lt hc.1), le_trans (le_of_lt hc.2) h₁.2⟩
      (by rwa [deriv_xiRe] at hderiv)

/-- **At least one event**, by the intermediate value theorem. -/
theorem exists_zero_of_sign_change {a b : ℝ} (hab : a ≤ b) (hsign : xiRe a * xiRe b < 0) :
    ∃ t ∈ Set.Ioo a b, xiRe t = 0 := by
  have hane : xiRe a ≠ 0 := fun h => by rw [h, zero_mul] at hsign; exact absurd hsign (by norm_num)
  have hbne : xiRe b ≠ 0 := fun h => by rw [h, mul_zero] at hsign; exact absurd hsign (by norm_num)
  have : ∃ t ∈ Set.Icc a b, xiRe t = 0 := by
    rcases mul_neg_iff.mp hsign with ⟨hpa, hnb⟩ | ⟨hna, hpb⟩
    · obtain ⟨t, ht, h0⟩ := intermediate_value_Icc' hab continuous_xiRe.continuousOn
        (Set.mem_Icc.mpr ⟨hnb.le, hpa.le⟩)
      exact ⟨t, ht, h0⟩
    · obtain ⟨t, ht, h0⟩ := intermediate_value_Icc hab continuous_xiRe.continuousOn
        (Set.mem_Icc.mpr ⟨hna.le, hpb.le⟩)
      exact ⟨t, ht, h0⟩
  obtain ⟨t, ht, h0⟩ := this
  refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, h0⟩
  · rintro rfl; exact hane h0
  · rintro rfl; exact hbne h0

/-- **The event is simple**: a zero with non-vanishing derivative has analytic order one. -/
theorem order_eq_one_of_deriv_ne_zero {t : ℝ} (h0 : xiEntire (t : ℂ) = 0)
    (hd : (deriv xiEntire (t : ℂ)).re ≠ 0) :
    analyticOrderNatAt xiEntire (t : ℂ) = 1 := by
  have hne : deriv xiEntire (t : ℂ) ≠ 0 := fun h => hd (by rw [h]; simp)
  have := (xiEntire_analyticAt (t : ℂ)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero h0 hne
  unfold analyticOrderNatAt
  rw [this]
  rfl

/-- **A COUNT OF ONE, WITHOUT A COUNT.**  A sign change across a bracket on which the readout's
derivative does not vanish gives `zeroCount a b = 1` — exactly one event, and it is simple. -/
theorem zeroCount_eq_one_of_deriv_ne_zero {a b : ℝ} (hab : a < b)
    (hd : ∀ t ∈ Set.Icc a b, (deriv xiEntire (t : ℂ)).re ≠ 0)
    (hsign : xiRe a * xiRe b < 0) :
    zeroCount a b = 1 := by
  obtain ⟨γ, hγ, h0⟩ := exists_zero_of_sign_change hab.le hsign
  have hγC : xiEntire (γ : ℂ) = 0 := (xiEntire_re_eq_zero_iff γ).mp h0
  have hsingle : (zeros_finite_Ioo a b).toFinset = {γ} := by
    ext t
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, h0t⟩
      exact subsingleton_zeros_of_deriv_ne_zero hd
        ⟨le_of_lt ht.1, le_of_lt ht.2⟩ ⟨le_of_lt hγ.1, le_of_lt hγ.2⟩
        ((xiEntire_re_eq_zero_iff t).mpr h0t) h0
    · rintro rfl; exact ⟨hγ, hγC⟩
  rw [zeroCount, hsingle, Finset.sum_singleton]
  exact order_eq_one_of_deriv_ne_zero hγC (hd γ ⟨le_of_lt hγ.1, le_of_lt hγ.2⟩)

/-- The enclosure, with no count routine anywhere: a sign change plus a non-vanishing derivative
gives a unique simple event, and any sign-change sub-bracket holds it. -/
theorem unique_event_of_deriv_ne_zero {a b : ℝ} (hab : a < b)
    (hd : ∀ t ∈ Set.Icc a b, (deriv xiEntire (t : ℂ)).re ≠ 0)
    (hsign : xiRe a * xiRe b < 0) :
    ∃! γ : ℝ, γ ∈ Set.Ioo a b ∧ xiEntire (γ : ℂ) = 0 :=
  unique_event_of_count_eq_one (zeroCount_eq_one_of_deriv_ne_zero hab hd hsign)

/-! ## The count from a certified chain -/

/-- A degenerate interval holds no events. -/
theorem zeroCount_self (a : ℝ) : zeroCount a a = 0 := by
  have h : (zeros_finite_Ioo a a).toFinset = ∅ := by
    ext t
    simp [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_Ioo]
  rw [zeroCount, h, Finset.sum_empty]

/-- A certified cell has a non-vanishing readout at each end. -/
theorem endpoints_ne_zero_of_sign {a b : ℝ} (hsign : xiRe a * xiRe b < 0) :
    xiEntire (a : ℂ) ≠ 0 ∧ xiEntire (b : ℂ) ≠ 0 := by
  have ha : xiRe a ≠ 0 := fun h => by
    rw [h, zero_mul] at hsign; exact absurd hsign (by norm_num)
  have hb : xiRe b ≠ 0 := fun h => by
    rw [h, mul_zero] at hsign; exact absurd hsign (by norm_num)
  exact ⟨fun h => ha ((xiEntire_re_eq_zero_iff a).mpr h),
         fun h => hb ((xiEntire_re_eq_zero_iff b).mpr h)⟩

/-- **THE COUNT FROM A CERTIFIED CHAIN.**  Given ordinates `t 0 < t 1 < … < t n` such that across
each cell the readout changes sign and its derivative does not vanish, the total event count over
`(t 0, t n)` is exactly `n`.

This discharges the count with NO counting routine and NO unproved input: each cell contributes
exactly one simple event by `zeroCount_eq_one_of_deriv_ne_zero`, and the counts add by
`zeroCount_split`.  The cost is one cell per event — linear in the index — which is the price of
not assuming a clock bound. -/
theorem zeroCount_chain : ∀ (n : ℕ) (t : ℕ → ℝ),
    (∀ k, k < n → t k < t (k+1)) →
    (∀ k, k < n → ∀ s ∈ Set.Icc (t k) (t (k+1)), (deriv xiEntire (s : ℂ)).re ≠ 0) →
    (∀ k, k < n → xiRe (t k) * xiRe (t (k+1)) < 0) →
    zeroCount (t 0) (t n) = n := by
  intro n
  induction n with
  | zero => intro t _ _ _; exact zeroCount_self (t 0)
  | succ m ih =>
    intro t hlt hd hs
    have hmono : ∀ k, k ≤ m+1 → ∀ j, j ≤ k → t j ≤ t k := by
      intro k
      induction k with
      | zero =>
        intro _ j hj
        have : j = 0 := Nat.le_zero.mp hj
        rw [this]
      | succ p ihp =>
        intro hp j hj
        rcases eq_or_lt_of_le hj with h | h
        · rw [h]
        · exact le_trans (ihp (by omega) j (by omega)) (le_of_lt (hlt p (by omega)))
    have hc : xiEntire ((t m : ℝ) : ℂ) ≠ 0 := (endpoints_ne_zero_of_sign (hs m (by omega))).1
    rw [zeroCount_split (hmono m (by omega) 0 (Nat.zero_le m))
        (le_of_lt (hlt m (by omega))) hc,
      ih t (fun k hk => hlt k (by omega)) (fun k hk => hd k (by omega))
        (fun k hk => hs k (by omega)),
      zeroCount_eq_one_of_deriv_ne_zero (hlt m (by omega)) (hd m (by omega)) (hs m (by omega))]

/-! ## The capstone: the i-th event, enclosed, with nothing assumed -/

/-- **THE i-TH EVENT FROM A CERTIFIED CHAIN.**  Given ordinates `t 0 < t 1 < … < t n` across each of
which the readout changes sign and its derivative does not vanish: the counts to either side of the
`i`-th cell are exactly `i−1` and `i`, and that cell holds a unique event, which is simple.

Every hypothesis is a POINTWISE, COMPUTABLE condition on finitely many evaluations.  Nothing is
assumed about zeros outside the chain, nothing about simplicity, and no counting routine appears. -/
theorem ith_event_of_chain {n : ℕ} (t : ℕ → ℝ)
    (hlt : ∀ k, k < n → t k < t (k+1))
    (hdz : ∀ k, k < n → ∀ s ∈ Set.Icc (t k) (t (k+1)), (deriv xiEntire (s : ℂ)).re ≠ 0)
    (hsg : ∀ k, k < n → xiRe (t k) * xiRe (t (k+1)) < 0)
    {i : ℕ} (hi : 0 < i) (hin : i ≤ n) :
    zeroCount (t 0) (t (i-1)) = i - 1
      ∧ zeroCount (t 0) (t i) = i
      ∧ ∃! γ : ℝ, γ ∈ Set.Ioo (t (i-1)) (t i) ∧ xiEntire (γ : ℂ) = 0 := by
  have hsucc : i - 1 + 1 = i := Nat.succ_pred_eq_of_pos hi
  have hlow : zeroCount (t 0) (t (i-1)) = i - 1 :=
    zeroCount_chain (i-1) t (fun k hk => hlt k (by omega)) (fun k hk => hdz k (by omega))
      (fun k hk => hsg k (by omega))
  have hhigh : zeroCount (t 0) (t i) = i :=
    zeroCount_chain i t (fun k hk => hlt k (by omega)) (fun k hk => hdz k (by omega))
      (fun k hk => hsg k (by omega))
  refine ⟨hlow, hhigh, ?_⟩
  have hcell : (i-1) < n := by omega
  have h1 : t (i-1) < t i := by rw [← hsucc]; exact hlt (i-1) hcell
  have h2 : ∀ s ∈ Set.Icc (t (i-1)) (t i), (deriv xiEntire (s : ℂ)).re ≠ 0 := by
    rw [← hsucc]; exact hdz (i-1) hcell
  have h3 : xiRe (t (i-1)) * xiRe (t i) < 0 := by rw [← hsucc]; exact hsg (i-1) hcell
  exact unique_event_of_deriv_ne_zero h1 h2 h3

/-- **THE ENCLOSURE.**  Any sub-bracket of the `i`-th cell across which the readout changes sign
contains that unique event.  This is the returned interval: `γ_i ∈ (c,d)`. -/
theorem ith_event_enclosed {n : ℕ} (t : ℕ → ℝ)
    (hlt : ∀ k, k < n → t k < t (k+1))
    (hdz : ∀ k, k < n → ∀ s ∈ Set.Icc (t k) (t (k+1)), (deriv xiEntire (s : ℂ)).re ≠ 0)
    (hsg : ∀ k, k < n → xiRe (t k) * xiRe (t (k+1)) < 0)
    {i : ℕ} (hi : 0 < i) (hin : i ≤ n)
    {c d : ℝ} (hac : t (i-1) ≤ c) (hcd : c ≤ d) (hdb : d ≤ t i)
    (hsign : xiRe c * xiRe d < 0) :
    ∃ γ, γ ∈ Set.Ioo c d ∧ xiEntire (γ : ℂ) = 0 ∧
      ∀ γ' ∈ Set.Ioo (t (i-1)) (t i), xiEntire (γ' : ℂ) = 0 → γ' = γ := by
  have hsucc : i - 1 + 1 = i := Nat.succ_pred_eq_of_pos hi
  have hcell : (i-1) < n := by omega
  have h1 : t (i-1) < t i := by rw [← hsucc]; exact hlt (i-1) hcell
  have h2 : ∀ s ∈ Set.Icc (t (i-1)) (t i), (deriv xiEntire (s : ℂ)).re ≠ 0 := by
    rw [← hsucc]; exact hdz (i-1) hcell
  have h3 : xiRe (t (i-1)) * xiRe (t i) < 0 := by rw [← hsucc]; exact hsg (i-1) hcell
  exact event_mem_of_sign_bracket (zeroCount_eq_one_of_deriv_ne_zero h1 h2 h3) hac hcd hdb hsign

/-! ## The link to the carrier: the capstone's sign hypotheses are the carrier readout's -/

/-- `xiRe` and the carrier readout differ by two strictly positive factors. -/
theorem xiRe_mul_weldFactor_norm (Δ : ℝ) (t : ℝ) :
    xiRe t * ‖weldFactor Δ t‖ = (1/4 + t^2) * weldReadout Δ t := by
  rw [xiRe, xiEntire_re_ofReal, weldReadout]
  ring

/-- **The sign of the carrier readout IS the sign of `xiRe`.**  So the sign-change hypotheses of
`ith_event_of_chain` and `ith_event_enclosed` are exactly what the carrier readout reports — at any
carrier scale, since the bit is scale-free. -/
theorem sign_product_iff {Δ : ℝ} (hΔ : 0 < Δ) (a b : ℝ) :
    xiRe a * xiRe b < 0 ↔ weldReadout Δ a * weldReadout Δ b < 0 := by
  have ha := xiRe_mul_weldFactor_norm Δ a
  have hb := xiRe_mul_weldFactor_norm Δ b
  have pa : 0 < ‖weldFactor Δ a‖ := norm_pos_iff.mpr (weldFactor_ne_zero hΔ a)
  have pb : 0 < ‖weldFactor Δ b‖ := norm_pos_iff.mpr (weldFactor_ne_zero hΔ b)
  have qa := quarter_add_sq_pos a
  have qb := quarter_add_sq_pos b
  have key : (xiRe a * xiRe b) * (‖weldFactor Δ a‖ * ‖weldFactor Δ b‖)
      = ((1/4 + a^2) * (1/4 + b^2)) * (weldReadout Δ a * weldReadout Δ b) := by
    calc (xiRe a * xiRe b) * (‖weldFactor Δ a‖ * ‖weldFactor Δ b‖)
        = (xiRe a * ‖weldFactor Δ a‖) * (xiRe b * ‖weldFactor Δ b‖) := by ring
      _ = ((1/4 + a^2) * weldReadout Δ a) * ((1/4 + b^2) * weldReadout Δ b) := by rw [ha, hb]
      _ = ((1/4 + a^2) * (1/4 + b^2)) * (weldReadout Δ a * weldReadout Δ b) := by ring
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have h1 : (xiRe a * xiRe b) * (‖weldFactor Δ a‖ * ‖weldFactor Δ b‖) < 0 :=
      mul_neg_of_neg_of_pos h (mul_pos pa pb)
    have h2 : 0 ≤ ((1/4 + a^2) * (1/4 + b^2)) * (weldReadout Δ a * weldReadout Δ b) :=
      mul_nonneg (le_of_lt (mul_pos qa qb)) hc
    rw [key] at h1; linarith
  · intro h
    by_contra hc
    push_neg at hc
    have h1 : ((1/4 + a^2) * (1/4 + b^2)) * (weldReadout Δ a * weldReadout Δ b) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos qa qb) h
    have h2 : 0 ≤ (xiRe a * xiRe b) * (‖weldFactor Δ a‖ * ‖weldFactor Δ b‖) :=
      mul_nonneg hc (le_of_lt (mul_pos pa pb))
    rw [key] at h2; linarith

/-- **THE CHAIN, DRIVEN BY THE CARRIER READOUT.**  Every hypothesis is now something the phasor
bank reports: a sign change of the weld readout across each cell (at any carrier scale `Δ > 0`) and
a non-vanishing derivative.  The conclusion is the `i`-th event, enclosed. -/
theorem ith_event_enclosed_carrier {Δ : ℝ} (hΔ : 0 < Δ) {n : ℕ} (t : ℕ → ℝ)
    (hlt : ∀ k, k < n → t k < t (k+1))
    (hdz : ∀ k, k < n → ∀ s ∈ Set.Icc (t k) (t (k+1)), (deriv xiEntire (s : ℂ)).re ≠ 0)
    (hsg : ∀ k, k < n → weldReadout Δ (t k) * weldReadout Δ (t (k+1)) < 0)
    {i : ℕ} (hi : 0 < i) (hin : i ≤ n)
    {c d : ℝ} (hac : t (i-1) ≤ c) (hcd : c ≤ d) (hdb : d ≤ t i)
    (hsign : weldReadout Δ c * weldReadout Δ d < 0) :
    ∃ γ, γ ∈ Set.Ioo c d ∧ riemannZeta (1/2 + (γ : ℂ) * Complex.I) = 0 ∧
      ∀ γ' ∈ Set.Ioo (t (i-1)) (t i), xiEntire (γ' : ℂ) = 0 → γ' = γ := by
  obtain ⟨γ, hγ, h0, huniq⟩ := ith_event_enclosed t hlt hdz
    (fun k hk => (sign_product_iff hΔ _ _).mpr (hsg k hk)) hi hin hac hcd hdb
    ((sign_product_iff hΔ c d).mpr hsign)
  exact ⟨γ, hγ, (xiEntire_ofReal_eq_zero_iff γ).mp h0, huniq⟩

end CriticalLinePhasor.CarrierParity
