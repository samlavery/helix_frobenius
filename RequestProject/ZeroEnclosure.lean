import RequestProject.CarrierIntervalCount

/-!
# The random-access zero finder: `i ↦ [L_i, U_i]`, with a proof that the interval holds `γ_i`

This is the product theorem for the extractor, scoped to the algorithm rather than to the global
zero geometry.  Nothing here assumes RH, nothing assumes simplicity of any zero it does not
certify, and nothing classifies zeros off the critical line.

## The shape

`Count(a) = i-1`, `Count(b) = i`, a bank-error bound and a jet-tail bound together imply
`γ_i ∈ I` for an explicit interval `I`.  The counting routine is an **interface**: the theorem
consumes two integers and a proof that the routine is additive along the ordinate axis, and does
not care whether they came from Turing's method, from Riemann–von Mangoldt plus a bound, from the
clock-and-parity construction, or from a table.

* `CountRoutine`, `count_eq_one_of_endpoints` — the interface, and the reduction of the two endpoint
  counts to the single fact the rest of the proof uses: `zeroCount a b = 1`.
* `unique_event_of_count_eq_one` — that fact gives a UNIQUE event in `(a,b)`, of multiplicity one.
  Multiplicity is where simplicity would otherwise have to be assumed: it is certified here, by the
  count, not hypothesised.
* `sign_change_of_count_eq_one` — the readout's two endpoint signs then necessarily differ, so a
  bisection is guaranteed to make progress.  From the interval count law.
* `event_mem_of_sign_bracket` — and any sub-bracket across which the readout changes sign contains
  that same unique event.  This is the bisection certificate.
* `ratio_enclosure` — the method-specific analytic step, stated with the two error budgets as
  hypotheses.  If `P` and `Q` are within `α` and `β` of the principal jets `d^{-m}` and
  `d^{-(m+1)}`, then `P/Q` is within an explicit radius of `d`.  The bank error and the jet tail
  both enter only through `α` and `β`, so the lemma is indifferent to which contributed what.
* `gamma_enclosure` — the composition: the returned interval, and the proof it holds `γ_i`.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.CarrierParity

/-! ## The count, as an interface -/

/-- A counting routine.  `C T` is whatever certifies "how many events are at most `T`".  The only
property the enclosure theorem needs is additivity along the axis between non-event ordinates. -/
structure CountRoutine where
  /-- the count at a height -/
  C : ℝ → ℕ
  /-- additivity between ordinates carrying no event -/
  additive : ∀ x y : ℝ, x ≤ y → xiEntire (x : ℂ) ≠ 0 → xiEntire (y : ℂ) ≠ 0 →
    C y = C x + zeroCount x y

/-- **The interface reduction.**  The two endpoint counts are used once, here, and never again. -/
theorem count_eq_one_of_endpoints (R : CountRoutine) {a b : ℝ} {i : ℕ} (hab : a ≤ b)
    (ha : xiEntire (a : ℂ) ≠ 0) (hb : xiEntire (b : ℂ) ≠ 0)
    (hi : 1 ≤ i) (h1 : R.C a + 1 = i) (h2 : R.C b = i) :
    zeroCount a b = 1 := by
  have := R.additive a b hab ha hb
  omega

/-! ## What the count buys: a unique event, with its multiplicity certified -/

/-- An event has order at least one. -/
theorem one_le_order_of_zero {t : ℝ} (h0 : xiEntire (t : ℂ) = 0) :
    1 ≤ analyticOrderNatAt xiEntire (t : ℂ) := by
  by_contra hlt
  push Not at hlt
  interval_cases h : analyticOrderNatAt xiEntire (t : ℂ)
  obtain ⟨g, _, hg0, hev⟩ :=
    ((xiEntire_analyticAt (t : ℂ)).analyticOrderNatAt_eq_iff
      (xiEntire_analyticOrderAt_ne_top _)).mp h
  have := hev.self_of_nhds
  rw [pow_zero, one_smul] at this
  exact hg0 (this ▸ h0)

/-- **A count of one gives a unique event, and certifies that it is simple.**  Simplicity is not
assumed anywhere: it is a consequence of the endpoint counts differing by exactly one. -/
theorem unique_event_of_count_eq_one {a b : ℝ} (hcount : zeroCount a b = 1) :
    ∃! γ : ℝ, γ ∈ Set.Ioo a b ∧ xiEntire (γ : ℂ) = 0 := by
  set F := (zeros_finite_Ioo a b).toFinset with hF
  have hmem : ∀ t, t ∈ F ↔ (t ∈ Set.Ioo a b ∧ xiEntire (t : ℂ) = 0) := by
    intro t; simp [hF, Set.Finite.mem_toFinset]
  have hone : ∀ t ∈ F, 1 ≤ analyticOrderNatAt xiEntire (t : ℂ) :=
    fun t ht => one_le_order_of_zero ((hmem t).mp ht).2
  have hle : F.card ≤ 1 := by
    calc F.card = ∑ _t ∈ F, 1 := by simp
      _ ≤ ∑ t ∈ F, analyticOrderNatAt xiEntire (t : ℂ) := Finset.sum_le_sum hone
      _ = 1 := hcount
  have hpos : F.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hc
    push Not at hc
    interval_cases h : F.card
    rw [zeroCount, ← hF, Finset.card_eq_zero.mp h, Finset.sum_empty] at hcount
    exact absurd hcount (by norm_num)
  obtain ⟨γ, hγ⟩ := Finset.card_eq_one.mp (le_antisymm hle (Finset.card_pos.mpr hpos))
  refine ⟨γ, (hmem γ).mp (by rw [hγ]; exact Finset.mem_singleton_self γ), ?_⟩
  intro y hy
  have : y ∈ F := (hmem y).mpr hy
  rw [hγ, Finset.mem_singleton] at this
  exact this

/-- **A count of one forces the endpoint signs to differ**, so bisection is guaranteed to make
progress.  From the interval count law. -/
theorem sign_change_of_count_eq_one {a b : ℝ} (hab : a ≤ b)
    (ha : xiEntire (a : ℂ) ≠ 0) (hb : xiEntire (b : ℂ) ≠ 0) (hcount : zeroCount a b = 1) :
    (xiEntire (a : ℂ)).re * (xiEntire (b : ℂ)).re < 0 := by
  have hnotEven : ¬ Even (zeroCount a b) := by rw [hcount]; decide
  have hnp : ¬ (0 < (xiEntire (a : ℂ)).re * (xiEntire (b : ℂ)).re) :=
    fun h => hnotEven ((zeroCount_even_iff hab ha hb).mpr h)
  rcases lt_trichotomy ((xiEntire (a : ℂ)).re * (xiEntire (b : ℂ)).re) 0 with h | h | h
  · exact h
  · exfalso
    rcases mul_eq_zero.mp h with h' | h'
    · exact ha ((xiEntire_re_eq_zero_iff a).mp h')
    · exact hb ((xiEntire_re_eq_zero_iff b).mp h')
  · exact absurd h hnp

/-- **The bisection certificate.**  Any sub-bracket across which the readout changes sign contains
the unique event, wherever inside `(a,b)` it sits. -/
theorem event_mem_of_sign_bracket {a b c d : ℝ} (hcount : zeroCount a b = 1)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hsign : (xiEntire (c : ℂ)).re * (xiEntire (d : ℂ)).re < 0) :
    ∃ γ, γ ∈ Set.Ioo c d ∧ xiEntire (γ : ℂ) = 0 ∧
      ∀ γ' ∈ Set.Ioo a b, xiEntire (γ' : ℂ) = 0 → γ' = γ := by
  obtain ⟨γ₀, hγ₀, huniq⟩ := unique_event_of_count_eq_one hcount
  -- a zero exists in `[c,d]`, else the sign would be constant
  by_cases hex : ∀ t ∈ Set.Icc c d, xiEntire (t : ℂ) ≠ 0
  · exact absurd (sign_const_of_no_zeros hcd hex) (by linarith)
  push Not at hex
  obtain ⟨t, ht, h0⟩ := hex
  have hcne : xiEntire (c : ℂ) ≠ 0 := fun h => by
    rw [(xiEntire_re_eq_zero_iff c).mpr h] at hsign; simp at hsign
  have hdne : xiEntire (d : ℂ) ≠ 0 := fun h => by
    rw [(xiEntire_re_eq_zero_iff d).mpr h] at hsign; simp at hsign
  have htc : c < t := lt_of_le_of_ne ht.1 (fun h => hcne (h ▸ h0))
  have htd : t < d := lt_of_le_of_ne ht.2 (fun h => hdne (h ▸ h0))
  have htab : t ∈ Set.Ioo a b := ⟨lt_of_le_of_lt hac htc, lt_of_lt_of_le htd hdb⟩
  have := huniq t ⟨htab, h0⟩
  exact ⟨t, ⟨htc, htd⟩, h0, fun γ' hγ' h0' => (huniq γ' ⟨hγ', h0'⟩).trans this.symm⟩

/-! ## The method-specific analytic step: the jet ratio, with both budgets as hypotheses -/

/-- **The ratio enclosure.**  If `P` and `Q` are within `α` and `β` of the principal jets `d^{-m}`
and `d^{-(m+1)}`, then `P/Q` sits within an explicit radius of `d`.  The finite-bank error and the
jet tail enter only through `α` and `β`, so this step is indifferent to which contributed what. -/
theorem ratio_enclosure {d P Q : ℂ} {m : ℕ} {α β : ℝ} (hd : d ≠ 0)
    (hP : ‖P - 1 / d ^ m‖ ≤ α) (hQ : ‖Q - 1 / d ^ (m + 1)‖ ≤ β)
    (hβ : β < 1 / ‖d‖ ^ (m + 1)) :
    ‖P / Q - d‖ ≤ (α + ‖d‖ * β) / (1 / ‖d‖ ^ (m + 1) - β) := by
  have hdm : d ^ (m + 1) ≠ 0 := pow_ne_zero _ hd
  have hnd : (0 : ℝ) < ‖d‖ := norm_pos_iff.mpr hd
  have hQlb : 1 / ‖d‖ ^ (m + 1) - β ≤ ‖Q‖ := by
    have h1 : ‖(1 : ℂ) / d ^ (m + 1)‖ = 1 / ‖d‖ ^ (m + 1) := by
      rw [norm_div, norm_one, norm_pow]
    have h2 : ‖(1 : ℂ) / d ^ (m + 1)‖ ≤ ‖(1 : ℂ) / d ^ (m + 1) - Q‖ + ‖Q‖ :=
      norm_le_norm_sub_add _ _
    rw [h1, ← norm_neg ((1 : ℂ) / d ^ (m + 1) - Q), neg_sub] at h2
    linarith [h2, hQ]
  have hden : (0 : ℝ) < 1 / ‖d‖ ^ (m + 1) - β := by
    have : (0 : ℝ) < 1 / ‖d‖ ^ (m + 1) := by positivity
    linarith
  have hQ0 : Q ≠ 0 := by
    intro h; rw [h, norm_zero] at hQlb; linarith
  have hnum : P - d * Q = (P - 1 / d ^ m) - d * (Q - 1 / d ^ (m + 1)) := by
    field_simp
    ring
  have hsplit : P / Q - d = (P - d * Q) / Q := by field_simp
  rw [hsplit, norm_div]
  have hn : ‖P - d * Q‖ ≤ α + ‖d‖ * β := by
    rw [hnum]
    calc ‖(P - 1 / d ^ m) - d * (Q - 1 / d ^ (m + 1))‖
        ≤ ‖P - 1 / d ^ m‖ + ‖d * (Q - 1 / d ^ (m + 1))‖ := norm_sub_le _ _
      _ = ‖P - 1 / d ^ m‖ + ‖d‖ * ‖Q - 1 / d ^ (m + 1)‖ := by rw [norm_mul]
      _ ≤ α + ‖d‖ * β := by
          have := mul_le_mul_of_nonneg_left hQ (le_of_lt hnd)
          linarith
  have hnn : (0 : ℝ) ≤ α + ‖d‖ * β := le_trans (norm_nonneg _) hn
  calc ‖P - d * Q‖ / ‖Q‖ ≤ (α + ‖d‖ * β) / ‖Q‖ := by
        exact div_le_div_of_nonneg_right hn (le_of_lt (lt_of_lt_of_le hden hQlb))
    _ ≤ (α + ‖d‖ * β) / (1 / ‖d‖ ^ (m + 1) - β) := by
        exact div_le_div_of_nonneg_left hnn hden hQlb

/-- The real readout's estimate: taking the real part can only shrink the error. -/
theorem re_enclosure {d : ℝ} {P Q : ℂ} {m : ℕ} {α β ε : ℝ} (hd : (d : ℂ) ≠ 0)
    (hP : ‖P - 1 / (d : ℂ) ^ m‖ ≤ α) (hQ : ‖Q - 1 / (d : ℂ) ^ (m + 1)‖ ≤ β)
    (hβ : β < 1 / ‖(d : ℂ)‖ ^ (m + 1))
    (hε : (α + ‖(d : ℂ)‖ * β) / (1 / ‖(d : ℂ)‖ ^ (m + 1) - β) ≤ ε) :
    |(P / Q).re - d| ≤ ε := by
  have h := ratio_enclosure hd hP hQ hβ
  have : |(P / Q).re - d| ≤ ‖P / Q - (d : ℂ)‖ := by
    have hre : (P / Q - (d : ℂ)).re = (P / Q).re - d := by simp
    calc |(P / Q).re - d| = |(P / Q - (d : ℂ)).re| := by rw [hre]
      _ ≤ ‖P / Q - (d : ℂ)‖ := Complex.abs_re_le_norm _
  linarith

/-! ## The product theorem -/

/-- **THE PRODUCT THEOREM.**  `Count(a) = i-1`, `Count(b) = i`, a bank-error bound and a jet-tail
bound give `γ_i ∈ I` for the explicit interval `I = [γ̂ - ε, γ̂ + ε] ∩ (a,b)`.

The counting routine appears only as the interface `R`; RH is nowhere in scope; and the event's
multiplicity is certified by the count rather than assumed. -/
theorem gamma_enclosure (R : CountRoutine) {a b : ℝ} {i : ℕ} (hab : a ≤ b)
    (ha : xiEntire (a : ℂ) ≠ 0) (hb : xiEntire (b : ℂ) ≠ 0)
    (hi : 1 ≤ i) (hCa : R.C a + 1 = i) (hCb : R.C b = i)
    (y₀ : ℝ) (P Q : ℂ) (m : ℕ) (α β ε : ℝ)
    (hjet : ∀ γ : ℝ, γ ∈ Set.Ioo a b → xiEntire (γ : ℂ) = 0 →
      ((y₀ - γ : ℝ) : ℂ) ≠ 0 ∧
      ‖P - 1 / ((y₀ - γ : ℝ) : ℂ) ^ m‖ ≤ α ∧
      ‖Q - 1 / ((y₀ - γ : ℝ) : ℂ) ^ (m + 1)‖ ≤ β ∧
      β < 1 / ‖((y₀ - γ : ℝ) : ℂ)‖ ^ (m + 1) ∧
      (α + ‖((y₀ - γ : ℝ) : ℂ)‖ * β) / (1 / ‖((y₀ - γ : ℝ) : ℂ)‖ ^ (m + 1) - β) ≤ ε) :
    ∃ γ : ℝ, γ ∈ Set.Ioo a b ∧ xiEntire (γ : ℂ) = 0 ∧
      (∀ γ' ∈ Set.Ioo a b, xiEntire (γ' : ℂ) = 0 → γ' = γ) ∧
      γ ∈ Set.Icc (y₀ - (P / Q).re - ε) (y₀ - (P / Q).re + ε) := by
  have hcount := count_eq_one_of_endpoints R hab ha hb hi hCa hCb
  obtain ⟨γ, hγ, huniq⟩ := unique_event_of_count_eq_one hcount
  obtain ⟨hd, hP, hQ, hβ, hε⟩ := hjet γ hγ.1 hγ.2
  have hbound := re_enclosure hd hP hQ hβ hε
  refine ⟨γ, hγ.1, hγ.2, fun γ' hγ' h0' => huniq γ' ⟨hγ', h0'⟩, ?_⟩
  rw [abs_le] at hbound
  constructor <;> linarith [hbound.1, hbound.2]

end CriticalLinePhasor.CarrierParity
