import RequestProject.Erdos377CarryRails

/-!
# Erdős 377, atomic front

Stage-3 formalization: measure identities and the integer-realization lemma
(tick-sup = real-sup).  Roadmap: `automorph/stage3_boundary_note.md`.

The exact target unfolds as
`∃ C : ℝ, ∀ n, ∑ p ∈ nondivisorPrimes n, (1 : ℝ) / p ≤ C`.
Before adding the top-window adapter, the following searches were run:

```
rg -n -i "adaptive.?j|top.?window|integer.?realization|transversal|Cantor|negative.?dimension|dimension.?excess|tail.?empty|over.?budget|3160|3250|atomic.?mass|diffuse.?mass" RequestProject automorph tmp --glob '*.lean' --glob '*.md' --glob '*.tex' --glob '*.py'
rg -n "railDigit|CarryFreeThrough|carryAt.*digit|digit.*CarryFree|mod_pow_succ" RequestProject/Erdos377CarryRails.lean
rg -n "theorem log_.*mono|log_mono|Nat\\.log.*≤|le_log|log_le" .lake/packages/mathlib/Mathlib/Data/Nat .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n "(:|→) Erdos377Bound|Erdos377Bound :=|HarmonicAtomicRailBudget|HarmonicDiffuseRailContractionAt|topWindow|TopWindow|transvers|Cantor|tail" RequestProject --glob '*.lean'
rg -n "HarmonicAtomicRailBudget|HarmonicDiffuseRailContractionAt|topWindow|TopWindow|transvers|Cantor|tail" .lake/packages/mathlib/Mathlib --glob '*.lean'
lean_local_search "carry-free base-p digits lower half"
lean_leansearch "If twice a residue modulo p^(j+1) is below p^(j+1), its j-th base-p digit is at most (p-1)/2"
```

Neutral decomposition: unfold the prefix inequality and expose its top digit with
`mod_pow_succ_eq_mod_add_digit_mul_pow`.

Two executable decompositions of the new bridge begin with:

1. `rw [mod_pow_succ_eq_mod_add_digit_mul_pow, pow_succ] at hprefix`;
2. `rw [prime_not_dvd_centralBinom_iff_carryFree hp] at hnondiv`.
-/

open Finset

namespace CriticalLinePhasor.Erdos377

/-- **Integer realization.**  If `x` satisfies gap conditions
`2·(x mod mᵢ) < mᵢ` for a finite family of moduli, then the integer
`A = max mᵢ·⌊x/mᵢ⌋` (the maximal cell left endpoint) satisfies every one of
them, sits at or below `x`, and within one cell width of it.  Consequently
the supremum of any gap-mass functional over the integers equals its
supremum over the reals: extremal configurations are always
integer-realized. -/
theorem integer_realization {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (m : ι → ℕ) (x : ℕ) (hgap : ∀ i ∈ s, 2 * (x % m i) < m i) :
    ∃ A : ℕ, A ≤ x ∧ ∀ i ∈ s, 2 * (A % m i) < m i ∧ x < A + m i := by
  classical
  refine ⟨s.sup' hs (fun j => x / m j * m j), ?_, ?_⟩
  · exact Finset.sup'_le hs (fun j => x / m j * m j)
      (fun j hj => Nat.div_mul_le_self x (m j))
  · intro i hi
    set A := s.sup' hs (fun j => x / m j * m j) with hAdef
    have hAle : A ≤ x := by
      rw [hAdef]
      exact Finset.sup'_le hs (fun j => x / m j * m j)
        (fun j hj => Nat.div_mul_le_self x (m j))
    have hAi : x / m i * m i ≤ A := by
      rw [hAdef]
      exact Finset.le_sup' (fun j => x / m j * m j) hi
    have hdm := Nat.div_add_mod x (m i)
    have hb : m i * (x / m i) = x / m i * m i := by ring
    have hg := hgap i hi
    have hmlt : x % m i < m i := by omega
    have ht : A - x / m i * m i ≤ x % m i := by omega
    have hmod : A % m i = A - x / m i * m i := by
      have hAeq : A = A - x / m i * m i + x / m i * m i := by omega
      conv_lhs => rw [hAeq]
      rw [Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt (by omega)
    exact ⟨by omega, by omega⟩

/-! ## Exact monotone adapter from full carry closure to a top window -/

/-- A single carry-free prefix forces its newly exposed base-`p` digit into the lower half.
This is the arithmetic bridge from Kummer's nested prefix test to the digit event counted by
`card_topDigits_lowerHalf`. -/
theorem railDigit_lowerHalf_of_prefix_noCarry {p n j : ℕ} (hp : 0 < p)
    (hprefix : 2 * (n % p ^ (j + 1)) < p ^ (j + 1)) :
    railDigit p n j ≤ (p - 1) / 2 := by
  rw [mod_pow_succ_eq_mod_add_digit_mul_pow, pow_succ] at hprefix
  have hpow : 0 < p ^ j := pow_pos hp j
  have hlt : (2 * railDigit p n j) * p ^ j < p * p ^ j := by
    calc
      (2 * railDigit p n j) * p ^ j =
          2 * (railDigit p n j * p ^ j) := by ring
      _ ≤ 2 * (n % p ^ j + railDigit p n j * p ^ j) := by
        exact Nat.mul_le_mul_left 2 (Nat.le_add_left _ _)
      _ < p * p ^ j := by simpa [mul_comm] using hprefix
  have hdigit : 2 * railDigit p n j < p :=
    (Nat.mul_lt_mul_right hpow).mp hlt
  omega

/-- The top-window event for an adaptive per-prime order `J`.  Truncating by `railDepth`
makes the definition total even on shallow rails. -/
def TopWindowLowerHalf (p n J : ℕ) : Prop :=
  ∀ i < min J (railDepth p n),
    railDigit p n (railDepth p n - 1 - i) ≤ (p - 1) / 2

/-- Full carry closure implies every truncated top-window condition. -/
theorem carryFree_topWindowLowerHalf {p n J : ℕ} (hp : 0 < p)
    (hfree : CarryFree p n) : TopWindowLowerHalf p n J := by
  intro i hi
  have hid : i < railDepth p n := hi.trans_le (min_le_right _ _)
  have hlevel : railDepth p n - 1 - i + 1 ∈ Ico 1 (carryCutoff p n) := by
    refine mem_Ico.mpr ⟨by omega, ?_⟩
    have hlog : railDepth p n ≤ Nat.log p (2 * n) := by
      exact Nat.log_mono_right (by omega)
    simp only [railDepth] at hid hlog ⊢
    simp only [carryCutoff]
    omega
  exact railDigit_lowerHalf_of_prefix_noCarry hp (hfree _ hlevel)

/-- Second executable route: start from the original nondivisibility predicate and cross the
Kummer adapter before entering the top window. -/
theorem primeNondivisor_topWindowLowerHalf {p n J : ℕ} (hp : p.Prime)
    (hnondiv : ¬p ∣ (2 * n).choose n) : TopWindowLowerHalf p n J := by
  rw [prime_not_dvd_centralBinom_iff_carryFree hp] at hnondiv
  exact carryFree_topWindowLowerHalf hp.pos hnondiv

/-- Prime bank selected only by the adaptive top-window event. -/
noncomputable def topWindowPrimes (n : ℕ) (J : ℕ → ℕ) : Finset ℕ := by
  classical
  exact n.primesLE.filter fun p ↦ TopWindowLowerHalf p n (J p)

/-- Harmonic mass of the adaptive top-window bank. -/
noncomputable def topWindowMass (n : ℕ) (J : ℕ → ℕ) : ℝ :=
  primeHarmonicMass (topWindowPrimes n J)

/-- Monotone restriction: every carry-free prime is retained by every adaptive top window. -/
theorem carryFreePrimes_subset_topWindowPrimes (n : ℕ) (J : ℕ → ℕ) :
    carryFreePrimes n ⊆ topWindowPrimes n J := by
  classical
  intro p hp
  have hpLE : p ∈ n.primesLE := (mem_filter.mp hp).1
  have hpPrime : p.Prime := Nat.prime_of_mem_primesLE hpLE
  rw [topWindowPrimes]
  exact mem_filter.mpr ⟨hpLE,
    carryFree_topWindowLowerHalf hpPrime.pos (mem_filter.mp hp).2⟩

/-- The original Erdős mass is bounded pointwise by the adaptive top-window functional. -/
theorem erdos377Mass_le_topWindowMass (n : ℕ) (J : ℕ → ℕ) :
    erdos377Mass n ≤ topWindowMass n J := by
  rw [erdos377Mass_eq_carryFreeRailSum, topWindowMass]
  exact primeHarmonicMass_mono (carryFreePrimes_subset_topWindowPrimes n J)

/-- On a rail of exact depth `d`, the intrinsic top-window event is literally the digit event
appearing in the finite measure identity. -/
theorem topWindowLowerHalf_iff_digit_event {p n J d : ℕ} (hJ : J ≤ d)
    (hdepth : railDepth p n = d) :
    TopWindowLowerHalf p n J ↔
      ∀ i < J, n / p ^ (d - 1 - i) % p ≤ (p - 1) / 2 := by
  simp only [TopWindowLowerHalf, hdepth, min_eq_left hJ, railDigit]

/-! ## Executable finite census for the first over-budget rail sets

Neutral decomposition: express simultaneous balance as a finite conjunction of the already
decidable `CarryFree` predicate, then normalize the bounded census by computation.

Two executable decompositions begin with:

1. `native_decide` on the filtered interval;
2. `rw [balanced_3_5_7_11_census] at hmem` in the pointwise corollary.

These theorems certify exactly the interval through `3250`; they deliberately make no statement
about larger integers.
-/

/-- Simultaneous full-depth balance on a finite bank of integer bases. -/
def BalancedOn (S : Finset ℕ) (n : ℕ) : Prop := ∀ p ∈ S, CarryFree p n

/-- Executable Boolean form of one full-depth carry-free test. -/
def carryFreeBool (p n : ℕ) : Bool :=
  (List.range (carryCutoff p n)).all fun i ↦ decide (2 * (n % p ^ i) < p ^ i)

/-- Executable Boolean form of simultaneous balance. -/
def balancedOnBool (S : List ℕ) (n : ℕ) : Bool :=
  S.all fun p ↦ carryFreeBool p n

theorem carryFreeBool_eq_true_iff (p n : ℕ) :
    carryFreeBool p n = true ↔ CarryFree p n := by
  simp only [carryFreeBool, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    CarryFree, CarryFreeThrough, mem_Ico]
  constructor
  · intro h i hi
    exact h i hi.2
  · intro h i hi
    by_cases hi0 : i = 0
    · subst i
      simpa using Nat.mod_one n
    · exact h i ⟨Nat.one_le_iff_ne_zero.mpr hi0, hi⟩

theorem balancedOnBool_eq_true_iff (S : List ℕ) (n : ℕ) :
    balancedOnBool S n = true ↔ ∀ p ∈ S, CarryFree p n := by
  simp [balancedOnBool, List.all_eq_true, carryFreeBool_eq_true_iff]

def overBudgetBases11 : Finset ℕ := {3, 5, 7, 11}
def overBudgetBases13 : Finset ℕ := {3, 5, 7, 13}
def overBudgetBases17 : Finset ℕ := {3, 5, 7, 17}
def overBudgetBases19 : Finset ℕ := {3, 5, 7, 19}
def overBudgetBaseList11 : List ℕ := [3, 5, 7, 11]
def overBudgetBaseList13 : List ℕ := [3, 5, 7, 13]
def overBudgetBaseList17 : List ℕ := [3, 5, 7, 17]
def overBudgetBaseList19 : List ℕ := [3, 5, 7, 19]

/- Exact finite census for `{3,5,7,11}` through `3250`, including zero. -/
set_option maxRecDepth 100000 in
theorem balanced_3_5_7_11_census :
    (Finset.range 3251).filter (fun n ↦ balancedOnBool overBudgetBaseList11 n = true) =
      {0, 1, 3160} := by
  set_option maxHeartbeats 1000000 in decide

/- Exact finite census for `{3,5,7,13}` through `3250`, including zero. -/
set_option maxRecDepth 100000 in
theorem balanced_3_5_7_13_census :
    (Finset.range 3251).filter (fun n ↦ balancedOnBool overBudgetBaseList13 n = true) =
      {0, 1, 756, 757, 3250} := by
  set_option maxHeartbeats 1000000 in decide

/- Exact finite census for `{3,5,7,17}` through `3250`, including zero. -/
set_option maxRecDepth 100000 in
theorem balanced_3_5_7_17_census :
    (Finset.range 3251).filter (fun n ↦ balancedOnBool overBudgetBaseList17 n = true) =
      {0, 1} := by
  set_option maxHeartbeats 1000000 in decide

/- Exact finite census for `{3,5,7,19}` through `3250`, including zero. -/
set_option maxRecDepth 100000 in
theorem balanced_3_5_7_19_census :
    (Finset.range 3251).filter (fun n ↦ balancedOnBool overBudgetBaseList19 n = true) =
      {0, 1, 3250} := by
  set_option maxHeartbeats 1000000 in decide

/-- Pointwise form of the first finite census. -/
theorem balancedOn_3_5_7_11_of_le_3250 {n : ℕ} (hn : n ≤ 3250)
    (hbalanced : BalancedOn overBudgetBases11 n) :
    n = 0 ∨ n = 1 ∨ n = 3160 := by
  have hmem : n ∈ (Finset.range 3251).filter
      (fun m ↦ balancedOnBool overBudgetBaseList11 m = true) :=
    mem_filter.mpr ⟨mem_range.mpr (by omega),
      (balancedOnBool_eq_true_iff _ _).mpr (by
        intro p hp
        exact hbalanced p (by simpa [overBudgetBaseList11, overBudgetBases11] using hp))⟩
  rw [balanced_3_5_7_11_census] at hmem
  simpa [Finset.mem_insert, Finset.mem_singleton] using hmem

/-- Pointwise form of the second finite census. -/
theorem balancedOn_3_5_7_13_of_le_3250 {n : ℕ} (hn : n ≤ 3250)
    (hbalanced : BalancedOn overBudgetBases13 n) :
    n = 0 ∨ n = 1 ∨ n = 756 ∨ n = 757 ∨ n = 3250 := by
  have hmem : n ∈ (Finset.range 3251).filter
      (fun m ↦ balancedOnBool overBudgetBaseList13 m = true) :=
    mem_filter.mpr ⟨mem_range.mpr (by omega),
      (balancedOnBool_eq_true_iff _ _).mpr (by
        intro p hp
        exact hbalanced p (by simpa [overBudgetBaseList13, overBudgetBases13] using hp))⟩
  rw [balanced_3_5_7_13_census] at hmem
  simpa [Finset.mem_insert, Finset.mem_singleton] using hmem

/-- Digits below the truncation level are unchanged by `mod p^D`. -/
theorem digit_of_mod {p x s D : ℕ} (_hp : 1 ≤ p) (h : s + 1 ≤ D) :
    x % p ^ D / p ^ s % p = x / p ^ s % p := by
  rw [show p ^ D = p ^ s * p ^ (D - s) by rw [← pow_add]; congr 1; omega]
  rw [Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (dvd_pow_self p (by omega : D - s ≠ 0))

/-- **Measure identity, general `J`.**  The top-`J`-digit lower-half conditions confine
residues mod `p^d` to exactly `((p-1)/2 + 1)^J * p^(d-J)` classes — the exact fraction
`((p+1)/2p)^J` behind the top-window mean theorem (sharp threshold `c* = 1/log 2`). -/
theorem card_topDigits_lowerHalf {p : ℕ} (hp : 1 ≤ p) :
    ∀ J d, J ≤ d →
    ((Finset.range (p ^ d)).filter
        (fun x => ∀ i < J, x / p ^ (d - 1 - i) % p ≤ (p - 1) / 2)).card
      = ((p - 1) / 2 + 1) ^ J * p ^ (d - J)
  | 0, d, _ => by
      simp
  | J + 1, d, hJd => by
      classical
      have hd1 : 1 ≤ d := by omega
      have hP : 0 < p ^ (d - 1) := pow_pos (by omega) _
      set h := (p - 1) / 2 + 1 with hh
      -- bijection with (range h) ×ˢ (J-condition filter at d-1)
      have key :
          ((Finset.range (p ^ d)).filter
            (fun x => ∀ i < J + 1, x / p ^ (d - 1 - i) % p ≤ (p - 1) / 2)).card
          = ((Finset.range h) ×ˢ
             ((Finset.range (p ^ (d - 1))).filter
               (fun y => ∀ i < J, y / p ^ (d - 1 - 1 - i) % p ≤ (p - 1) / 2))).card := by
        apply Finset.card_nbij'
          (i := fun x => (x / p ^ (d - 1), x % p ^ (d - 1)))
          (j := fun q => q.1 * p ^ (d - 1) + q.2)
        · intro x hx
          try simp only [Finset.mem_coe] at hx
          obtain ⟨hxr0, hcond⟩ := Finset.mem_filter.mp hx
          have hxr := Finset.mem_range.mp hxr0
          have htop : x / p ^ (d - 1) < p := by
            rw [Nat.div_lt_iff_lt_mul hP]
            calc x < p ^ d := hxr
              _ = p * p ^ (d - 1) := by
                  rw [← pow_succ']
                  congr 1
                  omega
          simp only [Finset.mem_coe, Finset.mem_product]
          try dsimp only
          refine ⟨Finset.mem_range.mpr ?_,
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hP), ?_⟩⟩
          · have h0 := hcond 0 (by omega)
            simp only [Nat.sub_zero] at h0
            rw [Nat.mod_eq_of_lt htop] at h0
            omega
          · intro i hi
            have := hcond (i + 1) (by omega)
            have hexp : d - 1 - (i + 1) = d - 1 - 1 - i := by omega
            rw [hexp] at this
            rw [digit_of_mod hp (by omega : (d - 1 - 1 - i) + 1 ≤ d - 1)]
            exact this
        · intro q hq
          try simp only [Finset.mem_coe] at hq
          obtain ⟨hq1x, hq2x⟩ := Finset.mem_product.mp hq
          have hq1 := Finset.mem_range.mp hq1x
          obtain ⟨hq2y, hqc⟩ := Finset.mem_filter.mp hq2x
          have hq2 := Finset.mem_range.mp hq2y
          have hqp : q.1 < p := by omega
          try simp only [Finset.mem_coe]
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
          · calc q.1 * p ^ (d - 1) + q.2 < q.1 * p ^ (d - 1) + p ^ (d - 1) := by omega
              _ = (q.1 + 1) * p ^ (d - 1) := by ring
              _ ≤ p * p ^ (d - 1) := Nat.mul_le_mul_right _ (by omega)
              _ = p ^ d := by
                  rw [← pow_succ']
                  congr 1
                  omega
          · intro i hi
            rcases Nat.eq_zero_or_pos i with rfl | hipos
            · simp only [Nat.sub_zero]
              have hdiv : (q.1 * p ^ (d - 1) + q.2) / p ^ (d - 1) = q.1 := by
                rw [show q.1 * p ^ (d - 1) + q.2 = q.2 + q.1 * p ^ (d - 1) by ring]
                rw [Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hq2]
                omega
              rw [hdiv, Nat.mod_eq_of_lt hqp]
              omega
            · have hexp : d - 1 - i = d - 1 - 1 - (i - 1) := by omega
              rw [hexp]
              have hmod : (q.1 * p ^ (d - 1) + q.2) % p ^ (d - 1) = q.2 := by
                rw [show q.1 * p ^ (d - 1) + q.2 = q.2 + q.1 * p ^ (d - 1) by ring]
                rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq2]
              rw [← digit_of_mod hp (by omega : (d - 1 - 1 - (i - 1)) + 1 ≤ d - 1), hmod]
              exact hqc (i - 1) (by omega)
        · intro x _
          exact Nat.div_add_mod' x (p ^ (d - 1))
        · intro q hq
          try simp only [Finset.mem_coe] at hq
          obtain ⟨hq1x, hq2x⟩ := Finset.mem_product.mp hq
          have hq1 := Finset.mem_range.mp hq1x
          have hq2 := Finset.mem_range.mp (Finset.mem_filter.mp hq2x).1
          have hdiv : (q.1 * p ^ (d - 1) + q.2) / p ^ (d - 1) = q.1 := by
            rw [show q.1 * p ^ (d - 1) + q.2 = q.2 + q.1 * p ^ (d - 1) by ring]
            rw [Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hq2]
            omega
          have hmod : (q.1 * p ^ (d - 1) + q.2) % p ^ (d - 1) = q.2 := by
            rw [show q.1 * p ^ (d - 1) + q.2 = q.2 + q.1 * p ^ (d - 1) by ring]
            rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq2]
          exact Prod.ext_iff.mpr ⟨hdiv, hmod⟩
      rw [key, Finset.card_product, Finset.card_range,
        card_topDigits_lowerHalf hp J (d - 1) (by omega)]
      rw [show d - 1 - J = d - (J + 1) by omega]
      ring

end CriticalLinePhasor.Erdos377

#print axioms CriticalLinePhasor.Erdos377.integer_realization
#print axioms CriticalLinePhasor.Erdos377.railDigit_lowerHalf_of_prefix_noCarry
#print axioms CriticalLinePhasor.Erdos377.carryFree_topWindowLowerHalf
#print axioms CriticalLinePhasor.Erdos377.primeNondivisor_topWindowLowerHalf
#print axioms CriticalLinePhasor.Erdos377.erdos377Mass_le_topWindowMass
#print axioms CriticalLinePhasor.Erdos377.topWindowLowerHalf_iff_digit_event
#print axioms CriticalLinePhasor.Erdos377.balanced_3_5_7_11_census
#print axioms CriticalLinePhasor.Erdos377.balanced_3_5_7_13_census
#print axioms CriticalLinePhasor.Erdos377.balanced_3_5_7_17_census
#print axioms CriticalLinePhasor.Erdos377.balanced_3_5_7_19_census
#print axioms CriticalLinePhasor.Erdos377.balancedOn_3_5_7_11_of_le_3250
#print axioms CriticalLinePhasor.Erdos377.balancedOn_3_5_7_13_of_le_3250
#print axioms CriticalLinePhasor.Erdos377.card_topDigits_lowerHalf
#print axioms CriticalLinePhasor.Erdos377.uniformHarmonicDiffuseRailBandEnvelope
#print axioms CriticalLinePhasor.Erdos377.erdos377Bound_of_harmonicAtomic_diffuse_uniform_band
