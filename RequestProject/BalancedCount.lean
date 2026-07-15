import RequestProject.CMTypeCensus

/-!
# The balanced-CM-type counting identity: `#balanced-(n,n) = C(2n, n)`

This file supplies the *combinatorial engine* behind the census of `CMTypeCensus.lean`.
That file measures, field by field, the number of **primitive** `K`-balanced CM types (the
simple abelian varieties of Weil type).  Here we prove the underlying counting law that
explains the measurements uniformly, and read the census's two headline numbers — the
dimension-4 obstruction (`0`) and the dimension-6 dissolution (`12`) — off a single identity.

## The identity

Fix a degree-`4n` abelian CM field with its `2n` conjugate pairs `{a, −a}` of embeddings, and
an imaginary quadratic subfield `K` given by an index-2 subgroup `H` with `−1 ∉ H`.  A CM type
`Φ` chooses one embedding from each pair.  Its `K`-signature is `(|Φ ∩ H|, |Φ ∖ H|)`, and `Φ`
is **balanced-`(n,n)`** when the two halves are equal.

> **The `−1 ∉ H` coset lemma (the structural heart).**  Because `−1 ∉ H` and `H` has index 2,
> the two embeddings `a` and `−a` of a conjugate pair lie in *different* `H`-cosets: exactly one
> of `{a, −a}` is in `H`.  So building a CM type is: for each of the `2n` pairs, decide whether
> its `H`-side or its non-`H`-side representative enters `Φ`.  A balanced choice is one that puts
> exactly `n` of the `2n` pairs on the `H`-side, hence

> **`#{balanced-(n,n) CM types} = C(2n, n)`   (`balancedCount_eq_choose`).**

This is proved **generally** — for any pair-map `neg` and any membership predicate `inH` such that
each pair splits (`inH a ≠ inH (neg a)`, which is exactly the `−1 ∉ H` coset condition) — by
induction on the pair list (`count_choices`), specialising Pascal's rule.  It is not a
per-modulus enumeration.

## Reading the census through the identity

`primitive = balanced − imprimitive` (partition by primitivity, `census_add_imprim`).  The
identity fixes `balanced = C(2n, n)` once and for all; the census's `decide` supplies the
imprimitive count per field.  Two consequences, each an instance:

* **Dimension 4 (`n = 2`), the Mumford obstruction restated.**  `balanced = C(4,2) = 6` and the
  imprimitive-balanced count is also `6`: **imprimitivity exactly saturates balance**, so
  `primitive = 6 − 6 = 0` for every imaginary `K` in `ℚ(ζ_N)`, `N ∈ {15,16,20,24}`
  (`obstruction_via_identity`).  A simple abelian fourfold of Weil type has no cyclotomic CM.
* **Dimension 6 (`n = 3`), the dissolution.**  `balanced = C(6,3) = 20`, imprimitive-balanced
  `= 8`, so `primitive = 20 − 8 = 12` — *uniformly* across every imaginary `K` in `ℚ(ζ_N)`,
  `N ∈ {21,28,36}` (`uniform_twelve`).  Simple cyclotomic Weil-type sixfolds exist, `12` per `K`.

**Scope.**  Cyclotomic degree-12 fields only, matching `CMTypeCensus.lean`.  The composite
(non-cyclotomic) degree-12 abelian CM fields, where the scout's Sage census
(`tmp/weil_composite_census.sage`) measured the *same* uniform `12`/`8`, use a coset-of-`H`
model rather than the direct `(ℤ/N)ˣ` model of this framework; that enumeration is the named
remaining brick (the "composite degree-12" section below).  The identification of a balanced
primitive type with a simple abelian variety of Weil type is the classical Shimura–Taniyama /
Moonen–Zarhin dictionary of `CMTypeCensus.lean`, cited not re-proven.  No `axiom`, no `sorry`,
no `native_decide`; nothing assumes or proves RH/GRH.
-/

open List

namespace CriticalLinePhasor.CMTypeCensus

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

/-! ## The abstract choice model

`choices neg L` builds every "type" over a list `L` of pair representatives: fold over `L`,
choosing at each pair `a` either `a` itself or its partner `neg a`.  With `neg := negMod N` and
`L := pairReps N` this is definitionally the census's `cmTypes N`. -/

/-- All choices over the pair list `L`: one of `{a, neg a}` per pair.  Structurally identical to
`cmTypes`, with the partner map `neg` abstracted. -/
def choices (neg : ℕ → ℕ) (L : List ℕ) : List (List ℕ) :=
  L.foldr (fun a acc => acc.flatMap (fun t => [a :: t, neg a :: t])) [[]]

/-- `cmTypes N` is the choice model with partner map `negMod N` over the pairs `pairReps N`. -/
theorem cmTypes_eq_choices (N : ℕ) : cmTypes N = choices (negMod N) (pairReps N) := rfl

lemma choices_cons (neg : ℕ → ℕ) (a : ℕ) (L : List ℕ) :
    choices neg (a :: L) = (choices neg L).flatMap (fun t => [a :: t, neg a :: t]) := rfl

/-- Every choice list has one entry per pair: its length is `L.length`. -/
lemma mem_choices_length (neg : ℕ → ℕ) :
    ∀ (L : List ℕ) (Φ : List ℕ), Φ ∈ choices neg L → Φ.length = L.length := by
  intro L
  induction L with
  | nil => intro Φ hΦ; simp only [choices, List.foldr_nil, List.mem_singleton] at hΦ; simp [hΦ]
  | cons a L ih =>
    intro Φ hΦ
    rw [choices_cons, List.mem_flatMap] at hΦ
    obtain ⟨t, ht, hΦt⟩ := hΦ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hΦt
    rcases hΦt with h | h <;> (subst h; simp [ih t ht])

/-! ## The `C(2n, n)` counting identity

The heart: when each pair splits across `H` (`inH a ≠ inH (neg a)` — the `−1 ∉ H` coset
condition), the number of choice lists with exactly `k` entries inside `H` is `C(L.length, k)`. -/

/-- One pair `a` contributes exactly one `H`-side and one non-`H`-side extension of `t`: its two
children shift the inside-count by `0` and by `1`.  (`inH a ≠ inH (neg a)` is the splitting.) -/
lemma key_term (neg : ℕ → ℕ) (inH : ℕ → Bool) {a : ℕ} (hne : inH a ≠ inH (neg a))
    (t : List ℕ) (k : ℕ) :
    ([a :: t, neg a :: t]).countP (fun Φ => Φ.countP inH == k)
      = (if ((t.countP inH == k) = true) then 1 else 0)
        + (if ((t.countP inH + 1 == k) = true) then 1 else 0) := by
  simp only [List.countP_cons, List.countP_nil, Nat.zero_add]
  cases ha : inH a <;> cases hb : inH (neg a) <;> (simp_all; try omega)

/-- Distributing the inside-count over one pair's branching: choices with `k` inside come from
tails with `k` inside (the non-`H` child) plus tails with `k−1` inside (the `H` child). -/
lemma flat_split (neg : ℕ → ℕ) (inH : ℕ → Bool) {a : ℕ} (hne : inH a ≠ inH (neg a)) (k : ℕ)
    (l : List (List ℕ)) :
    (l.flatMap (fun t => [a :: t, neg a :: t])).countP (fun Φ => Φ.countP inH == k)
      = l.countP (fun t => t.countP inH == k) + l.countP (fun t => t.countP inH + 1 == k) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.flatMap_cons, List.countP_append, ih, key_term neg inH hne t k,
        List.countP_cons, List.countP_cons]
    omega

/-- **The counting identity (abstract).**  If every pair `a ∈ L` splits across `inH`
(`inH a ≠ inH (neg a)`), the number of choice lists with exactly `k` entries in `inH` is
`C(L.length, k)`.  Proof: induction on `L`, with Pascal's rule at the inductive step. -/
theorem count_choices (neg : ℕ → ℕ) (inH : ℕ → Bool) :
    ∀ (L : List ℕ), (∀ a ∈ L, inH a ≠ inH (neg a)) →
      ∀ k, (choices neg L).countP (fun Φ => Φ.countP inH == k) = (L.length).choose k := by
  intro L
  induction L with
  | nil => intro _ k; cases k <;> simp [choices]
  | cons a L ih =>
    intro hsplit k
    have hne : inH a ≠ inH (neg a) := hsplit a (by simp)
    have hL : ∀ b ∈ L, inH b ≠ inH (neg b) := fun b hb => hsplit b (List.mem_cons_of_mem a hb)
    rw [choices_cons, flat_split neg inH hne, List.length_cons, ih hL k]
    cases k with
    | zero =>
      rw [Nat.choose_zero_right, Nat.choose_zero_right]
      have h0 : (choices neg L).countP (fun t => t.countP inH + 1 == 0) = 0 := by
        apply List.countP_eq_zero.2; intro t _; simp
      rw [h0]
    | succ k =>
      have hs : (choices neg L).countP (fun t => t.countP inH + 1 == k + 1)
              = L.length.choose k := by
        rw [show (fun t : List ℕ => t.countP inH + 1 == k + 1)
              = (fun t => t.countP inH == k) from by funext t; simp, ih hL k]
      rw [hs, Nat.choose_succ_succ]
      ring

/-! ## The balanced and imprimitive-balanced counts -/

/-- The number of `K`-balanced-`(k,k)` CM types of `ℚ(ζ_N)` — primitive **or not**. -/
def balancedCount (N : ℕ) (H : List ℕ) (k : ℕ) : ℕ := (cmTypes N).countP (isBalanced H k)

/-- The number of **imprimitive** (non-simple) `K`-balanced-`(k,k)` CM types. -/
def imprimBalancedCount (N : ℕ) (H : List ℕ) (k : ℕ) : ℕ :=
  (cmTypes N).countP (fun Φ => !isPrimitive N Φ && isBalanced H k Φ)

/-- **The balanced count is `C(2n, n)`.**  For any imaginary quadratic `H` whose `2n` conjugate
pairs each split across `H` (`hsplit`, the `−1 ∉ H` coset condition), the number of
`K`-balanced-`(n,n)` CM types of `ℚ(ζ_N)` equals `C(2n, n)`.  This is the general theorem behind
the census's per-field balanced totals. -/
theorem balancedCount_eq_choose (N : ℕ) (H : List ℕ) (n : ℕ)
    (hlen : (pairReps N).length = 2 * n)
    (hsplit : ∀ a ∈ pairReps N, (H.contains a) ≠ (H.contains (negMod N a))) :
    balancedCount N H n = Nat.choose (2 * n) n := by
  have hcongr : balancedCount N H n
      = (cmTypes N).countP (fun Φ => Φ.countP (fun m => H.contains m) == n) := by
    apply List.countP_congr
    intro Φ hΦ
    have hlenΦ : Φ.length = 2 * n := by
      rw [mem_choices_length (negMod N) (pairReps N) Φ hΦ]; exact hlen
    have hb : isBalanced H n Φ = (Φ.countP (fun m => H.contains m) == n) := by
      show ((Φ.countP (fun m => H.contains m), Φ.length - Φ.countP (fun m => H.contains m)) == (n, n))
          = (Φ.countP (fun m => H.contains m) == n)
      rw [hlenΦ]
      generalize Φ.countP (fun m => H.contains m) = c
      show ((c == n) && (2 * n - c == n)) = (c == n)
      cases h : (c == n) with
      | false => simp
      | true => rw [beq_iff_eq] at h; subst h; simp only [Bool.true_and]; rw [beq_iff_eq]; omega
    simp only [hb]
  have hc : (cmTypes N).countP (fun Φ => Φ.countP (fun m => H.contains m) == n)
      = (pairReps N).length.choose n :=
    count_choices (negMod N) (fun m => H.contains m) (pairReps N) hsplit n
  rw [hcongr, hc, hlen]

/-! ## Primitive = balanced − imprimitive -/

/-- Partitioning a Boolean predicate `q` by another predicate `p`: the `p`-true and `p`-false
`q`-counts sum to the `q`-count. -/
lemma countP_and_not_split {α : Type*} (l : List α) (p q : α → Bool) :
    l.countP (fun x => p x && q x) + l.countP (fun x => !p x && q x) = l.countP q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.countP_cons]; cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

/-- **`primitive + imprimitive = balanced`.**  The census's primitive-balanced count plus the
imprimitive-balanced count is the total balanced count. -/
theorem census_add_imprim (N : ℕ) (H : List ℕ) (k : ℕ) :
    censusCount N H k + imprimBalancedCount N H k = balancedCount N H k :=
  countP_and_not_split (cmTypes N) (isPrimitive N) (isBalanced H k)

/-! ## Dimension 6 — the uniform 12, read off the identity

`balanced = C(6,3) = 20` (an instance of `balancedCount_eq_choose`), `imprimitive = 8` (kernel
enumeration), so `primitive = 20 − 8 = 12`, for every imaginary quadratic `K` in each degree-12
cyclotomic CM field. -/

/-- The two decidable per-field inputs at `N = 21`: each imaginary `K` splits every pair
(`−1 ∉ H`), and its imprimitive-balanced-`(3,3)` count is `8`. -/
theorem deg12_data_21 : ∀ H ∈ imaginaryQuadSubgroups 21,
    (∀ a ∈ pairReps 21, (H.contains a) ≠ (H.contains (negMod 21 a)))
      ∧ imprimBalancedCount 21 H 3 = 8 := by decide

theorem deg12_data_28 : ∀ H ∈ imaginaryQuadSubgroups 28,
    (∀ a ∈ pairReps 28, (H.contains a) ≠ (H.contains (negMod 28 a)))
      ∧ imprimBalancedCount 28 H 3 = 8 := by decide

theorem deg12_data_36 : ∀ H ∈ imaginaryQuadSubgroups 36,
    (∀ a ∈ pairReps 36, (H.contains a) ≠ (H.contains (negMod 36 a)))
      ∧ imprimBalancedCount 36 H 3 = 8 := by decide

/-- `ℚ(ζ₂₁)`: for each imaginary quadratic `K`, `balanced = 20 = C(6,3)`, `imprimitive = 8`,
`primitive = 12`. -/
theorem uniform12_21 : ∀ H ∈ imaginaryQuadSubgroups 21,
    balancedCount 21 H 3 = 20 ∧ imprimBalancedCount 21 H 3 = 8 ∧ censusCount 21 H 3 = 12 := by
  intro H hH
  obtain ⟨hsplit, himp⟩ := deg12_data_21 H hH
  have hbal : balancedCount 21 H 3 = 20 := by
    have h := balancedCount_eq_choose 21 H 3 (by decide) hsplit; rw [h]; decide
  have hcen : censusCount 21 H 3 = 12 := by have := census_add_imprim 21 H 3; omega
  exact ⟨hbal, himp, hcen⟩

theorem uniform12_28 : ∀ H ∈ imaginaryQuadSubgroups 28,
    balancedCount 28 H 3 = 20 ∧ imprimBalancedCount 28 H 3 = 8 ∧ censusCount 28 H 3 = 12 := by
  intro H hH
  obtain ⟨hsplit, himp⟩ := deg12_data_28 H hH
  have hbal : balancedCount 28 H 3 = 20 := by
    have h := balancedCount_eq_choose 28 H 3 (by decide) hsplit; rw [h]; decide
  have hcen : censusCount 28 H 3 = 12 := by have := census_add_imprim 28 H 3; omega
  exact ⟨hbal, himp, hcen⟩

theorem uniform12_36 : ∀ H ∈ imaginaryQuadSubgroups 36,
    balancedCount 36 H 3 = 20 ∧ imprimBalancedCount 36 H 3 = 8 ∧ censusCount 36 H 3 = 12 := by
  intro H hH
  obtain ⟨hsplit, himp⟩ := deg12_data_36 H hH
  have hbal : balancedCount 36 H 3 = 20 := by
    have h := balancedCount_eq_choose 36 H 3 (by decide) hsplit; rw [h]; decide
  have hcen : censusCount 36 H 3 = 12 := by have := census_add_imprim 36 H 3; omega
  exact ⟨hbal, himp, hcen⟩

/-- **The uniform 12 (dimension 6).**  For each of `N ∈ {21, 28, 36}` and every imaginary
quadratic `K ⊂ ℚ(ζ_N)`, the balanced-`(3,3)` types number `20 = C(6,3)`, the imprimitive ones
`8`, and the **primitive (simple Weil-type sixfolds)** exactly `20 − 8 = 12`.  The identity's
`C(6,3) = 20` is the field-independent input; the uniform `12` is the census headline. -/
theorem uniform_twelve :
    ∀ N ∈ ([21, 28, 36] : List ℕ), ∀ H ∈ imaginaryQuadSubgroups N,
      balancedCount N H 3 = 20 ∧ imprimBalancedCount N H 3 = 8 ∧ censusCount N H 3 = 12 := by
  intro N hN
  fin_cases hN
  · exact uniform12_21
  · exact uniform12_28
  · exact uniform12_36

/-! ## Dimension 4 — the Mumford obstruction as "imprimitivity saturates balance"

`balanced = C(4,2) = 6` and imprimitive-balanced `= 6`, so `primitive = 6 − 6 = 0`.  The
obstruction is exactly the coincidence that at `n = 2` imprimitivity consumes *all* of the
balance. -/

theorem deg8_data_15 : ∀ H ∈ imaginaryQuadSubgroups 15,
    (∀ a ∈ pairReps 15, (H.contains a) ≠ (H.contains (negMod 15 a)))
      ∧ imprimBalancedCount 15 H 2 = 6 := by decide

theorem deg8_data_16 : ∀ H ∈ imaginaryQuadSubgroups 16,
    (∀ a ∈ pairReps 16, (H.contains a) ≠ (H.contains (negMod 16 a)))
      ∧ imprimBalancedCount 16 H 2 = 6 := by decide

theorem deg8_data_20 : ∀ H ∈ imaginaryQuadSubgroups 20,
    (∀ a ∈ pairReps 20, (H.contains a) ≠ (H.contains (negMod 20 a)))
      ∧ imprimBalancedCount 20 H 2 = 6 := by decide

theorem deg8_data_24 : ∀ H ∈ imaginaryQuadSubgroups 24,
    (∀ a ∈ pairReps 24, (H.contains a) ≠ (H.contains (negMod 24 a)))
      ∧ imprimBalancedCount 24 H 2 = 6 := by decide

theorem obstruction12_15 : ∀ H ∈ imaginaryQuadSubgroups 15,
    balancedCount 15 H 2 = 6 ∧ imprimBalancedCount 15 H 2 = 6 ∧ censusCount 15 H 2 = 0 := by
  intro H hH
  obtain ⟨hsplit, himp⟩ := deg8_data_15 H hH
  have hbal : balancedCount 15 H 2 = 6 := by
    have h := balancedCount_eq_choose 15 H 2 (by decide) hsplit; rw [h]; decide
  have hcen : censusCount 15 H 2 = 0 := by have := census_add_imprim 15 H 2; omega
  exact ⟨hbal, himp, hcen⟩

theorem obstruction12_16 : ∀ H ∈ imaginaryQuadSubgroups 16,
    balancedCount 16 H 2 = 6 ∧ imprimBalancedCount 16 H 2 = 6 ∧ censusCount 16 H 2 = 0 := by
  intro H hH
  obtain ⟨hsplit, himp⟩ := deg8_data_16 H hH
  have hbal : balancedCount 16 H 2 = 6 := by
    have h := balancedCount_eq_choose 16 H 2 (by decide) hsplit; rw [h]; decide
  have hcen : censusCount 16 H 2 = 0 := by have := census_add_imprim 16 H 2; omega
  exact ⟨hbal, himp, hcen⟩

theorem obstruction12_20 : ∀ H ∈ imaginaryQuadSubgroups 20,
    balancedCount 20 H 2 = 6 ∧ imprimBalancedCount 20 H 2 = 6 ∧ censusCount 20 H 2 = 0 := by
  intro H hH
  obtain ⟨hsplit, himp⟩ := deg8_data_20 H hH
  have hbal : balancedCount 20 H 2 = 6 := by
    have h := balancedCount_eq_choose 20 H 2 (by decide) hsplit; rw [h]; decide
  have hcen : censusCount 20 H 2 = 0 := by have := census_add_imprim 20 H 2; omega
  exact ⟨hbal, himp, hcen⟩

theorem obstruction12_24 : ∀ H ∈ imaginaryQuadSubgroups 24,
    balancedCount 24 H 2 = 6 ∧ imprimBalancedCount 24 H 2 = 6 ∧ censusCount 24 H 2 = 0 := by
  intro H hH
  obtain ⟨hsplit, himp⟩ := deg8_data_24 H hH
  have hbal : balancedCount 24 H 2 = 6 := by
    have h := balancedCount_eq_choose 24 H 2 (by decide) hsplit; rw [h]; decide
  have hcen : censusCount 24 H 2 = 0 := by have := census_add_imprim 24 H 2; omega
  exact ⟨hbal, himp, hcen⟩

/-- **The Mumford obstruction, restated through the identity (dimension 4).**  For each of
`N ∈ {15, 16, 20, 24}` and every imaginary quadratic `K ⊂ ℚ(ζ_N)`, the balanced-`(2,2)` types
number `6 = C(4,2)`, the imprimitive ones **also** `6`, so the **primitive (simple Weil-type
fourfolds)** number `6 − 6 = 0`.  The obstruction is exactly "imprimitivity saturates balance"
at `n = 2` — the census headline `no_simple_weil_fourfold_cyclotomic` as a corollary. -/
theorem obstruction_via_identity :
    ∀ N ∈ ([15, 16, 20, 24] : List ℕ), ∀ H ∈ imaginaryQuadSubgroups N,
      balancedCount N H 2 = 6 ∧ imprimBalancedCount N H 2 = 6 ∧ censusCount N H 2 = 0 := by
  intro N hN
  fin_cases hN
  · exact obstruction12_15
  · exact obstruction12_16
  · exact obstruction12_20
  · exact obstruction12_24

/-! ## Named remaining enumeration: the composite degree-12 fields

The scout's Sage census (`tmp/weil_composite_census.sage`) measured the **same** uniform
`12` primitive / `8` imprimitive balanced-`(3,3)` count for every imaginary quadratic `K` in
every *composite* (non-cyclotomic) degree-12 abelian CM field `E = fixed(H) ⊂ ℚ(ζ_N)`,
`[E:ℚ] = 12` (`N ∈ {35, 39, 45, 52, 56, 57, 63, 70, 72, …}`).  That case needs a
**coset-of-`H`** CM-type model (embeddings of `E` = cosets of `H` in `(ℤ/N)ˣ`), not the direct
`(ℤ/N)ˣ` model of `CMTypeCensus.lean`.  Building that model here is the named remaining brick;
the counting identity `balancedCount_eq_choose` above already applies verbatim to it once the
pair-splitting hypothesis is phrased over cosets, so only the model glue is outstanding.  The
cyclotomic case is discharged in full by `uniform_twelve` and `obstruction_via_identity`. -/

end CriticalLinePhasor.CMTypeCensus

#print axioms CriticalLinePhasor.CMTypeCensus.balancedCount_eq_choose
#print axioms CriticalLinePhasor.CMTypeCensus.count_choices
#print axioms CriticalLinePhasor.CMTypeCensus.uniform_twelve
#print axioms CriticalLinePhasor.CMTypeCensus.obstruction_via_identity
#print axioms CriticalLinePhasor.CMTypeCensus.census_add_imprim
