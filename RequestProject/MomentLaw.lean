import Mathlib

/-!
# The channel-moment closed form — the tower atlas' moment law as finite algebra

The tensor-tower atlas measured, at every grade `g` and every clock frequency `k`, that the
bounded channel second moment `E|T_k|²` sits on an exact rational
`C(g, μ)·Σᵢ C(μ, i)·C(g−μ, i)·(1/4)ⁱ` with `μ = (g − k)/2` (`tower_atlas_results.txt`,
`grade56_scaling_results.txt`).  This file proves that identity as a **pure finite
combinatorial fact**, with the Sato–Tate single-clock moments entering only as the three
scalar hypotheses `m 0 = 1`, `m (±2) = −1/2` — the measure theory that makes those the true
moments of a `SU(2)`-equidistributed angle is cited, not formalised.

The `g`-fold tensor's channels are **sign vectors** `ε ∈ {±1}^g` (one leg per factor of the
weight-1 conjugate pair `α^{±1}`), here indexed faithfully by `s : Fin g → Bool` through the
sign map `sgn`.  The channel's clock frequency is `Σⱼ sgn(sⱼ)`; the **channel second moment**
at frequency `k` is the lane-pair sum `Σ_{s, t : freq = k} ∏ⱼ m(sgn sⱼ − sgn tⱼ)` — the
diagonal of the Gram matrix of the frequency-`k` lanes under the single-clock moment `m`.

* `sgn`, `freq`, `minusSet` — the sign map, a channel's clock frequency, and its minus-set
  (the legs carrying `−1`); `freq_eq_g_sub_two_mul` : `freq s = g − 2·|minusSet s|`.
* `momentProd_eq` — **the single identity that turns analysis into counting**: the leg product
  `∏ⱼ m(sgn sⱼ − sgn tⱼ)` equals `(−1/2)^{#mismatched legs}`, because two legs agree ⇒ moment
  `1`, disagree ⇒ moment `−1/2` (their sign difference is `±2`).
* `channelMoment` — the frequency-`k` lane-pair sum, the object of the law.
* `subsetPairSum` — **the combinatorial core** (oracle-free): for the minus-sets,
  `Σ_{A,B : |A|=|B|=μ} (−1/2)^{|A ∆ B|} = C(g,μ)·Σᵢ C(μ,i)·C(g−μ,i)·(1/4)ⁱ`, proved by the
  fiber count `#{B : |A \ B| = i} = C(μ,i)·C(g−μ,i)` (a subset ↔ (intersection, added-part)
  bijection).
* `channelMoment_closedForm` — **the headline**: `channelMoment m (g − 2μ) = C(g,μ)·Σᵢ
  C(μ,i)·C(g−μ,i)·(1/4)ⁱ` (for every `μ`; degenerate `0 = 0` once `μ > g`).
* `stMoment`, `stChannelMoment_closedForm` — the concrete Sato–Tate single-clock moment
  function `m 0 = 1, m (±2) = −1/2, else 0` and the law instantiated on it.

**Scope.**  This is the finite-algebra content of the moment law: a combinatorial identity
about sign vectors, with the single-clock moments as scalar inputs.  It carries no arithmetic —
that `m` is the genuine Sato–Tate moment sequence (so the measured `E|T_k|²` equals this sum)
is the equidistribution theorem's territory (Sato–Tate for the constituent curves, joint
independence for distinct conductors), cited in the atlas and neither assumed nor proven here.
Nothing here assumes or proves RH/GRH.  No `axiom`, no `sorry`.
-/

open scoped BigOperators symmDiff
open Finset

namespace MomentLaw

variable {g : ℕ}

/-- The **sign map**: `true ↦ +1`, `false ↦ −1`.  A sign vector `ε ∈ {±1}^g` is a
`s : Fin g → Bool` read through `sgn`. -/
def sgn (b : Bool) : ℤ := if b then 1 else -1

/-- The **clock frequency** of a channel `s`: the sign sum `Σⱼ sgn(sⱼ) = #plus − #minus`. -/
def freq (s : Fin g → Bool) : ℤ := ∑ i, sgn (s i)

/-- The **minus-set** of a channel: the legs carrying `−1` (`sⱼ = false`).  Its size is the
number of minus legs `μ`, and `freq s = g − 2μ`. -/
def minusSet (s : Fin g → Bool) : Finset (Fin g) := univ.filter (fun i => s i = false)

/-- The Bool vector whose minus-set is exactly `A` (the inverse of `minusSet`). -/
def boolOf (A : Finset (Fin g)) : Fin g → Bool := fun i => if i ∈ A then false else true

@[simp] lemma minusSet_boolOf (A : Finset (Fin g)) : minusSet (boolOf A) = A := by
  ext i
  simp only [minusSet, boolOf, mem_filter, mem_univ, true_and]
  by_cases h : i ∈ A <;> simp_all

@[simp] lemma boolOf_minusSet (s : Fin g → Bool) : boolOf (minusSet s) = s := by
  funext i
  simp only [boolOf, minusSet, mem_filter, mem_univ, true_and]
  cases h : s i <;> simp_all

/-- **The frequency bookkeeping**: `freq s = g − 2·|minusSet s|`, so `freq s = k` pins the
minus-count.  Measured from the all-plus channel, two per flipped leg. -/
lemma freq_eq_g_sub_two_mul (s : Fin g → Bool) :
    freq s = (g : ℤ) - 2 * (minusSet s).card := by
  have hpt : ∀ i, sgn (s i) = 1 - 2 * (if s i = false then (1 : ℤ) else 0) := by
    intro i; cases s i <;> simp [sgn]
  rw [freq]
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum, Finset.sum_boole]
  simp only [minusSet, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- `freq s = g − 2μ` exactly when the minus-set has size `μ` (for `μ ≤ g`). -/
lemma freq_eq_iff_card (s : Fin g → Bool) (μ : ℕ) :
    freq s = (g : ℤ) - 2 * μ ↔ (minusSet s).card = μ := by
  rw [freq_eq_g_sub_two_mul]
  constructor
  · intro h; omega
  · intro h; rw [h]

/-- Membership of `minusSet s` in the `μ`-subsets is the frequency condition. -/
lemma minusSet_mem_powersetCard (s : Fin g → Bool) (μ : ℕ) :
    minusSet s ∈ powersetCard μ (univ : Finset (Fin g)) ↔ freq s = (g : ℤ) - 2 * μ := by
  rw [mem_powersetCard, freq_eq_iff_card]
  simp [Finset.subset_univ]

/-! ### The analysis-to-counting bridge -/

/-- **The single moment identity**: a leg pair contributes `1` if the two channels agree there
and `−1/2` if they disagree (their sign difference is `±2`).  Uses only the three scalar
moment values. -/
lemma moment_leg (mfun : ℤ → ℚ) (hm0 : mfun 0 = 1) (hm2 : mfun 2 = -(1/2))
    (hm2' : mfun (-2) = -(1/2)) (a b : Bool) :
    mfun (sgn a - sgn b) = if a = b then (1 : ℚ) else -(1/2) := by
  cases a <;> cases b <;> simp [sgn, hm0, hm2, hm2']

/-- **The leg product is a power of `−1/2`**: `∏ⱼ m(sgn sⱼ − sgn tⱼ) = (−1/2)^{#mismatch}`.
This is the identity that replaces the analytic moment sum by pure counting. -/
lemma momentProd_eq (mfun : ℤ → ℚ) (hm0 : mfun 0 = 1) (hm2 : mfun 2 = -(1/2))
    (hm2' : mfun (-2) = -(1/2)) (s t : Fin g → Bool) :
    (∏ j, mfun (sgn (s j) - sgn (t j)))
      = (-1/2 : ℚ) ^ (univ.filter (fun j => s j ≠ t j)).card := by
  have hleg : ∀ j, mfun (sgn (s j) - sgn (t j)) = if s j = t j then (1 : ℚ) else -(1/2) :=
    fun j => moment_leg mfun hm0 hm2 hm2' (s j) (t j)
  simp_rw [hleg]
  rw [Finset.prod_ite, Finset.prod_const_one, Finset.prod_const, one_mul]
  congr 1
  norm_num

/-- The mismatch set of two channels is the symmetric difference of their minus-sets. -/
lemma mismatch_eq_symmDiff (s t : Fin g → Bool) :
    univ.filter (fun j => s j ≠ t j) = minusSet s ∆ minusSet t := by
  ext j
  simp only [mem_filter, mem_univ, true_and, minusSet, Finset.mem_symmDiff, mem_filter]
  cases hs : s j <;> cases ht : t j <;> simp_all

/-! ### The channel second moment and its closed form -/

/-- The **channel second moment** at clock frequency `k`: the lane-pair sum
`Σ_{s, t : freq = k} ∏ⱼ m(sgn sⱼ − sgn tⱼ)` — the diagonal Gram entry of the frequency-`k`
lanes under the single-clock moment `m`. -/
def channelMoment (mfun : ℤ → ℚ) (k : ℤ) : ℚ :=
  ∑ s ∈ univ.filter (fun s : Fin g → Bool => freq s = k),
    ∑ t ∈ univ.filter (fun t : Fin g → Bool => freq t = k),
      ∏ j, mfun (sgn (s j) - sgn (t j))

/-- **The fiber count** (the combinatorial engine): among the `μ`-subsets `B`, exactly
`C(μ, i)·C(g−μ, i)` have `|A \ B| = i` (for `A` of size `μ`, `i ≤ μ`).  Proven by the
bijection `B ↦ (A ∩ B, B \ A)` onto (a `(μ−i)`-subset of `A`) × (an `i`-subset of `Aᶜ`). -/
lemma fiber_card {A : Finset (Fin g)} (hA : A.card = μ) {i : ℕ} (hi : i ≤ μ) :
    ((powersetCard μ (univ : Finset (Fin g))).filter (fun B => (A \ B).card = i)).card
      = μ.choose i * (g - μ).choose i := by
  have hbij :
      ((powersetCard μ (univ : Finset (Fin g))).filter (fun B => (A \ B).card = i)).card
        = ((powersetCard (μ - i) A) ×ˢ (powersetCard i (Aᶜ))).card := by
    apply Finset.card_nbij' (fun B => (A ∩ B, B \ A)) (fun p => p.1 ∪ p.2)
    · -- maps to
      intro B hB
      simp only [Finset.mem_coe, mem_filter, mem_powersetCard] at hB
      obtain ⟨⟨_hBsub, hBcard⟩, hAB⟩ := hB
      have hinter : (A ∩ B).card = μ - i := by
        have := Finset.card_inter_add_card_sdiff A B
        omega
      have hsdiff : (B \ A).card = i := by
        have hcomm : (A \ B).card = (B \ A).card := card_sdiff_comm (by rw [hA, hBcard])
        omega
      simp only [Finset.mem_coe, Finset.mem_product, mem_powersetCard]
      refine ⟨⟨inter_subset_left, hinter⟩, ⟨?_, hsdiff⟩⟩
      intro x hx
      rw [mem_compl]
      exact (mem_sdiff.1 hx).2
    · -- maps from
      intro p hp
      simp only [Finset.mem_coe, Finset.mem_product, mem_powersetCard] at hp
      obtain ⟨⟨hCsub, hCcard⟩, ⟨hDsub, hDcard⟩⟩ := hp
      have hdisj : Disjoint p.1 p.2 := by
        apply Finset.disjoint_left.2
        intro x hx1 hx2
        have := hDsub hx2
        rw [mem_compl] at this
        exact this (hCsub hx1)
      have hAeq : A \ (p.1 ∪ p.2) = A \ p.1 := by
        ext x
        simp only [mem_sdiff, mem_union]
        constructor
        · rintro ⟨hxA, hx⟩; exact ⟨hxA, fun h => hx (Or.inl h)⟩
        · rintro ⟨hxA, hx⟩
          refine ⟨hxA, ?_⟩
          rintro (h | h)
          · exact hx h
          · exact (mem_compl.1 (hDsub h)) hxA
      simp only [Finset.mem_coe, mem_filter, mem_powersetCard]
      refine ⟨⟨subset_univ _, ?_⟩, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisj, hCcard, hDcard]; omega
      · rw [hAeq, Finset.card_sdiff_of_subset hCsub, hA, hCcard]; omega
    · -- left inverse
      intro B _
      show (A ∩ B) ∪ (B \ A) = B
      ext x
      simp only [mem_union, mem_inter, mem_sdiff]
      constructor
      · rintro (⟨_, hxB⟩ | ⟨hxB, _⟩) <;> exact hxB
      · intro hxB
        by_cases hxA : x ∈ A
        · exact Or.inl ⟨hxA, hxB⟩
        · exact Or.inr ⟨hxB, hxA⟩
    · -- right inverse
      intro p hp
      simp only [Finset.mem_coe, Finset.mem_product, mem_powersetCard] at hp
      obtain ⟨⟨hCsub, _⟩, ⟨hDsub, _⟩⟩ := hp
      have hC : A ∩ (p.1 ∪ p.2) = p.1 := by
        ext x
        simp only [mem_inter, mem_union]
        constructor
        · rintro ⟨hxA, h | h⟩
          · exact h
          · exact absurd hxA (mem_compl.1 (hDsub h))
        · intro hx; exact ⟨hCsub hx, Or.inl hx⟩
      have hD : (p.1 ∪ p.2) \ A = p.2 := by
        ext x
        simp only [mem_sdiff, mem_union]
        constructor
        · rintro ⟨h | h, hxA⟩
          · exact absurd (hCsub h) hxA
          · exact h
        · intro hx
          exact ⟨Or.inr hx, mem_compl.1 (hDsub hx)⟩
      show (A ∩ (p.1 ∪ p.2), (p.1 ∪ p.2) \ A) = p
      rw [hC, hD]
  rw [hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard, hA,
    Finset.card_compl, Fintype.card_fin, hA, Nat.choose_symm hi]

/-- The reduced summand: for `A, B` of equal size, `(−1/2)^{|A ∆ B|} = (1/4)^{|A \ B|}`. -/
lemma summand_reduce {A B : Finset (Fin g)} (hAB : A.card = B.card) :
    (-1/2 : ℚ) ^ (A ∆ B).card = (1/4 : ℚ) ^ (A \ B).card := by
  have hd : (A ∆ B).card = (A \ B).card + (B \ A).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  have hc : (A \ B).card = (B \ A).card := card_sdiff_comm hAB
  rw [hd, ← hc, ← two_mul, pow_mul]
  norm_num

/-- The **combinatorial core**: the minus-set pair sum equals the closed form.  Independent of
any arithmetic — a fiber-counting identity over the `μ`-subsets of a `g`-element set. -/
theorem subsetPairSum (g μ : ℕ) :
    (∑ A ∈ powersetCard μ (univ : Finset (Fin g)),
      ∑ B ∈ powersetCard μ (univ : Finset (Fin g)), (-1/2 : ℚ) ^ (A ∆ B).card)
      = (g.choose μ : ℚ) *
        ∑ i ∈ range (μ + 1), (μ.choose i : ℚ) * ((g - μ).choose i : ℚ) * (1/4) ^ i := by
  -- inner sum for a fixed `A`, independent of `A`
  have hinner : ∀ A ∈ powersetCard μ (univ : Finset (Fin g)),
      (∑ B ∈ powersetCard μ (univ : Finset (Fin g)), (-1/2 : ℚ) ^ (A ∆ B).card)
        = ∑ i ∈ range (μ + 1), (μ.choose i : ℚ) * ((g - μ).choose i : ℚ) * (1/4) ^ i := by
    intro A hA
    rw [mem_powersetCard] at hA
    obtain ⟨_, hAcard⟩ := hA
    -- reduce each summand to `(1/4)^{|A \ B|}`
    have hstep1 : (∑ B ∈ powersetCard μ (univ : Finset (Fin g)), (-1/2 : ℚ) ^ (A ∆ B).card)
        = ∑ B ∈ powersetCard μ (univ : Finset (Fin g)), (1/4 : ℚ) ^ (A \ B).card := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [mem_powersetCard] at hB
      exact summand_reduce (hAcard.trans hB.2.symm)
    rw [hstep1]
    -- group by the fiber value `i = |A \ B|`
    have hmaps : ∀ B ∈ powersetCard μ (univ : Finset (Fin g)), (A \ B).card ∈ range (μ + 1) := by
      intro B _
      rw [mem_range]
      have : (A \ B).card ≤ A.card := Finset.card_le_card sdiff_subset
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    -- on the `i`-fiber the summand is the constant `(1/4)^i`
    have hcongr : (∑ B ∈ (powersetCard μ (univ : Finset (Fin g))).filter
        (fun B => (A \ B).card = i), (1/4 : ℚ) ^ (A \ B).card)
        = ∑ B ∈ (powersetCard μ (univ : Finset (Fin g))).filter
            (fun B => (A \ B).card = i), (1/4 : ℚ) ^ i := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [(mem_filter.1 hB).2]
    rw [hcongr, Finset.sum_const, fiber_card hAcard (by omega : i ≤ μ), nsmul_eq_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_fin, nsmul_eq_mul]

/-- **The headline law**: the channel second moment at frequency `k = g − 2μ` equals the atlas'
closed form `C(g, μ)·Σᵢ C(μ, i)·C(g−μ, i)·(1/4)ⁱ`.  A pure combinatorial identity with the
single-clock moment values `m 0 = 1, m (±2) = −1/2` as the only inputs. -/
theorem channelMoment_closedForm (mfun : ℤ → ℚ) (hm0 : mfun 0 = 1)
    (hm2 : mfun 2 = -(1/2)) (hm2' : mfun (-2) = -(1/2)) (μ : ℕ) :
    channelMoment (g := g) mfun ((g : ℤ) - 2 * μ)
      = (g.choose μ : ℚ) *
        ∑ i ∈ range (μ + 1), (μ.choose i : ℚ) * ((g - μ).choose i : ℚ) * (1/4) ^ i := by
  rw [← subsetPairSum g μ]
  -- rewrite each leg product as a power of `−1/2`, then reindex both sums by minus-sets
  unfold channelMoment
  have hprod : ∀ s t : Fin g → Bool,
      (∏ j, mfun (sgn (s j) - sgn (t j)))
        = (-1/2 : ℚ) ^ (minusSet s ∆ minusSet t).card := by
    intro s t
    rw [momentProd_eq mfun hm0 hm2 hm2' s t, mismatch_eq_symmDiff]
  simp_rw [hprod]
  -- reindex the outer sum `s ↦ minusSet s`
  apply Finset.sum_nbij' (fun s => minusSet s) (fun A => boolOf A)
  · intro s hs
    rw [mem_filter] at hs
    rw [minusSet_mem_powersetCard]
    exact hs.2
  · intro A hA
    rw [mem_powersetCard] at hA
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [← minusSet_mem_powersetCard, minusSet_boolOf, mem_powersetCard]
    exact ⟨subset_univ _, hA.2⟩
  · intro s _; exact boolOf_minusSet s
  · intro A _; exact minusSet_boolOf A
  · intro s hs
    -- reindex the inner sum `t ↦ minusSet t`
    apply Finset.sum_nbij' (fun t => minusSet t) (fun B => boolOf B)
    · intro t ht
      rw [mem_filter] at ht
      rw [minusSet_mem_powersetCard]
      exact ht.2
    · intro B hB
      rw [mem_powersetCard] at hB
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rw [← minusSet_mem_powersetCard, minusSet_boolOf, mem_powersetCard]
      exact ⟨subset_univ _, hB.2⟩
    · intro t _; exact boolOf_minusSet t
    · intro B _; exact minusSet_boolOf B
    · intro t _; rfl

/-! ### The concrete Sato–Tate single-clock moment -/

/-- The **Sato–Tate single-clock moment function**: `m 0 = 1`, `m (±2) = −1/2`, else `0` — the
moments of `2cos θ`'s harmonics for an `SU(2)`-equidistributed angle (the "otherwise `0`" clause
is part of the spec; only the achievable leg differences `±2, 0` enter the law). -/
def stMoment : ℤ → ℚ := fun k => if k = 0 then 1 else if k = 2 ∨ k = -2 then -(1/2) else 0

@[simp] lemma stMoment_zero : stMoment 0 = 1 := rfl
@[simp] lemma stMoment_two : stMoment 2 = -(1/2) := rfl
@[simp] lemma stMoment_neg_two : stMoment (-2) = -(1/2) := rfl

lemma stMoment_other {k : ℤ} (h0 : k ≠ 0) (h2 : k ≠ 2) (h2' : k ≠ -2) : stMoment k = 0 := by
  simp [stMoment, h0, h2, h2']

/-- **The moment law on the Sato–Tate moments**: instantiated at `stMoment`, the channel second
moment at frequency `g − 2μ` is the atlas' closed form. -/
theorem stChannelMoment_closedForm (μ : ℕ) :
    channelMoment (g := g) stMoment ((g : ℤ) - 2 * μ)
      = (g.choose μ : ℚ) *
        ∑ i ∈ range (μ + 1), (μ.choose i : ℚ) * ((g - μ).choose i : ℚ) * (1/4) ^ i :=
  channelMoment_closedForm stMoment stMoment_zero stMoment_two stMoment_neg_two μ

end MomentLaw

-- Grade-4 sanity: `E|T_0|² = 99/8`, `E|T_2|² = 7`, `E|T_4|² = 1` (atlas rationals).
#eval decide (MomentLaw.channelMoment (g := 4) MomentLaw.stMoment 0 = 99/8)
#eval decide (MomentLaw.channelMoment (g := 4) MomentLaw.stMoment 2 = 7)
#eval decide (MomentLaw.channelMoment (g := 4) MomentLaw.stMoment 4 = 1)

#print axioms MomentLaw.subsetPairSum
#print axioms MomentLaw.channelMoment_closedForm
#print axioms MomentLaw.stChannelMoment_closedForm
