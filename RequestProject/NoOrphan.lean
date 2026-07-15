import Mathlib

/-!
# The no-orphan decomposition — every frozen rail-subset carries a divisor or collective address

The Weil-rail detector (`tmp/weil_rails.py`, `no_orphan_decomposition`; `GRADE4_PROGRESS.md`
items 20–24) measured, on abelian `g`-folds, a falsifiable exhaustiveness law: the occupancy of
the invariant lattice — the frozen `g`-subsets of the `2g` rail-angles — splits with **zero
remainder** into a **divisor** part (conjugate-matched subsets) and a **collective** part, with an
**orphan** (a frozen subset carrying no address) impossible.  This file states and proves the
*model form* of that law as finite combinatorics, and reproduces the instrument's decomposition
table exactly via `#eval`.

The `2g` rail-angles are `Fin g ⊕ Fin g`: rail `a` carries `+φₐ` (`inl a`) and its conjugate
`−φₐ` (`inr a`).  Conjugation is `Sum.swap` (the fixed-point-free involution `ι`).  A `g`-subset
`S` is **ι-closed** (divisor / conjugate-matched) iff it is a union of conjugate pairs; otherwise
it is **collective** (full-support).

* `IotaClosed`, `orbitUnion`, `inlPart` — ι-closedness and the pair `ι-closed subset ↔ chosen
  rails` bijection.
* `divisor_card_eq_choose` — **the divisor count** (unconditional): for even `g`, the ι-closed
  `g`-subsets number exactly `C(g, g/2)` (choose `g/2` of the `g` conjugate pairs).
  `[g = 4 : 6; g = 6 : 20]`.
* `iotaClosed_lane_zero` — **why every divisor freezes unconditionally**: an ι-closed subset's lane
  `Σ_{x∈S} A x = 0` for any conjugation-odd angle assignment `A (ι x) = − A x`, so it is frozen at
  order 1 with no arithmetic input.
* `no_orphan` — **the law (model form)**: `occupancy = divisor + collective`, with **zero remainder
  by construction** — the frozen `g`-subsets partition into ι-closed and non-ι-closed, so an orphan
  (a frozen subset that is neither) is impossible.
* `occupancy_eq_choose_add_collective` — with every ι-closed subset frozen (the unconditional
  divisor freeze), `occupancy = C(g, g/2) + collective`, isolating all arithmetic in the collective
  count.

**The arithmetic layer (named, NOT proven here).**  Which *collective* subsets freeze — and to
what character order — is arithmetic: the collective order-1 count is `2·[ord r = 1]` for the
rail-freeze scalar `r = ∏_{n∈W} Jₙ / p^{g/2}`, and the freeze-order law `ord r = ord χ₃(D)`
(`D = disc f · disc g²`) rests on the **one unproven bridge**
`det(Frob | V_ζ) = p^{g/2} · χ₃(D)`.  This file does **not** prove that bridge; it takes the
collective freeze pattern as the `collective` input and proves only the model-layer combinatorics
(the divisor count and the zero-remainder decomposition).

**Scope.**  This is the *model* form of the no-orphan law: the divisor count `C(g, g/2)`, the
unconditional lane-zero freeze of divisors, and the exhaustive divisor/collective partition (orphan
= ∅ by construction).  Whether reality's measured occupancy matches the model — i.e. whether every
measured invariant carries a rail-freeze certificate — is the **instruments' job** (the `weil_rails`
detectors), gated on the named `det(Frob)` bridge above; that is where a genuine orphan could, in
principle, appear.  Nothing here assumes or proves RH/GRH.  No `axiom`, no `sorry`.
-/

open Finset
open scoped BigOperators

namespace NoOrphan

variable {g : ℕ}

/-- A `g`-subset of the `2g` rail-angles is **ι-closed** (divisor / conjugate-matched): closed
under conjugation `Sum.swap`, i.e. a union of conjugate pairs. -/
def IotaClosed (S : Finset (Fin g ⊕ Fin g)) : Prop := ∀ x ∈ S, Sum.swap x ∈ S

instance (S : Finset (Fin g ⊕ Fin g)) : Decidable (IotaClosed S) := by
  unfold IotaClosed; infer_instance

/-- The conjugate-pair union of a set of chosen rails `R ⊆ Fin g`: each rail contributes both its
`+φ` (`inl`) and `−φ` (`inr`) legs.  The divisor subsets are exactly these. -/
def orbitUnion (R : Finset (Fin g)) : Finset (Fin g ⊕ Fin g) :=
  R.image Sum.inl ∪ R.image Sum.inr

/-- The chosen rails of a subset: `{a : inl a ∈ S}`. -/
def inlPart (S : Finset (Fin g ⊕ Fin g)) : Finset (Fin g) := univ.filter (fun a => Sum.inl a ∈ S)

@[simp] lemma mem_orbitUnion_inl {R : Finset (Fin g)} {a : Fin g} :
    Sum.inl a ∈ orbitUnion R ↔ a ∈ R := by
  simp only [orbitUnion, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨b, hb, hab⟩ | ⟨b, _, hab⟩)
    · exact (Sum.inl_injective hab) ▸ hb
    · exact absurd hab (by simp)
  · intro h; exact Or.inl ⟨a, h, rfl⟩

@[simp] lemma mem_orbitUnion_inr {R : Finset (Fin g)} {a : Fin g} :
    Sum.inr a ∈ orbitUnion R ↔ a ∈ R := by
  simp only [orbitUnion, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨b, _, hab⟩ | ⟨b, hb, hab⟩)
    · exact absurd hab (by simp)
    · exact (Sum.inr_injective hab) ▸ hb
  · intro h; exact Or.inr ⟨a, h, rfl⟩

lemma iotaClosed_orbitUnion (R : Finset (Fin g)) : IotaClosed (orbitUnion R) := by
  intro x hx
  cases x with
  | inl a => rw [mem_orbitUnion_inl] at hx; simpa using hx
  | inr a => rw [mem_orbitUnion_inr] at hx; simpa using hx

lemma orbitUnion_card (R : Finset (Fin g)) : (orbitUnion R).card = 2 * R.card := by
  have hdisj : Disjoint (R.image Sum.inl) (R.image Sum.inr) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_image] at hx hx'
    obtain ⟨a, _, ha⟩ := hx
    obtain ⟨b, _, hb⟩ := hx'
    rw [← ha] at hb; exact absurd hb (by simp)
  rw [orbitUnion, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ Sum.inr_injective]
  ring

@[simp] lemma inlPart_orbitUnion (R : Finset (Fin g)) : inlPart (orbitUnion R) = R := by
  ext a
  simp [inlPart]

lemma orbitUnion_inlPart {S : Finset (Fin g ⊕ Fin g)} (h : IotaClosed S) :
    orbitUnion (inlPart S) = S := by
  ext x
  cases x with
  | inl a => simp [inlPart]
  | inr a =>
      rw [mem_orbitUnion_inr]
      simp only [inlPart, mem_filter, mem_univ, true_and]
      constructor
      · intro ha; have := h _ ha; simpa using this
      · intro ha; have := h _ ha; simpa using this

/-- **The divisor count** (unconditional): the ι-closed `g`-subsets — the conjugate-matched
(divisor) lanes — number exactly `C(g, g/2)`: choose `g/2` of the `g` conjugate pairs.  `g = 4 ⇒
6`, `g = 6 ⇒ 20`. -/
theorem divisor_card_eq_choose (hg : Even g) :
    ((powersetCard g (univ : Finset (Fin g ⊕ Fin g))).filter IotaClosed).card
      = Nat.choose g (g / 2) := by
  have hgg : 2 * (g / 2) = g := Nat.two_mul_div_two_of_even hg
  have hbij :
      ((powersetCard g (univ : Finset (Fin g ⊕ Fin g))).filter IotaClosed).card
        = (powersetCard (g / 2) (univ : Finset (Fin g))).card := by
    apply Finset.card_nbij' inlPart orbitUnion
    · intro S hS
      simp only [Finset.mem_coe, mem_filter, mem_powersetCard] at hS
      obtain ⟨⟨_, hcard⟩, hclosed⟩ := hS
      simp only [Finset.mem_coe, mem_powersetCard]
      refine ⟨subset_univ _, ?_⟩
      have hio := orbitUnion_inlPart hclosed
      have h2 : 2 * (inlPart S).card = g := by rw [← orbitUnion_card, hio, hcard]
      omega
    · intro R hR
      simp only [Finset.mem_coe, mem_powersetCard] at hR
      simp only [Finset.mem_coe, mem_filter, mem_powersetCard]
      refine ⟨⟨subset_univ _, ?_⟩, iotaClosed_orbitUnion R⟩
      rw [orbitUnion_card, hR.2, hgg]
    · intro S hS
      simp only [Finset.mem_coe, mem_filter] at hS
      exact orbitUnion_inlPart hS.2
    · intro R _
      exact inlPart_orbitUnion R
  rw [hbij, Finset.card_powersetCard, Finset.card_fin]

/-- **The lane-zero fact** (why every divisor freezes at order 1 with no arithmetic): for any
conjugation-odd angle assignment `A (ι x) = − A x`, an ι-closed subset's lane vanishes,
`Σ_{x∈S} A x = 0` — the `+φ` and `−φ` legs of each conjugate pair cancel. -/
theorem iotaClosed_lane_zero {M : Type*} [AddCommGroup M] (A : (Fin g ⊕ Fin g) → M)
    (hA : ∀ x, A (Sum.swap x) = - A x) {S : Finset (Fin g ⊕ Fin g)} (h : IotaClosed S) :
    ∑ x ∈ S, A x = 0 := by
  have hdisj : Disjoint ((inlPart S).image Sum.inl) ((inlPart S).image Sum.inr) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_image] at hx hx'
    obtain ⟨a, _, ha⟩ := hx
    obtain ⟨b, _, hb⟩ := hx'
    rw [← ha] at hb; exact absurd hb (by simp)
  rw [← orbitUnion_inlPart h, orbitUnion, Finset.sum_union hdisj,
    Finset.sum_image (fun a _ b _ hh => Sum.inl_injective hh),
    Finset.sum_image (fun a _ b _ hh => Sum.inr_injective hh),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  have := hA (Sum.inl a)
  simp only [Sum.swap_inl] at this
  rw [this]; abel

/-! ### The zero-remainder decomposition -/

variable (frozen : Finset (Fin g ⊕ Fin g) → Prop) [DecidablePred frozen]

/-- The **occupancy**: the number of frozen `g`-subsets (the model's total invariant count). -/
def occupancy : ℕ := ((powersetCard g (univ : Finset (Fin g ⊕ Fin g))).filter frozen).card

/-- The **divisor count**: frozen conjugate-matched (ι-closed) subsets. -/
def divisor : ℕ :=
  ((powersetCard g (univ : Finset (Fin g ⊕ Fin g))).filter (fun S => frozen S ∧ IotaClosed S)).card

/-- The **collective count**: frozen full-support (non-ι-closed) subsets. -/
def collective : ℕ :=
  ((powersetCard g (univ : Finset (Fin g ⊕ Fin g))).filter
    (fun S => frozen S ∧ ¬ IotaClosed S)).card

/-- **The no-orphan law (model form)**: `occupancy = divisor + collective`, with **zero remainder
by construction**.  The frozen `g`-subsets partition into ι-closed (divisor) and non-ι-closed
(collective) — the two cases are exhaustive, so an orphan (a frozen subset that is neither) is
impossible in the model. -/
theorem no_orphan : occupancy frozen = divisor frozen + collective frozen := by
  unfold occupancy divisor collective
  rw [← Finset.filter_filter, ← Finset.filter_filter,
    Finset.card_filter_add_card_filter_not]

/-- **The occupancy count with the unconditional divisor freeze**: if every ι-closed `g`-subset is
frozen (the lane-zero fact), then `occupancy = C(g, g/2) + collective` — the divisor part is the
unconditional `C(g, g/2)` and *all* arithmetic sits in the collective count. -/
theorem occupancy_eq_choose_add_collective (hg : Even g)
    (hdiv : ∀ S ∈ powersetCard g (univ : Finset (Fin g ⊕ Fin g)), IotaClosed S → frozen S) :
    occupancy frozen = Nat.choose g (g / 2) + collective frozen := by
  have hdiveq : divisor frozen = Nat.choose g (g / 2) := by
    unfold divisor
    rw [Finset.filter_congr (q := IotaClosed)
      (fun S hS => ⟨fun h => h.2, fun h => ⟨hdiv S hS h, h⟩⟩), divisor_card_eq_choose hg]
  rw [no_orphan, hdiveq]

end NoOrphan

/-! ### `#eval` cross-check — reproduce the instrument's decomposition table exactly

`tmp/weil_rails.py` (`no_orphan_decomposition`):

  object            g  occupancy  divisor=C(g,g/2)  collective  orphan
  fourfold (2,2)    4      8             6              2          0
  fourfold (1,3)    4      6             6              0          0
  sixfold  S1       6     22            20              2          0
  sixfold  S2       6     20            20              0          0

`collective = 2·[ord r = 1]` is the arithmetic-supplied input.  `orphan = 0` by construction. -/

/-- `(divisor, occupancy, orphan)` for a `g`-fold with a given collective count. -/
def NoOrphan.decompRow (g coll : ℕ) : ℕ × ℕ × ℕ :=
  (Nat.choose g (g / 2), Nat.choose g (g / 2) + coll, 0)

-- Instrument table (divisor, occupancy, orphan):
#eval NoOrphan.decompRow 4 2   -- (6, 8, 0)   fourfold (2,2)
#eval NoOrphan.decompRow 4 0   -- (6, 6, 0)   fourfold (1,3)
#eval NoOrphan.decompRow 6 2   -- (20, 22, 0) sixfold S1
#eval NoOrphan.decompRow 6 0   -- (20, 20, 0) sixfold S2

-- Brute enumeration confirms the divisor formula `C(g, g/2)` against the ι-closed count:
#eval decide
  (((powersetCard 4 (Finset.univ : Finset (Fin 4 ⊕ Fin 4))).filter NoOrphan.IotaClosed).card = 6)
#eval decide
  (((powersetCard 6 (Finset.univ : Finset (Fin 6 ⊕ Fin 6))).filter NoOrphan.IotaClosed).card = 20)

#print axioms NoOrphan.divisor_card_eq_choose
#print axioms NoOrphan.iotaClosed_lane_zero
#print axioms NoOrphan.no_orphan
#print axioms NoOrphan.occupancy_eq_choose_add_collective
