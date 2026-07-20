import Mathlib

/-!
# The carrier loss-ledger filtration: abstract logical core

Formalizes the **abstract logical core** of the carrier-tower ↔ cycle-filtration correspondence of
the paper (§Status, the box `first nonzero carrier tower depth = filtration depth`).  For an
arbitrary tower of readouts `T : ℕ → Z → V` — the level-`d` carrier/tensor-tower ledger coordinate,
`Z` the declared cycle/motivic object, `V` its level-`d` realization — the *carrier filtration* is

  `carrierFiltration T d = { z | ∀ j < d, T j z = 0 }`.

Everything here is proved with **no reference to any Bloch–Beilinson depth** (non-circular: the
filtration is cut out purely by the tower `T`), unconditionally, with the standard axiom footprint:

* `carrierFiltration_zero`, `carrierFiltration_antitone`, `carrierFiltration_succ_subset` — it is an
  antitone filtration with top `= univ`;
* `mem_carrierFiltration_succ` / `ledger_kernel` — the **graded-kernel law**
  `z ∈ F (d+1) ↔ z ∈ F d ∧ T d z = 0`: the level-`d` readout is a *faithful graded ledger
  coordinate*, its kernel on `F d` being exactly `F (d+1)`;
* `no_early_detection` (`z ∈ F d → ∀ j < d, T j z = 0`, direction **B / no-early-detection**) and
  `grade_visibility` (`z ∈ F d \ F (d+1) → T d z ≠ 0`, direction **A / no-late-detection at grade d**);
* `isFirstVisible_iff`, `isFirstVisible_unique`, `firstVisibleDepth_eq_grade` — the **depth
  equivalence** `firstNonzeroCarrierDepth z = d ↔ z ∈ F d ∧ z ∉ F (d+1)`, with `d` unique;
* `gradeLedger_injective` — under additive readouts, two grade-`d` classes with equal level-`d`
  ledger differ by an element of `F (d+1)` (the genuine graded-ledger injection);
* `carrierFiltration_map`, `carrierFiltration_map_iff`, `isFirstVisible_map_iff` — **functorial
  transport**: a faithful (readout-intertwining, injective) transport preserves the filtration and
  the first-visible depth;
* `carrierFiltration_unique` and `blochBeilinson_coincides` — **uniqueness**: any filtration whose
  graded pieces are cut out by the same tower equals `carrierFiltration T`.  Exact strength of the
  corollary: its hypothesis `hBBsucc` *already asserts* that every successive BB step is cut out by
  this very tower — far stronger than the existence of a Bloch–Beilinson filtration with its usual
  (conjectural) properties — so the statement is recursion bookkeeping (any filtration recursively
  defined by these tower kernels equals the filtration so defined), NOT an independent
  identification of the carrier filtration with Bloch–Beilinson.  The identification content lives
  entirely in verifying `hBBsucc` for an independently constructed BB filtration, which is open.

What is **NOT** proved here — and stated as explicit hypotheses (`Exhaustive`) or left to the paper:
the no-silent-layer / tower-completeness input (`Exhaustive T`, numerically supported, not proved),
and the arithmetic level-`d` landings (`|Ш|` at 1, CM at 2, Gross–Schoen/Ceresa height at 3, the last
consuming Zhang / Yuan–Zhang–Zhang).  This file is the abstract skeleton those inputs would populate.

No `sorry`, no `axiom`.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {Z V : Type*}

section Core
variable [Zero V]

/-- The **carrier filtration**: `z` is in level `d` iff every tower readout below `d` vanishes on it. -/
def carrierFiltration (T : ℕ → Z → V) (d : ℕ) : Set Z := {z | ∀ j < d, T j z = 0}

theorem mem_carrierFiltration {T : ℕ → Z → V} {d : ℕ} {z : Z} :
    z ∈ carrierFiltration T d ↔ ∀ j < d, T j z = 0 := Iff.rfl

/-- The top of the filtration is everything (vacuous condition). -/
theorem carrierFiltration_zero (T : ℕ → Z → V) : carrierFiltration T 0 = Set.univ := by
  ext z
  simp only [carrierFiltration, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact fun j hj => absurd hj (Nat.not_lt_zero j)

/-- **The graded-kernel law.** Membership at level `d+1` is membership at level `d` together with the
vanishing of the level-`d` readout — so the kernel of `T d` on `F d` is exactly `F (d+1)`. -/
theorem mem_carrierFiltration_succ {T : ℕ → Z → V} {d : ℕ} {z : Z} :
    z ∈ carrierFiltration T (d+1) ↔ z ∈ carrierFiltration T d ∧ T d z = 0 := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h d (Nat.lt_succ_self d)⟩
  · rintro ⟨hd, hlast⟩ j hj
    rcases (Nat.lt_succ_iff.mp hj).lt_or_eq with hlt | heq
    · exact hd j hlt
    · exact heq ▸ hlast

theorem carrierFiltration_succ_subset (T : ℕ → Z → V) (d : ℕ) :
    carrierFiltration T (d+1) ⊆ carrierFiltration T d :=
  fun _ h => (mem_carrierFiltration_succ.mp h).1

/-- The carrier filtration is antitone: higher levels are smaller. -/
theorem carrierFiltration_antitone (T : ℕ → Z → V) : Antitone (carrierFiltration T) := by
  intro d e hde z hz j hj
  exact hz j (hj.trans_le hde)

/-- **Faithful graded ledger coordinate.** On `F d`, the level-`d` readout `T d` vanishes exactly on
`F (d+1)`: the graded piece `F d / F (d+1)` is separated by `T d`. -/
theorem ledger_kernel {T : ℕ → Z → V} {z : Z} {d : ℕ} (hz : z ∈ carrierFiltration T d) :
    T d z = 0 ↔ z ∈ carrierFiltration T (d+1) := by
  rw [mem_carrierFiltration_succ]
  exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩

/-- `z` is **first visible at depth `d`** iff all readouts below `d` vanish and the `d`-th does not. -/
def IsFirstVisible (T : ℕ → Z → V) (z : Z) (d : ℕ) : Prop :=
  (∀ j < d, T j z = 0) ∧ T d z ≠ 0

/-- **The depth equivalence.** First-visible-at-`d` is exactly `z ∈ F d \ F (d+1)`. -/
theorem isFirstVisible_iff {T : ℕ → Z → V} {z : Z} {d : ℕ} :
    IsFirstVisible T z d ↔ z ∈ carrierFiltration T d ∧ z ∉ carrierFiltration T (d+1) := by
  constructor
  · rintro ⟨hlt, hlast⟩
    exact ⟨hlt, fun h => hlast (mem_carrierFiltration_succ.mp h).2⟩
  · rintro ⟨hmem, hnmem⟩
    exact ⟨hmem, fun hlast => hnmem (mem_carrierFiltration_succ.mpr ⟨hmem, hlast⟩)⟩

/-- **Direction B (no early detection).** A class of filtration level `≥ d` is silent below `d`. -/
theorem no_early_detection {T : ℕ → Z → V} {z : Z} {d : ℕ}
    (h : z ∈ carrierFiltration T d) : ∀ j < d, T j z = 0 := h

/-- **Direction A (no late detection at grade `d`).** A genuine grade-`d` class fires at level `d`. -/
theorem grade_visibility {T : ℕ → Z → V} {z : Z} {d : ℕ}
    (hmem : z ∈ carrierFiltration T d) (hnmem : z ∉ carrierFiltration T (d+1)) :
    T d z ≠ 0 :=
  (isFirstVisible_iff.mpr ⟨hmem, hnmem⟩).2

/-- The first-visible depth is unique. -/
theorem isFirstVisible_unique {T : ℕ → Z → V} {z : Z} {d e : ℕ}
    (hd : IsFirstVisible T z d) (he : IsFirstVisible T z e) : d = e := by
  rcases lt_trichotomy d e with h | h | h
  · exact absurd (he.1 d h) hd.2
  · exact h
  · exact absurd (hd.1 e h) he.2

/-- `z` is **detectable** if some tower level sees it. This is the per-class no-silent-layer input. -/
def Detectable (T : ℕ → Z → V) (z : Z) : Prop := ∃ d, T d z ≠ 0

/-- A detectable class has a first-visible depth. -/
theorem exists_isFirstVisible {T : ℕ → Z → V} {z : Z} (h : Detectable T z) :
    ∃ d, IsFirstVisible T z d := by
  classical
  refine ⟨Nat.find h, fun j hj => ?_, Nat.find_spec h⟩
  by_contra hj0
  exact Nat.find_min h hj hj0

/-- The **first nonzero carrier depth** of a detectable class. -/
noncomputable def firstVisibleDepth {T : ℕ → Z → V} {z : Z} (h : Detectable T z) : ℕ :=
  Classical.choose (exists_isFirstVisible h)

theorem firstVisibleDepth_isFirstVisible {T : ℕ → Z → V} {z : Z} (h : Detectable T z) :
    IsFirstVisible T z (firstVisibleDepth h) :=
  Classical.choose_spec (exists_isFirstVisible h)

theorem firstVisibleDepth_eq_iff {T : ℕ → Z → V} {z : Z} {d : ℕ} (h : Detectable T z) :
    firstVisibleDepth h = d ↔ IsFirstVisible T z d :=
  ⟨fun he => he ▸ firstVisibleDepth_isFirstVisible h,
   fun hd => isFirstVisible_unique (firstVisibleDepth_isFirstVisible h) hd⟩

/-- **The headline correspondence.** `firstNonzeroCarrierDepth z = d ↔ z ∈ F d ∧ z ∉ F (d+1)`:
the first nonzero carrier tower depth equals the carrier-filtration depth (unconditional given
detectability). -/
theorem firstVisibleDepth_eq_grade {T : ℕ → Z → V} {z : Z} {d : ℕ} (h : Detectable T z) :
    firstVisibleDepth h = d ↔
      (z ∈ carrierFiltration T d ∧ z ∉ carrierFiltration T (d+1)) := by
  rw [firstVisibleDepth_eq_iff, isFirstVisible_iff]

/-- **The no-silent-layer / tower-completeness hypothesis** (the paper's "tower completeness";
numerically supported, *not* proved here). -/
def Exhaustive [Zero Z] (T : ℕ → Z → V) : Prop := ∀ z : Z, z ≠ 0 → Detectable T z

/-- Under exhaustion every nonzero class has a well-defined first-visible depth. -/
theorem exhaustive_firstVisible [Zero Z] {T : ℕ → Z → V} (hex : Exhaustive T) {z : Z}
    (hz : z ≠ 0) : IsFirstVisible T z (firstVisibleDepth (hex z hz)) :=
  firstVisibleDepth_isFirstVisible _

/-- **Uniqueness.** Any filtration `G` whose top is everything and whose graded pieces are cut out by
the same tower (`G (d+1) = { z ∈ G d | T d z = 0 }`) equals the carrier filtration. -/
theorem carrierFiltration_unique {T : ℕ → Z → V} (G : ℕ → Set Z)
    (hG0 : G 0 = Set.univ)
    (hGsucc : ∀ d, G (d+1) = {z | z ∈ G d ∧ T d z = 0}) :
    G = carrierFiltration T := by
  funext d
  induction d with
  | zero => rw [hG0, carrierFiltration_zero]
  | succ d ih =>
      rw [hGsucc, ih]
      ext z
      rw [Set.mem_setOf_eq, mem_carrierFiltration_succ]

/-- **Tower-graded coincidence (Bloch–Beilinson reading, exact strength).** If a filtration `BB`
has top `univ` and each successive step cut out by the carrier tower (`hBBsucc`), it equals
`carrierFiltration T`.  Note the strength: `hBBsucc` is not "a Bloch–Beilinson filtration exists" —
it already asserts that every BB step is graded by this very tower, so the theorem is
`carrierFiltration_unique` bookkeeping, not an independent identification with Bloch–Beilinson.
Verifying `hBBsucc` for an independently constructed BB filtration is the open identification
step; nothing here supplies it. -/
theorem blochBeilinson_coincides {T : ℕ → Z → V} (BB : ℕ → Set Z)
    (hBB0 : BB 0 = Set.univ)
    (hBBsucc : ∀ d, BB (d+1) = {z | z ∈ BB d ∧ T d z = 0}) :
    BB = carrierFiltration T :=
  carrierFiltration_unique BB hBB0 hBBsucc

end Core

section Transport
variable {Z' V' : Type*} [Zero V] [Zero V']

/-- **Functorial transport (membership).** A readout-intertwining transport carries the filtration
forward. -/
theorem carrierFiltration_map {d : ℕ}
    (φ : Z → Z') (T : ℕ → Z → V) (T' : ℕ → Z' → V') (ψ : ℕ → V → V')
    (hψ0 : ∀ j, ψ j 0 = 0) (hcomm : ∀ j z, T' j (φ z) = ψ j (T j z))
    {z : Z} (hz : z ∈ carrierFiltration T d) : φ z ∈ carrierFiltration T' d := by
  intro j hj
  rw [hcomm, hz j hj, hψ0]

/-- **Faithful transport (equivalence).** If each level intertwiner is injective and zero-preserving,
the transport preserves filtration membership exactly. -/
theorem carrierFiltration_map_iff {d : ℕ}
    (φ : Z → Z') (T : ℕ → Z → V) (T' : ℕ → Z' → V') (ψ : ℕ → V → V')
    (hψ0 : ∀ j, ψ j 0 = 0) (hψinj : ∀ j, Function.Injective (ψ j))
    (hcomm : ∀ j z, T' j (φ z) = ψ j (T j z)) {z : Z} :
    φ z ∈ carrierFiltration T' d ↔ z ∈ carrierFiltration T d := by
  constructor
  · intro h j hj
    have hj' := h j hj
    rw [hcomm] at hj'
    have : ψ j (T j z) = ψ j 0 := by rw [hj', hψ0]
    exact hψinj j this
  · exact fun hz => carrierFiltration_map φ T T' ψ hψ0 hcomm hz

/-- **Depth preservation under faithful transport.** First-visible depth is a transport invariant. -/
theorem isFirstVisible_map_iff {d : ℕ}
    (φ : Z → Z') (T : ℕ → Z → V) (T' : ℕ → Z' → V') (ψ : ℕ → V → V')
    (hψ0 : ∀ j, ψ j 0 = 0) (hψinj : ∀ j, Function.Injective (ψ j))
    (hcomm : ∀ j z, T' j (φ z) = ψ j (T j z)) {z : Z} :
    IsFirstVisible T' (φ z) d ↔ IsFirstVisible T z d := by
  rw [isFirstVisible_iff, isFirstVisible_iff,
    carrierFiltration_map_iff φ T T' ψ hψ0 hψinj hcomm,
    carrierFiltration_map_iff φ T T' ψ hψ0 hψinj hcomm]

end Transport

section Additive
variable [AddCommGroup Z] [AddCommGroup V]

/-- **Graded ledger injection.** Under additive readouts, two grade-`d` classes with equal level-`d`
ledger differ by an element of `F (d+1)`: the induced map `F d / F (d+1) → V`, `z ↦ T d z`, is
injective. -/
theorem gradeLedger_injective (T : ℕ → Z → V)
    (hTsub : ∀ j (a b : Z), T j (a - b) = T j a - T j b)
    {d : ℕ} {z w : Z} (hz : z ∈ carrierFiltration T d) (hw : w ∈ carrierFiltration T d)
    (h : T d z = T d w) : z - w ∈ carrierFiltration T (d+1) := by
  rw [mem_carrierFiltration_succ]
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [hTsub, hz j hj, hw j hj, sub_zero]
  · rw [hTsub, h, sub_self]

end Additive

section Radical
variable [Zero V]

/-- **The carrier radical**: the classes invisible to *every* tower level,
`R = ⋂_d ker T_d`.  The whole no-silent-layer question is *identify `R`* — emphatically **not**
"inherit the kernel of some fixed lower realization (complex Abel–Jacobi, ordinary Hodge)". -/
def radical (T : ℕ → Z → V) : Set Z := {z | ∀ d, T d z = 0}

theorem mem_radical {T : ℕ → Z → V} {z : Z} : z ∈ radical T ↔ ∀ d, T d z = 0 := Iff.rfl

/-- Outside the radical `⇔` detectable: exhaustion on `Z ⧸ R` is free (tautological). -/
theorem not_mem_radical_iff_detectable {T : ℕ → Z → V} {z : Z} :
    z ∉ radical T ↔ Detectable T z := by
  constructor
  · intro h; exact not_forall.mp h
  · rintro ⟨d, hd⟩ h; exact hd (h d)

/-- The radical sits inside every filtration level. -/
theorem radical_subset_carrierFiltration (T : ℕ → Z → V) (d : ℕ) :
    radical T ⊆ carrierFiltration T d :=
  fun _ hz j _ => hz j

/-- **No-silent-layer `=` trivial radical.** If the only tower-invisible class is `0`, exhaustion
holds.  This localizes the entire problem to `R = 0`. -/
theorem exhaustive_of_radical_trivial [Zero Z] {T : ℕ → Z → V}
    (h : ∀ z, z ∈ radical T → z = 0) : Exhaustive T :=
  fun z hz => not_mem_radical_iff_detectable.mp (fun hmem => hz (h z hmem))

/-- **Gradewise nondegeneracy ⇒ visibility.** If the level-`d` readout factors through an
*anisotropic* pairing `B` of a regulator `reg`, a class with nonzero regulator fires at level `d`.
This converts "tower completeness" into a family of nondegeneracy obligations: `reg_d` faithful on
`Gr^d` and `B_d` anisotropic (e.g. Néron–Tate positivity at `d = 1`). -/
theorem grade_visible_of_nondegenerate {T : ℕ → Z → V} {d : ℕ} {W : Type*} [Zero W]
    (reg : Z → W) (B : W → W → V) (hfac : ∀ z, T d z = B (reg z) (reg z))
    (hanis : ∀ w : W, w ≠ 0 → B w w ≠ 0) {z : Z} (hreg : reg z ≠ 0) : T d z ≠ 0 := by
  rw [hfac]; exact hanis _ hreg

/-- **The radical inherits `ker π` ONLY under factorization.** If *every* tower level factors through
a fixed projection `π` (a lower realization — the complex Abel–Jacobi map, ordinary Hodge), then
`ker π ⊆ R`.  This factorization is exactly the hypothesis an "invisibility" claim requires; it is
not automatic. -/
theorem radical_of_factorsThrough {T : ℕ → Z → V} {P : Type*} [Zero P]
    (π : Z → P) (g : ℕ → P → V) (hg0 : ∀ d, g d 0 = 0) (hfac : ∀ d z, T d z = g d (π z))
    {z : Z} (hz : π z = 0) : z ∈ radical T := by
  intro d; rw [hfac, hz, hg0]

/-- **No free invisibility (the correction to the imported-ceiling error).** A single tower level
detecting a `π`-killed class keeps that class **out** of the radical.  Hence `π(z)=0 ⇒ ∀ d, T_d z = 0`
is *false* without a factorization theorem at every level: a class invisible to a fixed realization
`π` need not lie in the carrier radical.  This is the exact gap in "transcendental Griffiths ⊆ `R`". -/
theorem not_mem_radical_of_detectedPast {T : ℕ → Z → V} {P : Type*} [Zero P]
    (π : Z → P) {z : Z} {d : ℕ} (_hz : π z = 0) (hdet : T d z ≠ 0) : z ∉ radical T :=
  fun hmem => hdet (hmem d)

end Radical

end CriticalLinePhasor.HodgeLedgerFiltration
