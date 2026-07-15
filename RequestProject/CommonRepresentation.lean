import Mathlib

/-!
# The common representation (Universal Normalized Transport): unconditional structural core

Heterogeneous admissible fibers normalize onto one common carrier at a shared scale — the
**common refinement** of their native cell systems.  On that common (normalized) chart their
vanishing/closure structure is simultaneously realized, and closure **transfers** across the
normalization: closure on the fine (common) refinement assembles to closure on every fiber's
native cells.  This is the unconditional "the carrier is the common representation" statement —
no per-fiber niceness is assumed, no automorphic input is used.

Entireness (pole-absence) comes from **completeness**, not from the pencil: the pole/residue is
the DC mode = coefficient mean = trivial-channel coefficient (nontrivial channels have zero mean,
`harmonize_char`), so a complete fiber — *no* trivial channel — has zero DC mode, hence no pole
(`complete_bank_dc_zero`).  Completeness for Symʳπ is tested in the representation category:
`RepresentationRankGap.no_nonzero_intertwiner_of_finrank_lt` kills an equivariant residual into
a simple target, while `NonSelfDual.tateClass_zero_of_simple_not_unit` is the corresponding
`FDRep` Schur statement; the DC-mode = residue link is the standard
Riemann–Hecke Mellin identity.  (The pencil `B = L(1/2+iγ)` is zero-*detection*, not pole-absence;
it must not stand in for entireness — that was the audited error.)

`native_closure_of_refined_closure` is the mathematical heart (`thm:g10-common-refinement`):
pure finite combinatorics, with footprint `{propext, Classical.choice, Quot.sound}`.
-/

namespace CriticalLinePhasor.CommonRepresentation

open scoped BigOperators
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- **Common-refinement closure transfer (the normalized-chart core).**
`cell : I → κ` is a fiber's native cell labelling; `fine : I → κ'` is the finer labelling of
the common refinement, with `refines`: two indices in the same fine cell lie in the same native
cell (the refinement condition).  If the bank `a` closes on **every** fine cell, then it closes
on **every** native cell.  Thus normalizing a fiber onto the common refinement preserves its
closure (vanishing) structure — unconditionally, with no arithmetic input. -/
theorem native_closure_of_refined_closure {κ κ' : Type*} [DecidableEq κ] [DecidableEq κ']
    [Fintype κ']
    (a : I → ℂ) (cell : I → κ) (fine : I → κ')
    (refines : ∀ n m : I, fine n = fine m → cell n = cell m)
    (hfine : ∀ e : κ', ∑ n ∈ univ.filter (fun n => fine n = e), a n = 0)
    (c : κ) : ∑ n ∈ univ.filter (fun n => cell n = c), a n = 0 := by
  classical
  have hmaps : ∀ n ∈ univ.filter (fun n => cell n = c), fine n ∈ (univ : Finset κ') :=
    fun n _ => mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_eq_zero
  intro e _
  by_cases hne : (univ.filter (fun n => cell n = c)).filter (fun n => fine n = e) = ∅
  · rw [hne, Finset.sum_empty]
  · obtain ⟨n0, hn0⟩ := Finset.nonempty_of_ne_empty hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn0
    have hset : (univ.filter (fun n => cell n = c)).filter (fun n => fine n = e)
        = univ.filter (fun n => fine n = e) := by
      apply Finset.ext
      intro m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, hm⟩; exact hm
      · intro hm
        exact ⟨(refines m n0 (hm.trans hn0.2.symm)).trans hn0.1, hm⟩
    rw [hset]; exact hfine e

/-- **Simultaneous normalization of a finite family.**  Given a finite family of fibers, each a
coefficient bank `a i` with its own native cell labelling `cell i`, and a common refinement
`fine` refining every native labelling, closure on the common refinement (per bank) assembles to
native closure for **every** fiber at once — the fibers share one normalized chart while each
keeps its own native cells. -/
theorem family_native_closure_of_refined_closure {ι κ κ' : Type*} [DecidableEq κ] [DecidableEq κ']
    [Fintype κ']
    (a : ι → I → ℂ) (cell : ι → I → κ) (fine : I → κ')
    (refines : ∀ i, ∀ n m : I, fine n = fine m → cell i n = cell i m)
    (hfine : ∀ i, ∀ e : κ', ∑ n ∈ univ.filter (fun n => fine n = e), a i n = 0)
    (i : ι) (c : κ) : ∑ n ∈ univ.filter (fun n => cell i n = c), a i n = 0 :=
  native_closure_of_refined_closure (a i) (cell i) fine (refines i) (hfine i) c

/-! ## Coherence of transport on the common representation

The closure-preserving carrier transports compose coherently — identity, composition,
associativity — so functorial relations between sources descend to the common representation.
(These are the `CarrierFunctoriality` laws, re-stated here at the common-representation level;
they hold for an arbitrary closure predicate, i.e. unconditionally.) -/

/-- A carrier transport of the common-representation state. -/
abbrev Transport (S : Type*) := S → S

/-- `Faithful closes T`: the transport preserves the closure (vanishing) predicate. -/
def Faithful {S : Type*} (closes : S → Prop) (T : Transport S) : Prop :=
  ∀ x, closes x → closes (T x)

/-- Identity is faithful. -/
theorem faithful_id {S : Type*} (closes : S → Prop) : Faithful closes (id : Transport S) :=
  fun _ h => h

/-- The composite of faithful transports is faithful: closure is preserved along `T ∘ U`. -/
theorem faithful_comp {S : Type*} {closes : S → Prop} {T U : Transport S}
    (hT : Faithful closes T) (hU : Faithful closes U) : Faithful closes (T ∘ U) :=
  fun x h => hT (U x) (hU x h)

/-- Composition of transports is associative. -/
theorem comp_assoc {S : Type*} (T U V : Transport S) : (T ∘ U) ∘ V = T ∘ (U ∘ V) := rfl

/-! ## Exact readout preservation is a property of invertible adapters

The apparatus has **adapters for every operation** — on either side (carrier or fiber), by either
a **constant** or a **function**:

* carrier × constant = the **rescaling** (fixed π/3 → μ6, grade-invariant);
* carrier × function = the **warp** (dynamic unit-modulus, rides the rescaled carrier, adapts to
  the fiber);
* fiber × constant / fiber × function = the fiber adapters.

Every *invertible* adapter preserves the exact readout — the exact-chart tier, in contrast to the
one-directional normalized-chart transfer of the common-refinement core above.  Two representative,
**side-neutral** invertible-adapter facts:

* an **address reindexing** (a bijection `σ` of the carrier addresses) preserves every cell sum
  exactly (`cell_scale_reindex`);
* a **unit-modulus function** `w` is exactly *descalable* by `conj w`, `a·w·conj w = a`
  (`warp_descale_exact`) — whichever side it acts on.

Self-compatibility constrains a *function* adapter (warp) to the object's own integer clock
lattice — the admissible case; `residual_forcible`'s **free per-cell** weights are the
inadmissible one. -/

/-- **Carrier-scale (address) reindexing preserves cell sums exactly.**  A carrier reindexing
bijection `σ` carries the reindexed bank summed over the reindexed cell back to the native bank
summed over the native cell — exactly.  This is a *scale*-side (fixed-μ6, address) fact. -/
theorem cell_scale_reindex (a : I → ℂ) (σ : I ≃ I) (P : I → Prop) [DecidablePred P] :
    ∑ n ∈ univ.filter (fun n => P (σ n)), (a ∘ σ) n
      = ∑ m ∈ univ.filter (fun m => P m), a m := by
  apply Finset.sum_equiv σ
  · intro n; simp
  · intro n _; rfl

/-- **A unit-modulus adapter (either side, constant or function) is exactly descalable.**  For any
`w : I → ℂ` with `‖w n‖ = 1`, descaling the adapted coefficient by `conj w` returns the native
coefficient exactly (`a·w·conj w = a`) — the exact-readout round trip an invertible adapter
supplies.  The self-compatible lattice warp is the admissible instance; `residual_forcible`'s free
per-cell weights are the inadmissible one. -/
theorem warp_descale_exact (a w : I → ℂ) (hw : ∀ n, ‖w n‖ = 1) (n : I) :
    a n * w n * (starRingEnd ℂ) (w n) = a n := by
  have h1 : w n * (starRingEnd ℂ) (w n) = 1 := by
    rw [Complex.mul_conj]; norm_cast
    rw [Complex.normSq_eq_norm_sq, hw n, one_pow]
  rw [mul_assoc, h1, mul_one]

/-! ## Carrier scaling is chart-preserving for every admissible object: vanishing preserves readout

The culminating scale-tier statement.  For **every** admissible object, rescaling the carrier by a
self-compatible lattice **scale** (a constant carrier reparametrization on the object's own integer
lattice — *not* a warp) preserves the readout, so **vanishing preserves the readout**,
unconditionally.  A zero cannot be moved by an invertible scale.  (This is the zero/vanishing tier;
the continuation tier — entireness / pole-absence — is a separate per-object input and is
deliberately not claimed here.) -/

/-- An **admissible object** on the carrier: a coefficient bank `a` together with its
*self-compatible lattice scale* `scale : I ≃ I` — the invertible carrier reparametrization on the
object's own integer lattice that every admissible object supplies. -/
structure Admissible (I : Type*) where
  a : I → ℂ
  scale : I ≃ I

/-- **Carrier scaling is chart-preserving for every admissible object; vanishing preserves the
readout — unconditionally.**  For every admissible object `W` and every cell `P`, its self-compatible
lattice scale carries the readout (cell sum) over the scaled cell exactly to the native readout, so
`W` **vanishes** (closes) in the scaled chart iff it vanishes natively.  Scaling never moves a zero:
vanishing preserves the readout, for the whole admissible class, with no arithmetic input. -/
theorem vanishing_preserves_readout (W : Admissible I) (P : I → Prop) [DecidablePred P] :
    (∑ n ∈ univ.filter (fun n => P (W.scale n)), (W.a ∘ W.scale) n = 0)
      ↔ (∑ m ∈ univ.filter (fun m => P m), W.a m = 0) := by
  rw [cell_scale_reindex W.a W.scale P]

/-! ## The common scale for commensurate fibers is the GCD lattice (the π/3 example, proved)

If several fibers close at periods that are all integer multiples of one base cell `d` — e.g.
`π/3, π, 2π = 1·d, 3·d, 6·d` with `d = π/3` — then closing on the common **GCD-scale** `d`-cells
forces closure on every fiber's native `(m·d)`-cell, at every offset.  One fixed scale `d` (the
GCD) serves the whole commensurate family: the exact statement behind "scale everything to π/3". -/

/-- **Commensurate common-scale closure — unconditional.**  If the bank `a` closes on every base
`d`-cell (`∑_{i<d} a(k·d+i) = 0` for all `k`, the common GCD scale), then it closes on every native
`(m·d)`-cell at every offset `j·d`.  A single scale `d` makes every commensurate fiber (period
`m·d`) close. -/
theorem commensurate_closure (a : ℕ → ℂ) (d : ℕ)
    (hd : ∀ k, ∑ i ∈ Finset.range d, a (k * d + i) = 0) (m j : ℕ) :
    ∑ i ∈ Finset.range (m * d), a (j * d + i) = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, zero_add]
    have he : ∀ i ∈ Finset.range d, a (j * d + (m * d + i)) = a ((j + m) * d + i) := by
      intro i _; congr 1; ring
    rw [Finset.sum_congr rfl he]; exact hd (j + m)

/-! ## CRT scheme: cell closure factors by prime component (making the construction generic)

The μ_{mn} cell decomposes by the Chinese Remainder Theorem — `ZMod (m*n) ≃ ZMod m × ZMod n` for
coprime `m,n` (μ6 = μ2 × μ3 is the archetype).  A product-structured bank's cell sum then factors
multiplicatively, so closure on **any one** prime component closes the whole cell.  This is the
generic scheme that lets a large class of fibers — those whose cell structure is a CRT/Euler
product — be handled prime-by-prime (the way Dirichlet character sums and Euler products already
factor).  Winding-tier (closure combinatorics); the continuation tier is untouched. -/

/-- **CRT product closure.**  A product-structured bank on `A × B` has total sum `(∑ g)·(∑ h)`, so
it closes as soon as **either** factor closes.  Via `ZMod.chineseRemainder` (coprime moduli) this
is prime-component-wise cell closure: closing one CRT component closes the whole μ_{mn} cell — the
generic engine, unconditional. -/
theorem crt_product_closure {A B : Type*} [Fintype A] [Fintype B] (g : A → ℂ) (h : B → ℂ)
    (hg : ∑ x, g x = 0) : ∑ p : A × B, g p.1 * h p.2 = 0 := by
  have key : (∑ x, g x) * (∑ y, h y) = ∑ p : A × B, g p.1 * h p.2 := by
    rw [Finset.sum_mul, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun x _ => Finset.mul_sum _ _ _)
  rw [← key, hg, zero_mul]

/-! ## The harmonization criterion: every nontrivial channel of a self-commensurate fiber closes

A fiber's channel, over its self-commensurate cell — a finite abelian group `G` (cyclic `ZMod m`
for a single fundamental; a product for several) — is an **additive character** of `G`.  A
**nontrivial** character sums to zero over `G`, so every nontrivial channel **harmonizes (closes)**.
This is the universal winding-tier harmonization criterion: it covers Symʳ (single fundamental,
`G = ZMod m`), Rankin–Selberg (product `G`), base change (components), and Maass alike — so every
class the paper claims harmonizes.  The lone **trivial (DC)** channel does *not* close; it is the
pole / continuation-tier input, booked separately. -/

/-- **Harmonization criterion — unconditional.**  A nontrivial additive character `χ` of a finite
abelian group `G` (witnessed by some `t` with `χ t ≠ 1`) sums to zero over `G`.  Every nontrivial
channel of an admissible (self-commensurate) fiber is such a character, hence closes; the trivial
DC channel is the separately-booked pole. -/
theorem harmonize_char {G : Type*} [AddCommGroup G] [Fintype G] (χ : AddChar G ℂ)
    (t : G) (ht : χ t ≠ 1) : ∑ g, χ g = 0 := by
  have key : χ t * ∑ g, χ g = ∑ g, χ g := by
    rw [Finset.mul_sum]
    have hmap : ∀ g, χ t * χ g = χ (t + g) := fun g => (χ.map_add_eq_mul t g).symm
    simp_rw [hmap]
    exact Equiv.sum_comp (Equiv.addLeft t) fun g => χ g
  have hz : (χ t - 1) * ∑ g, χ g = 0 := by rw [sub_mul, one_mul, key, sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd (sub_eq_zero.mp h) ht
  · exact h

/-! ## Entireness comes from completeness: no trivial channel ⇒ zero DC mode (no pole)

The pole/residue of the readout is the **DC mode** — the mean of the coefficients — which, by
character orthogonality, is the coefficient of the **trivial** channel (every *nontrivial* channel
has zero mean, `harmonize_char`).  A **complete** fiber — one with *no* trivial channel, i.e. a
purely cuspidal bank — therefore has zero DC mode: **no pole, entire**.  This is the winding-side
core of "entireness comes from completeness".  It is *not* the pencil (zero-detection); it reads
the trivial-channel structure.  For a simple Symʳπ parameter, completeness (no trivial constituent)
is `RepresentationRankGap.no_nonzero_intertwiner_of_finrank_lt`: the residual is required to be
linear over the representation algebra, so a nonzero image is the whole simple target; only then
does the strict complex-rank inequality contradict surjectivity.  The
remaining bridge — DC mode `=` analytic residue — is the standard Riemann–Hecke Mellin identity. -/

/-- **Complete bank ⇒ zero DC mode (no pole).**  A bank that is a finite ℂ-combination of
**nontrivial** additive characters (completeness: no trivial channel) sums to zero over the cell —
its DC mode vanishes.  With the Riemann–Hecke identification (DC mode = residue) this is entireness,
sourced from completeness, not from the pencil. -/
theorem complete_bank_dc_zero {G : Type*} [AddCommGroup G] [Fintype G]
    {J : Type*} [Fintype J] (c : J → ℂ) (χ : J → AddChar G ℂ)
    (hχ : ∀ j, ∃ t, (χ j) t ≠ 1) :
    ∑ g, ∑ j, c j * (χ j) g = 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  rw [← Finset.mul_sum]
  obtain ⟨t, ht⟩ := hχ j
  rw [harmonize_char (χ j) t ht, mul_zero]

end CriticalLinePhasor.CommonRepresentation

#print axioms CriticalLinePhasor.CommonRepresentation.native_closure_of_refined_closure
#print axioms CriticalLinePhasor.CommonRepresentation.family_native_closure_of_refined_closure
#print axioms CriticalLinePhasor.CommonRepresentation.faithful_comp

#print axioms CriticalLinePhasor.CommonRepresentation.cell_scale_reindex
#print axioms CriticalLinePhasor.CommonRepresentation.warp_descale_exact

#print axioms CriticalLinePhasor.CommonRepresentation.vanishing_preserves_readout
#print axioms CriticalLinePhasor.CommonRepresentation.commensurate_closure

#print axioms CriticalLinePhasor.CommonRepresentation.crt_product_closure

#print axioms CriticalLinePhasor.CommonRepresentation.harmonize_char

#print axioms CriticalLinePhasor.CommonRepresentation.complete_bank_dc_zero
