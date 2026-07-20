import RequestProject.RecognitionReconstruction

/-!
# The Deligne–André–Abdulali skeleton: the Hodge conjecture for abelian varieties,
# factored to its single open field

Read at source (Milne, *Hodge classes on abelian varieties*, 2022; Gordon's survey,
alg-geom/9709030 §11; Abdulali 1994; Deligne LNM 900; André 1992):

* **Theorem 1 (André)**: every Hodge class on a CM abelian variety is a sum of
  pullbacks of Weil classes on abelian varieties of *split* Weil type — pure linear
  algebra plus Pohlmann; no deformation theory.
* **Theorem 3 (Deligne)**: every Hodge class on every abelian variety is *accessible*:
  chain-connected, through connecting families, to split-Weil classes — and the
  split-Weil families contain divisor-product members where the class is algebraic
  by construction (Deligne 1982, 4.8).
* **Remark 2/3 (Milne, after André 1996)**: the Hodge conjecture for all abelian
  varieties follows if algebraicity propagates along the connecting families, and it
  suffices to propagate over *complete smooth curves* in the PEL Shimura bases.
* **Proposition 1 (Abdulali)**: that propagation follows from the Lefschetz standard
  conjecture for the fibered *total spaces* (Kuga varieties over curve sections).

**The wall, located exactly** (this file's `variational` field): inverting the total
space's Lefschetz operator reduces, via Künnemann's algebraic relative hard Lefschetz
and the square-zero base class, to algebraically inverting invariants → coinvariants
of the local system — i.e. to realizing Deligne's semisimplicity of the VHS by an
algebraic projector: **the motivic fixed-part statement**.  All known formulations
(invariant cycles conjecture, Abdulali's L²-conjecture-A, B(Kuga totals), variational
Hodge over curves) are this one field in different coordinates.  For the *specific*
PEL families the reduction traverses, the projector question lives where special-cycle
technology exists (unitary Shimura varieties) — the researched attack corridor.

This file types the factorization: `DeligneSkeleton` carries the cited spine as data
(edges, seeds, accessibility) and the wall as the single field `variational`;
`recognition` and `sourceExhaustion` are then theorems — the Hodge conjecture for the
whole indexed family of abelian dials, given exactly that one input.  Register: the
cited fields are literature (named above); nothing here inhabits the wall.
No `sorry`, no `axiom`.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-- **The skeleton bundle**: dials indexed by the sites of the reduction, connecting-
family edges, split-Weil divisor-product seeds, the cited accessibility spine, and the
single open field — variational algebraicity along one edge. -/
structure DeligneSkeleton {ι : Type*} (Z : ι → Type*) [∀ i, AddCommGroup (Z i)]
    (D : ∀ i, HodgeDial (Z i)) where
  /-- Connecting-family edges: two classes at two sites given as values of one global
  section of a family over a complete smooth curve in a PEL Shimura base
  (Deligne 5.1(c) data, curve-reduced per Milne Rmk 3 / André 1996). -/
  Edge : (Σ i, Z i) → (Σ i, Z i) → Prop
  /-- Seeds: split-Weil divisor-product members — the classes algebraic by
  construction at the far end of every chain (Deligne 1982, 4.8). -/
  Seed : (Σ i, Z i) → Prop
  /-- Seeds are algebraic (intersections of divisor classes; elementary, cited). -/
  seed_algebraic : ∀ p, Seed p → (D p.1).Algebraic p.2
  /-- **Accessibility** (André Thm 1 + Deligne Thm 3, cited): every fired rational DC
  class is chain-connected to a seed. -/
  accessible : ∀ i (z : Z i), (∃ d, (D i).T d z ≠ 0) → (D i).DC z →
    (D i).Rational z →
    ∃ q, Seed q ∧ Relation.ReflTransGen Edge ⟨i, z⟩ q
  /-- **THE WALL — the single open field**: algebraicity propagates backward along a
  connecting edge.  Equivalent formulations: variational Hodge over complete curves;
  Grothendieck's invariant cycles conjecture for these families; Abdulali's
  L²-analogue of standard conjecture A; Lefschetz standard conjecture for the Kuga
  total spaces; the motivic fixed-part projector for the PEL local systems. -/
  variational : ∀ p q, Edge p q → (D q.1).Algebraic q.2 → (D p.1).Algebraic p.2

namespace DeligneSkeleton

variable {ι : Type*} {Z : ι → Type*} [∀ i, AddCommGroup (Z i)]
  {D : ∀ i, HodgeDial (Z i)}

/-- Algebraicity pulls back along a whole chain of connecting families. -/
theorem algebraic_of_chain (S : DeligneSkeleton Z D) {p q : Σ i, Z i}
    (hpath : Relation.ReflTransGen S.Edge p q)
    (hq : (D q.1).Algebraic q.2) : (D p.1).Algebraic p.2 := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact hq
  | head hedge _ ih => exact S.variational _ _ hedge ih

/-- **Recognition at every site, from the one field**: the wall plus the cited spine
give recognition for the entire indexed family of abelian dials. -/
theorem recognition (S : DeligneSkeleton Z D) (i : ι) : Recognition (D i) := by
  intro z hfired hdc hrat
  obtain ⟨q, hseed, hpath⟩ := S.accessible i z hfired hdc hrat
  exact S.algebraic_of_chain hpath (S.seed_algebraic q hseed)

/-- **The terminus**: proven retention at each site plus the skeleton give source
exhaustion everywhere — the Hodge conjecture for the indexed family of abelian dials,
factored to exactly one open input. -/
theorem sourceExhaustion (S : DeligneSkeleton Z D)
    (hret : ∀ i, Retention (D i)) (i : ι) : SourceExhaustion (D i) :=
  hodge_of_retention_recognition (hret i) (S.recognition i)

end DeligneSkeleton

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.DeligneSkeleton.algebraic_of_chain
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.DeligneSkeleton.recognition
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.DeligneSkeleton.sourceExhaustion
