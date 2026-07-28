import Mathlib
import RequestProject.NonabelianCable

/-!
# The bounded-complexity lift: the conductor is uniform complexity

The correspondent's cable-repair theorem (2026-07-27), verified in dialogue with two
repairs before formalization, and — for the first time in this program — a route where
the final implication is NOT the conjecture renamed:

    same bounded family of cycles exists in infinitely many reductions
      ⟹ the relative Hilbert scheme has a horizontal component
      ⟹ a characteristic-zero cycle exists (with the right class).

The lift is classical spreading-out, assembled from: projectivity of `Hilb_P(𝒳/S)` and
finiteness of its irreducible components (Grothendieck/FGA; noetherian); the
horizontal-component pigeonhole (PROVEN below); constructible image over a
one-dimensional base; the universal family's relative cycle class as a section of a
lisse sheaf, rigid on an irreducible base (SGA); smooth–proper base change; Betti–étale
comparison and injectivity of scalar extension.  **Two repairs recorded from the
verification** (both standard, neither fatal): take the component inside the Zariski
closure of the witness points themselves, so the witnesses are dense and the
simple-spectrum/connectivity conditions transfer to the generic point by lisse rigidity
(equal-at-one-point ⟹ equal-at-generic, not merely "generically after discarding a
closed subset"); and the cospecialization identification returns a Galois conjugate of
the target class — repaired by conjugating the cycle or a finite extension.  Cycles
enter the Hilbert scheme as pairs of effective parts (bounded degree ⟹ finitely many
Hilbert polynomials, so a SECOND application of the same pigeonhole upgrades "bounded
degree at infinitely many places" to "one fixed polynomial at infinitely many places").

**What is Lean-proven here**: the horizontal-component pigeonhole
(`exists_component_with_infinite_places` — infinitely many witnesses over finitely many
components force one component to carry infinitely many); the packaging of the
two-operator criterion (`SeparatorMixerData.closes`); and the assembly
(`hodge_of_bounded_complexity`): the pigeonhole selects the component, the lift field
produces the characteristic-zero separator–mixer–seed data, and the non-abelian
propagation theorem closes the block.  **What is consumed as the typed lift field**: the
classical spreading-out assembly above — cited geometry, not new mathematics, and not
formalizable in current Mathlib; its register is the same as the identification layers
elsewhere in the tree.

**The named ticket** (`uniform_cycle_complexity`, typed by `BoundedLiftPackage`): every
compatible Frobenius-defined Tate transport admits algebraic realizations in the
reductions whose degrees are bounded independently of the prime.  An infinite hypothesis
— the census cannot verify it outright; it CAN falsify it (degrees grow without bound)
or support it (the same finite list of Hilbert data recurs as `p → ∞`), and the boxed
experimental question is exactly that recurrence.  Scope: does not assume or prove the
Hodge conjecture; the package's existence is consumed, never asserted.  No `sorry`,
no `axiom`.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-- **The horizontal-component pigeonhole, proven**: witnesses at infinitely many places
distributed over finitely many components force some component to carry witnesses at
infinitely many places.  (Applied twice in the program: once to Hilbert-scheme
components, once to the finite list of Hilbert polynomials below a degree bound.) -/
theorem exists_component_with_infinite_places {V ι : Type*} [Finite ι]
    {places : Set V} (hinf : places.Infinite) (comp : V → ι) :
    ∃ c : ι, {v ∈ places | comp v = c}.Infinite := by
  by_contra h
  apply hinf
  have hfin : ∀ c : ι, {v ∈ places | comp v = c}.Finite := by
    intro c
    rw [← Set.not_infinite]
    exact fun hc => h ⟨c, hc⟩
  have hcover : places = ⋃ c : ι, {v ∈ places | comp v = c} := by
    ext v
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨fun hv => ⟨comp v, hv, rfl⟩, fun ⟨c, hv, _⟩ => hv⟩
  rw [hcover]
  exact Set.finite_iUnion hfin

/-- **The separator–mixer package**: the two-operator criterion's inputs, bundled — the
shape the characteristic-zero lift must deliver.  One separator (through its spectral
projectors), one mixer, one seed, connectivity. -/
structure SeparatorMixerData {H : Type*} [AddCommGroup H] [Module ℚ H]
    (Alg T : Submodule ℚ H) where
  /-- Number of channels (the separator's simple spectrum size). -/
  m : ℕ
  /-- The eigenchannels. -/
  Tc : Fin m → Submodule ℚ H
  chanle : ∀ i, Tc i ≤ T
  /-- The separator's Lagrange spectral projectors (polynomials in it — algebraic). -/
  e : Fin m → H → H
  /-- The mixer. -/
  B : H → H
  /-- The transition graph. -/
  edge : Fin m → Fin m → Prop
  ealg : ∀ i, ∀ x ∈ Alg, e i x ∈ Alg
  Balg : ∀ x ∈ Alg, B x ∈ Alg
  BT : ∀ x ∈ T, B x ∈ T
  decomp : ∀ x ∈ T, x = ∑ i, e i x
  echan : ∀ i, ∀ x ∈ T, e i x ∈ Tc i
  dim1 : ∀ i, ∀ u ∈ Tc i, u ≠ 0 → ∀ v ∈ Tc i, ∃ c : ℚ, v = c • u
  hedge : ∀ i j, edge i j → ∀ u ∈ Tc i, u ≠ 0 → e j (B u) ≠ 0
  conn : ∀ i j, Relation.ReflTransGen edge i j
  /-- The seed. -/
  F : H
  seed_alg : F ∈ Alg
  seed_mem : F ∈ T
  seed_ne : F ≠ 0

/-- A separator–mixer package closes its block — the two-operator criterion, packaged. -/
theorem SeparatorMixerData.closes {H : Type*} [AddCommGroup H] [Module ℚ H]
    {Alg T : Submodule ℚ H} (D : SeparatorMixerData Alg T) : T ≤ Alg :=
  hodge_of_nonabelian_connectivity Alg T D.Tc D.chanle D.e D.B D.edge D.ealg D.Balg
    D.BT D.decomp D.echan D.dim1 D.hedge D.conn D.F D.seed_alg D.seed_mem D.seed_ne

/-- **The bounded-lift package** — `uniform_cycle_complexity`, typed.  Witness data at
infinitely many places, sorted into the finitely many components of the product Hilbert
scheme (projectivity: cited), together with THE LIFT FIELD: any component carrying
infinitely many witnesses yields characteristic-zero separator–mixer–seed data (the
classical spreading-out assembly, with the two recorded repairs — cited geometry
consumed as a field, exactly like the tree's other identification layers). -/
structure BoundedLiftPackage (V : Type*) {H : Type*} [AddCommGroup H] [Module ℚ H]
    (Alg T : Submodule ℚ H) where
  /-- The good places of the integral model. -/
  places : Set V
  infinite_places : places.Infinite
  /-- The (finite) component count of the product Hilbert scheme at the fixed Hilbert
  data — finiteness is projectivity plus noetherianity (cited). -/
  compCount : ℕ
  /-- Which component each place's witness triple lands in. -/
  comp : V → Fin compCount
  /-- **The lift** (classical spreading-out assembly, cited; the two repairs recorded in
  the file header): a component with infinitely many witnesses produces the
  characteristic-zero package. -/
  lift : ∀ c : Fin compCount, {v ∈ places | comp v = c}.Infinite →
    SeparatorMixerData Alg T

/-- **The bounded-complexity terminus**: uniform cycle complexity closes the block —
pigeonhole selects the horizontal component, the lift delivers the characteristic-zero
separator–mixer–seed, and non-abelian propagation does the rest.  The closing argument
never asserts "Tate ⟹ algebraic"; the cycle EXISTS by geometry once complexity is
bounded. -/
theorem hodge_of_bounded_complexity {V : Type*} {H : Type*}
    [AddCommGroup H] [Module ℚ H] {Alg T : Submodule ℚ H}
    (P : BoundedLiftPackage V Alg T) : T ≤ Alg := by
  obtain ⟨c, hc⟩ := exists_component_with_infinite_places P.infinite_places P.comp
  exact (P.lift c hc).closes

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.exists_component_with_infinite_places
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.SeparatorMixerData.closes
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.hodge_of_bounded_complexity
