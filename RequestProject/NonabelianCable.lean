import RequestProject.AbelianTransportLadder

/-!
# The non-abelian cable: separator + mixer ⟹ irreducibility ⟹ Hodge

The correspondent's repair (2026-07-27): the matrix-unit demand was too strong.  You do
not need algebraic matrix units as INPUT — two noncommuting algebraic correspondences
with separator-plus-mixer behavior generate them automatically as OUTPUT.  This file
proves both halves at the standard footprint:

* **The non-abelian repair theorem** (`block_closed_of_irreducible`): if the Tate block
  `T` is an irreducible module under a composition-closed set of algebraic (linear)
  correspondences containing the identity, then the orbit span of the free seed is a
  nonzero invariant subspace, hence all of `T` — and every element of the orbit span is
  algebraic.  Irreducibility ⟹ cyclicity from `h^p` ⟹ Hodge for `(X, p)`.

* **The two-operator criterion** (`hodge_of_nonabelian_connectivity`): a SEPARATOR `A`
  with simple rational spectrum on `T` (entering through its Lagrange spectral projectors
  `e i` — polynomials in `A`, hence algebraic: exactly the house `clockChannelProjector`
  machinery) and a MIXER `B` whose transition graph between the one-dimensional
  eigenchannels is strongly connected.  The proof is DIRECT, not via invariant
  subspaces: the seed has a nonzero component in some channel; each edge `i → j` of the
  graph is a nonzero map between one-dimensional spaces, so path composition
  `e_j B e_{k_r} ⋯ B e_i` transports that component to a nonzero algebraic spanning
  vector of EVERY channel; any `β ∈ T` is then the sum of rational multiples of these
  manufactured per-channel seeds.  Connectivity manufactures the seeds — the
  construction the abelian route could only demand, made explicit.

**Necessity of noncommutativity**: if `B` commutes with the separator it commutes with
its spectral projectors, every off-diagonal block `e_j ∘ B ∘ e_i` (`i ≠ j`) vanishes, and
the graph has no edges: a commuting `B` mixes nothing.  The non-abelian-ness is
load-bearing.

**Register, exact.**  What this closes: the propagation.  What it opens (the new, finite,
operational target — the non-abelian cable): for each `(X, p)`, the EXISTENCE of the
pair — one algebraic separator with simple rational spectrum on the block, one algebraic
mixer with strongly connected transitions.  The census's new job list: (1) recover a
characteristic-zero algebraic separator from the stable Frobenius spectral data — still
gated by the bridge theorem of the previous register (Frobenius spectral projector ⇝
absolute-Hodge/motivated ⇝ algebraic; on abelian specimens the last step is banked via
B(AV)); (2) construct a geometric mixer NOT commuting with the separator; (3) verify
strong connectivity of the off-diagonal blocks — which is CHECKABLE mod `p` from point
counts.  Scope: does not assume or prove the Hodge conjecture; the pair's existence is
consumed, never asserted.  No `sorry`, no `axiom`.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {H : Type*} [AddCommGroup H] [Module ℚ H]

/-- **The non-abelian repair theorem**: irreducibility of the block under a
composition-closed set of algebraic linear correspondences forces the orbit span of the
free seed to be everything — cyclicity from `h^p` — and orbit spans of algebraic seeds
under algebraic operators are algebraic.  No matrix units demanded as input. -/
theorem block_closed_of_irreducible
    (Alg T : Submodule ℚ H)
    (Corr : Set (H →ₗ[ℚ] H))
    (hid : LinearMap.id ∈ Corr)
    (hcomp : ∀ f ∈ Corr, ∀ g ∈ Corr, f ∘ₗ g ∈ Corr)
    (stab : ∀ f ∈ Corr, ∀ x ∈ Alg, f x ∈ Alg)
    (hT : ∀ f ∈ Corr, ∀ x ∈ T, f x ∈ T)
    (hirr : ∀ S : Submodule ℚ H, S ≤ T →
      (∀ f ∈ Corr, ∀ x ∈ S, f x ∈ S) → S ≠ ⊥ → T ≤ S)
    (F : H) (hF : F ∈ Alg) (hFT : F ∈ T) (hFne : F ≠ 0) :
    T ≤ Alg := by
  set orbit : Set H := {y | ∃ f ∈ Corr, y = f F} with horbit
  set O : Submodule ℚ H := Submodule.span ℚ orbit with hO
  have hOT : O ≤ T := by
    rw [hO, Submodule.span_le]
    rintro y ⟨f, hf, rfl⟩
    exact hT f hf F hFT
  have hOA : O ≤ Alg := by
    rw [hO, Submodule.span_le]
    rintro y ⟨f, hf, rfl⟩
    exact stab f hf F hF
  have hOinv : ∀ f ∈ Corr, ∀ x ∈ O, f x ∈ O := by
    intro f hf x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨g, hg, rfl⟩ := hy
        exact Submodule.subset_span ⟨f ∘ₗ g, hcomp f hf g hg, rfl⟩
    | zero => simpa using O.zero_mem
    | add a b _ _ ha hb => simpa [map_add] using O.add_mem ha hb
    | smul c a _ ha => simpa [map_smul] using O.smul_mem c ha
  have hFO : F ∈ O := Submodule.subset_span ⟨LinearMap.id, hid, rfl⟩
  have hOne : O ≠ ⊥ := by
    intro h
    exact hFne (by simpa [h] using hFO)
  exact fun x hx => hOA (hirr O hOT hOinv hOne hx)

/-- **The two-operator criterion — separator + mixer ⟹ Hodge, constructively.**
The separator enters through its spectral projectors `e i` (Lagrange polynomials in an
algebraic correspondence with simple rational spectrum — algebraic, the house clock
machinery) with their channel decomposition `decomp`/`echan`/`dim1`; the mixer `B` enters
through the edge property `hedge` and strong connectivity `conn` of its transition graph.
The proof manufactures a nonzero algebraic spanning vector for EVERY channel by
transporting the seed's nonzero component along graph paths, then reads any `β ∈ T` off
channel by channel.  Connectivity manufactures the per-channel seeds. -/
theorem hodge_of_nonabelian_connectivity
    (Alg T : Submodule ℚ H) {m : ℕ}
    (Tc : Fin m → Submodule ℚ H) (chanle : ∀ i, Tc i ≤ T)
    (e : Fin m → H → H) (B : H → H) (edge : Fin m → Fin m → Prop)
    (ealg : ∀ i, ∀ x ∈ Alg, e i x ∈ Alg)
    (Balg : ∀ x ∈ Alg, B x ∈ Alg)
    (BT : ∀ x ∈ T, B x ∈ T)
    (decomp : ∀ x ∈ T, x = ∑ i, e i x)
    (echan : ∀ i, ∀ x ∈ T, e i x ∈ Tc i)
    (dim1 : ∀ i, ∀ u ∈ Tc i, u ≠ 0 → ∀ v ∈ Tc i, ∃ c : ℚ, v = c • u)
    (hedge : ∀ i j, edge i j → ∀ u ∈ Tc i, u ≠ 0 → e j (B u) ≠ 0)
    (conn : ∀ i j, Relation.ReflTransGen edge i j)
    (F : H) (hF : F ∈ Alg) (hFT : F ∈ T) (hFne : F ≠ 0) :
    T ≤ Alg := by
  -- the seed has a nonzero component in some channel
  have hex : ∃ i₀, e i₀ F ≠ 0 := by
    by_contra h
    push_neg at h
    exact hFne (by rw [decomp F hFT]; exact Finset.sum_eq_zero fun i _ => h i)
  obtain ⟨i₀, hi₀⟩ := hex
  -- path propagation: every channel reachable from i₀ acquires a nonzero algebraic
  -- spanning vector — the manufactured per-channel seeds
  have prop : ∀ j, Relation.ReflTransGen edge i₀ j →
      ∃ w, w ∈ Tc j ∧ w ∈ Alg ∧ w ≠ 0 := by
    intro j hj
    induction hj with
    | refl => exact ⟨e i₀ F, echan i₀ F hFT, ealg i₀ F hF, hi₀⟩
    | @tail b c _ hbc ih =>
        obtain ⟨w, hwT, hwA, hwne⟩ := ih
        exact ⟨e c (B w), echan c (B w) (BT w (chanle b hwT)),
          ealg c (B w) (Balg w hwA), hedge b c hbc w hwT hwne⟩
  -- read any class off channel by channel against the manufactured seeds
  intro β hβ
  rw [decomp β hβ]
  refine Submodule.sum_mem Alg fun j _ => ?_
  obtain ⟨w, hwT, hwA, hwne⟩ := prop j (conn i₀ j)
  obtain ⟨c, hc⟩ := dim1 j w hwT hwne (e j β) (echan j β hβ)
  rw [hc]
  exact Submodule.smul_mem Alg c hwA

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.block_closed_of_irreducible
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.hodge_of_nonabelian_connectivity
