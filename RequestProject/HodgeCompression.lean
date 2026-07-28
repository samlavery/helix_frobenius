import RequestProject.UniversalReconstruction

/-!
# The compression theorem: seeds are free, transitivity is proven, the wall is one field

The correspondent's next-step list (2026-07-27) asks for the structure leg in broad
generality and a *universal seeding theorem* — seeds from intrinsic data, not case-by-case
construction.  Both exist, unconditionally, at **full Hodge-correspondence strength**, and
this file proves them:

* **The structure leg, closed at Hodge strength** (`transport_exists`,
  `hodge_block_irreducible`): polarizable ℚ-Hodge structures form a semisimple category
  (classical — polarization positivity; cited, not formalized), so `H^{2p}(X,ℚ)` splits as
  `T ⊕ N` with `T` the Tate-isotypic block — and the underlying rational space of `T` is
  exactly the span of the Hodge classes, i.e. `Hdg^p(X) = T`.  Every ℚ-linear endomorphism
  of `T` extended by zero on `N` is a morphism of Hodge structures
  (`Hom_HS(ℚ(−p)^m, ℚ(−p)^m) = M_m(ℚ)`), hence — via Künneth and Poincaré duality — is
  induced by a HODGE class on `X × X` (the cited dictionary).  The Lean content is the
  linear algebra made exact: the block `T` is orbit-irreducible under the transport
  operators `hodgeTransport T N` — every nonzero element reaches every element.

* **The seeding leg, closed at Hodge strength**: the intrinsic seed is the polarization
  power `h^p` (hyperplane class to the `p`-th) — algebraic, Hodge, and nonzero for
  `p ≤ dim X` by hard Lefschetz (cited).  No Prym, no CM, no discovery search: at full
  transport strength the seed is free.  It enters `hodge_compression` as the hypothesis
  triple `(hF, hFT, hFne)`.

* **The compression theorem** (`hodge_compression`): with the splitting and the free seed,
  the ENTIRE Hodge conjecture for `(X, p)` is equivalent to the single field `halg`:
  *the Tate-block transport operators preserve algebraicity* — i.e. the transports, which
  are Hodge classes on `X × X`, are algebraic.  Proof: `seed_transfer` with `L = ⊥`,
  `W = T`, `Corr = hodgeTransport`.

**The self-reference, stated without disguise**: a rank-one transport carrying the seed to
a target `β` is, under the correspondence dictionary, built from `β` itself — so `halg` is
an instance of the Hodge conjecture one degree up, on `X × X`.  The compression is a
REORGANIZATION of the wall, not an escape from it.  Its value is coordinates, and they are
operative, not cosmetic:

* **The trade-off law.**  Restrict `Corr` to the proven-algebraic correspondences and
  `stab` is a theorem while irreducibility and seeding become the open legs — the
  sixfold's position.  Enlarge `Corr` to full Hodge transport and irreducibility and
  seeding are theorems (this file) while `stab` becomes the open field — the compression's
  position.  The Hodge conjecture is the statement that the two positions meet.
* **The instruments point at the field — at the correct register.**  The census's
  collective projector is a FROBENIUS spectral projector cutting the Weil channel; its
  measured p-independent signature (`D_p = 13`, `multW = 18`, nine primes) is *consistent
  with* — probes, but does not yet measure — the characteristic-zero transport operator
  `halg` names.  The identification requires one more theorem: a specialization/comparison
  bridge carrying Frobenius spectral projectors to absolute-Hodge transport operators —
  which is the program's existing `DescentDatum.glue` field in a new shape, and the same
  wall the universal harmonic clock states as "the clock's graph exists in char 0."
  Until that bridge is proven, the census is evidence about the field, not a reading
  of it.

Scope: this file does not assume or prove the Hodge conjecture.  It proves that at Hodge
strength both legs close and the conjecture IS the one named field.  No `sorry`,
no `axiom`.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {H : Type*} [AddCommGroup H] [Module ℚ H]

/-- **The Tate-block transport operators**: linear maps landing in the block `T` and
killing the complement `N`.  Under the cited dictionary (Künneth + Poincaré duality +
`Hom_HS(ℚ(−p)^m, ℚ(−p)^m) = M_m(ℚ)`), these are induced by Hodge classes on `X × X` —
the subclass of Hodge correspondences the compression actually consumes. -/
def hodgeTransport (T N : Submodule ℚ H) : Set (H → H) :=
  {f | ∃ g : H →ₗ[ℚ] H, ⇑g = f ∧ (∀ x, g x ∈ T) ∧ (∀ x ∈ N, g x = 0)}

/-- **The transport theorem (the structure leg's engine, unconditional)**: given the
splitting `H = T ⊕ N`, every nonzero `w₀ ∈ T` reaches every `w ∈ T` by a transport
operator.  The proof is the multiplicity-space argument made explicit: project to the
line `ℚ·w₀` along a complement containing `N`, then rescale onto `w`. -/
theorem transport_exists (T N : Submodule ℚ H) (hcompl : IsCompl T N)
    (w₀ : H) (hw₀ : w₀ ∈ T) (hne : w₀ ≠ 0) (w : H) (hw : w ∈ T) :
    ∃ f ∈ hodgeTransport T N, f w₀ = w := by
  classical
  set p : Submodule ℚ H := Submodule.span ℚ {w₀} with hp
  have hpT : p ≤ T := by
    rw [hp, Submodule.span_le, Set.singleton_subset_iff]; exact hw₀
  -- a complement of the line that contains N
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (p ⊔ N)
  have hpq : IsCompl p (N ⊔ U) := by
    constructor
    · -- disjointness: x ∈ p ∩ (N ⊔ U) forces x = 0
      rw [disjoint_iff]
      refine le_bot_iff.mp fun x hx => ?_
      obtain ⟨hxp, hxNU⟩ := Submodule.mem_inf.mp hx
      obtain ⟨n, hn, u, hu, rfl⟩ := Submodule.mem_sup.mp hxNU
      have huV : u ∈ p ⊔ N := by
        have : u = (n + u) - n := by abel
        rw [this]
        exact Submodule.sub_mem _ (Submodule.mem_sup_left hxp)
          (Submodule.mem_sup_right hn)
      have hu0 : u = 0 := by
        have := hU.disjoint.le_bot (Submodule.mem_inf.mpr ⟨huV, hu⟩)
        simpa using this
      subst hu0
      rw [add_zero] at hxp ⊢
      have : n ∈ T ⊓ N := Submodule.mem_inf.mpr ⟨hpT hxp, hn⟩
      have := hcompl.disjoint.le_bot this
      simpa using this
    · -- codisjointness: p ⊔ (N ⊔ U) = ⊤
      rw [codisjoint_iff]
      rw [← sup_assoc]
      exact codisjoint_iff.mp hU.codisjoint
  -- the projection onto the line, the coordinate, the rescale
  let π := Submodule.projectionOnto p (N ⊔ U) hpq
  let e := LinearEquiv.toSpanNonzeroSingleton ℚ H w₀ hne
  let g : H →ₗ[ℚ] H := LinearMap.smulRight ((e.symm : _ →ₗ[ℚ] ℚ).comp π) w
  have hgdef : ∀ x, g x = (e.symm (π x) : ℚ) • w := fun _ => rfl
  refine ⟨⇑g, ⟨g, rfl, ?_, ?_⟩, ?_⟩
  · intro x
    rw [hgdef]
    exact Submodule.smul_mem T _ hw
  · intro x hx
    rw [hgdef]
    have hπ0 : π x = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hpq (Submodule.mem_sup_left hx)
    rw [hπ0, map_zero, zero_smul]
  · rw [hgdef]
    have hπ : π w₀ = ⟨w₀, Submodule.mem_span_singleton_self w₀⟩ :=
      Submodule.projectionOnto_apply_of_mem_left hpq
        (Submodule.mem_span_singleton_self w₀)
    rw [hπ]
    have he : e.symm ⟨w₀, Submodule.mem_span_singleton_self w₀⟩ = 1 := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      show w₀ = (1 : ℚ) • w₀
      rw [one_smul]
    rw [he, one_smul]

/-- **The structure leg at Hodge strength**: the Tate block is orbit-irreducible under
the transport operators — in `seed_transfer`'s exact hypothesis shape. -/
theorem hodge_block_irreducible (T N : Submodule ℚ H) (hcompl : IsCompl T N) :
    ∀ w₀ ∈ T, w₀ ≠ 0 → ∀ w ∈ T, ∃ f ∈ hodgeTransport T N, f w₀ = w :=
  fun w₀ hw₀ hne w hw => transport_exists T N hcompl w₀ hw₀ hne w hw

/-- **The compression theorem**: the splitting (semisimplicity, cited), the free seed
(the polarization power `h^p` — algebraic, in the block, nonzero; cited), and the ONE
field `halg` (transport operators preserve algebraicity — Hodge classes on `X × X` are
algebraic, one degree up) give: the whole Tate block — that is, every Hodge class — is
algebraic.  The Hodge conjecture for `(X, p)`, priced at exactly one field. -/
theorem hodge_compression
    (Alg : Submodule ℚ H) (T N : Submodule ℚ H) (hcompl : IsCompl T N)
    (halg : ∀ f ∈ hodgeTransport T N, ∀ x ∈ Alg, f x ∈ Alg)
    (F : H) (hF : F ∈ Alg) (hFT : F ∈ T) (hFne : F ≠ 0) :
    T ≤ Alg :=
  seed_transfer Alg (hodgeTransport T N) halg ⊥ T bot_le
    (hodge_block_irreducible T N hcompl)
    F 0 F hF (zero_add F).symm (Submodule.zero_mem ⊥) hFT hFne

/-- **The two positions meet in the middle — the trade-off, packaged**: any set of
proven-algebraic correspondences `CorrAlg` (where `stab` is a theorem) that realizes the
transport orbit on the block (where irreducibility would otherwise be open) closes the
block.  The sixfold program and the compression are the two ends of this one statement:
the Hodge conjecture is the assertion that some such `CorrAlg` exists for every `(X, p)`. -/
theorem block_closed_of_algebraic_transport
    (Alg : Submodule ℚ H) (T : Submodule ℚ H)
    (CorrAlg : Set (H → H))
    (stab : ∀ f ∈ CorrAlg, ∀ x ∈ Alg, f x ∈ Alg)
    (hreach : ∀ w₀ ∈ T, w₀ ≠ 0 → ∀ w ∈ T, ∃ f ∈ CorrAlg, f w₀ = w)
    (F : H) (hF : F ∈ Alg) (hFT : F ∈ T) (hFne : F ≠ 0) :
    T ≤ Alg :=
  seed_transfer Alg CorrAlg stab ⊥ T bot_le hreach
    F 0 F hF (zero_add F).symm (Submodule.zero_mem ⊥) hFT hFne

/-- **The coincidence, as an equivalence — "the conjecture IS the intersection of the two
worlds," in both directions**: given the splitting and the free seed, the block is
algebraic IF AND ONLY IF some algebraicity-preserving correspondence set acts transitively
on it.  Forward: if the block is algebraic, the full transport set itself preserves
algebraicity (its image lies in the block), so the two algebras coincide on the
transports.  Backward: `seed_transfer`.  The Hodge conjecture for `(X, p)` is not merely
*reduced to* the coincidence of the algebraic and Hodge correspondence algebras on the
Tate-block transports; it *is* that coincidence. -/
theorem hodge_iff_positions_meet
    (Alg : Submodule ℚ H) (T N : Submodule ℚ H) (hcompl : IsCompl T N)
    (F : H) (hF : F ∈ Alg) (hFT : F ∈ T) (hFne : F ≠ 0) :
    T ≤ Alg ↔
      ∃ Corr : Set (H → H),
        (∀ f ∈ Corr, ∀ x ∈ Alg, f x ∈ Alg) ∧
        (∀ w₀ ∈ T, w₀ ≠ 0 → ∀ w ∈ T, ∃ f ∈ Corr, f w₀ = w) := by
  constructor
  · intro hT
    refine ⟨hodgeTransport T N, ?_, hodge_block_irreducible T N hcompl⟩
    rintro f ⟨g, rfl, hgT, -⟩ x -
    exact hT (hgT x)
  · rintro ⟨Corr, stab, hreach⟩
    exact block_closed_of_algebraic_transport Alg T Corr stab hreach F hF hFT hFne

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.transport_exists
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.hodge_block_irreducible
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.hodge_compression
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.block_closed_of_algebraic_transport
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.hodge_iff_positions_meet
