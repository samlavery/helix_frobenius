import RequestProject.RecognitionReconstruction

/-!
# Universal reconstruction: the seed-transfer mechanism, extracted Prym-free

The correspondent's ticket (2026-07-27): *"extract the invariant construction that does
not depend on Pryms, split discriminants, CM, or a pre-existing theorem of Schoen or
Markman."*  This file is that extraction.  The sixfold's K-sweep (`KSweepCompletion`)
succeeds for exactly one reason, and it is not the Prym scaffolding: **algebraicity
propagates along orbits of algebraicity-preserving operators**.  Stated at that level the
mechanism needs no field, no dimension bound, no abelian hypothesis — only:

* `seed_transfer` — for ANY set `Corr` of algebraicity-preserving operators (the algebraic
  correspondences of `X`, whatever they are), any constituent `W` of the Hodge space that
  is *orbit-irreducible* under `Corr` (every nonzero element reaches every element) becomes
  wholly algebraic as soon as ONE algebraic class `F = ℓ + w₀` has nonzero `W`-component.
  Subtract the Lefschetz part, transport along the orbit.  Nothing else.
* `exhaustion_of_seeds` — iterate over finitely many constituents: `L ⊔ ⨆ Wᵢ ≤ Alg` from
  one seed per constituent.  The universal quantifier over classes collapses to a finite
  list of seeds — the honest form of "reconstruction".
* `kline_seed_transfer` — the sixfold's K-sweep recovered as the one-line instance: a
  `K`-line is orbit-irreducible under the `K`-scalar operators.  The Prym, the CM field,
  the discriminant were scaffolding for ONE specimen's certificate, not the mechanism.
* `seed_without_irreducibility_fails` — the necessity of the wall, machine-checked: a model
  satisfying every hypothesis EXCEPT orbit-irreducibility in which the seeded constituent
  is NOT algebraic.  Irreducibility is load-bearing, not decorative.
* `sourced_of_sweep` / `sourceExhaustion_of_sweep` — the socket wiring: a `SweptRealization`
  fills the program's single field `sourced_of_pairing`, and composes with proven retention
  into source exhaustion.

**The price of the universal quantifier, exact.**  What the mechanism consumes, per
constituent of `Hdg^p(X)`:
1. the STRUCTURE leg — `Hdg^p(X) = L + Σ Wᵢ` with `L` in the divisor algebra and each `Wᵢ`
   orbit-irreducible under the actual correspondences of `X`;
2. the SEEDING leg — one algebraic class with nonzero `Wᵢ`-component (fired, measurable).

Where both legs are theorems today is the low-rung ledger of `LowDimChainDischarge`
(`p = 1`; products of elliptic curves / abelian surfaces; abelian threefolds; abelian
fourfolds incl. Weil — Markman 2025; fivefolds; split Weil sixfolds); the first open
constituent is the non-split Weil sixfold.  Scope: this file does **not** assume or prove
the Hodge conjecture; it prices it — and the Lean enforces the price.  No `sorry`,
no `axiom`.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

section Mechanism

variable {H : Type*} [AddCommGroup H] [Module ℚ H]

/-- **The seed-transfer theorem (the invariant mechanism, Prym-free).**  `Corr` is any set
of algebraicity-preserving operators; `W` is orbit-irreducible under `Corr`; one algebraic
class `F = ℓ + w₀` has nonzero `W`-component `w₀`.  Then `W` is wholly algebraic: subtract
the Lefschetz part, transport along the orbit. -/
theorem seed_transfer
    (Alg : Submodule ℚ H) (Corr : Set (H → H))
    (stab : ∀ T ∈ Corr, ∀ x ∈ Alg, T x ∈ Alg)
    (L W : Submodule ℚ H) (hL : L ≤ Alg)
    (hirr : ∀ w₀ ∈ W, w₀ ≠ 0 → ∀ w ∈ W, ∃ T ∈ Corr, T w₀ = w)
    (F ℓ w₀ : H) (hF : F ∈ Alg) (hsplit : F = ℓ + w₀)
    (hℓ : ℓ ∈ L) (hw₀ : w₀ ∈ W) (hne : w₀ ≠ 0) : W ≤ Alg := by
  -- the pure constituent component, by subtraction of the Lefschetz part
  have hw₀alg : w₀ ∈ Alg := by
    have h : w₀ = F - ℓ := by rw [hsplit, add_sub_cancel_left]
    rw [h]
    exact Submodule.sub_mem Alg hF (hL hℓ)
  -- the orbit transport: every element of W is reached from w₀ by a correspondence
  intro w hw
  obtain ⟨T, hT, hTw⟩ := hirr w₀ hw₀ hne w hw
  rw [← hTw]
  exact stab T hT w₀ hw₀alg

/-- **Exhaustion from finitely many seeds**: with `L` algebraic and each constituent `Wᵢ`
orbit-irreducible and seeded (or zero), the whole decomposed space is algebraic.  The
universal quantifier over classes collapses to one seed per constituent. -/
theorem exhaustion_of_seeds
    (Alg : Submodule ℚ H) (Corr : Set (H → H))
    (stab : ∀ T ∈ Corr, ∀ x ∈ Alg, T x ∈ Alg)
    (L : Submodule ℚ H) (hL : L ≤ Alg)
    {k : ℕ} (W : Fin k → Submodule ℚ H)
    (hirr : ∀ i, ∀ w₀ ∈ W i, w₀ ≠ 0 → ∀ w ∈ W i, ∃ T ∈ Corr, T w₀ = w)
    (seeds : ∀ i, W i = ⊥ ∨
      ∃ F ℓ w₀, F ∈ Alg ∧ F = ℓ + w₀ ∧ ℓ ∈ L ∧ w₀ ∈ W i ∧ w₀ ≠ 0) :
    L ⊔ (⨆ i, W i) ≤ Alg := by
  refine sup_le hL (iSup_le fun i => ?_)
  rcases seeds i with hbot | ⟨F, ℓ, w₀, hF, hsplit, hℓ, hw₀, hne⟩
  · rw [hbot]; exact bot_le
  · exact seed_transfer Alg Corr stab L (W i) hL (hirr i) F ℓ w₀ hF hsplit hℓ hw₀ hne

/-- **The sixfold's K-sweep, recovered as an instance**: a `K`-line is orbit-irreducible
under the `K`-scalar operators, so `KSweepCompletion.completion_implication` is the
`Corr = {(a • ·) | a : K}` case of `seed_transfer`.  The Prym, the CM field, the split
discriminant were one specimen's certificate, not the mechanism. -/
theorem kline_seed_transfer
    {K : Type*} [Field K] [Algebra ℚ K] [Module K H] [IsScalarTower ℚ K H]
    (Alg : Submodule ℚ H)
    (algSMul : ∀ (a : K) (x : H), x ∈ Alg → a • x ∈ Alg)
    (L W : Submodule ℚ H) (hL : L ≤ Alg)
    (hdim : ∀ w₀ w : H, w₀ ∈ W → w₀ ≠ 0 → w ∈ W → ∃ a : K, w = a • w₀)
    (F ℓ w₀ : H) (hF : F ∈ Alg) (hsplit : F = ℓ + w₀)
    (hℓ : ℓ ∈ L) (hw₀ : w₀ ∈ W) (hne : w₀ ≠ 0) : W ≤ Alg :=
  seed_transfer Alg {f | ∃ a : K, f = fun x => a • x}
    (by rintro T ⟨a, rfl⟩ x hx; exact algSMul a x hx)
    L W hL
    (fun v hv hvne w hw => by
      obtain ⟨a, ha⟩ := hdim v w hv hvne hw
      exact ⟨fun x => a • x, ⟨a, rfl⟩, ha.symm⟩)
    F ℓ w₀ hF hsplit hℓ hw₀ hne

/-- **The wall is load-bearing — necessity of orbit-irreducibility, machine-checked**: a
model satisfying every hypothesis of `seed_transfer` EXCEPT irreducibility (operators:
the identity; a two-dimensional constituent; a fired seed) in which the constituent is NOT
algebraic.  Without orbit-irreducibility the seed certifies only itself: the reduction's
entire content lives in the structure leg, and the register says so. -/
theorem seed_without_irreducibility_fails :
    ∃ (Alg L W : Submodule ℚ (ℚ × ℚ)) (Corr : Set ((ℚ × ℚ) → (ℚ × ℚ)))
      (F ℓ w₀ : ℚ × ℚ),
      (∀ T ∈ Corr, ∀ x ∈ Alg, T x ∈ Alg) ∧ L ≤ Alg ∧ F ∈ Alg ∧ F = ℓ + w₀ ∧
      ℓ ∈ L ∧ w₀ ∈ W ∧ w₀ ≠ 0 ∧ ¬ W ≤ Alg := by
  refine ⟨Submodule.span ℚ {((1 : ℚ), (0 : ℚ))}, ⊥, ⊤, {id}, (1, 0), 0, (1, 0),
    ?_, bot_le, Submodule.mem_span_singleton_self _, (zero_add _).symm,
    Submodule.zero_mem _, Submodule.mem_top, ?_, ?_⟩
  · rintro T hT x hx
    rw [Set.mem_singleton_iff] at hT
    subst hT
    simpa using hx
  · intro h
    have h1 : (1 : ℚ) = 0 := by simpa using congrArg Prod.fst h
    exact one_ne_zero h1
  · intro h
    have := h (Submodule.mem_top (x := ((0 : ℚ), (1 : ℚ))))
    rw [Submodule.mem_span_singleton] at this
    obtain ⟨a, ha⟩ := this
    have : (a : ℚ) • ((1 : ℚ), (0 : ℚ)) = ((0 : ℚ), (1 : ℚ)) := ha
    have h2 := congrArg Prod.snd this
    simp at h2

end Mechanism

/-! ## The socket: universal reconstruction fills `sourced_of_pairing`

A `SweptRealization` carries the two open legs as named fields — `irreducible` (the
structure leg: the constituents of the actual `Hdg^p(X)` under the actual correspondences)
and `seeded` (the discovery leg: one fired algebraic class per constituent) — together
with the realization of the dial into the decomposed space.  Given those legs, the
program's single remaining field is filled by the mechanism, and retention completes the
terminus.  The fields are consumed, never asserted. -/

/-- The sweep realization of a dial: the decomposed Hodge space, the correspondence set,
the two open legs (structure, seeding) as fields, and the dial's realization into it. -/
structure SweptRealization {Z : Type*} [Zero Z] (D : HodgeDial Z)
    (G : GeneratingPairingData D) (H : Type*) [AddCommGroup H] [Module ℚ H] where
  /-- The algebraic classes. -/
  Alg : Submodule ℚ H
  /-- The algebraic correspondences, as operators. -/
  Corr : Set (H → H)
  /-- Correspondences preserve algebraicity (composition of cycles — cited at use). -/
  stab : ∀ T ∈ Corr, ∀ x ∈ Alg, T x ∈ Alg
  /-- The Lefschetz-type part. -/
  L : Submodule ℚ H
  /-- The number of non-Lefschetz constituents. -/
  rank : ℕ
  /-- The constituents. -/
  W : Fin rank → Submodule ℚ H
  /-- `L` is algebraic (the divisor algebra — Lefschetz (1,1) and products). -/
  lefschetz_algebraic : L ≤ Alg
  /-- **The structure leg (open in general; theorem on the low rungs)**: each constituent
  is orbit-irreducible under the correspondences. -/
  irreducible : ∀ i, ∀ w₀ ∈ W i, w₀ ≠ 0 → ∀ w ∈ W i, ∃ T ∈ Corr, T w₀ = w
  /-- **The seeding leg (the discovery node, per constituent)**: one algebraic class with
  nonzero constituent component — or the constituent is zero. -/
  seeded : ∀ i, W i = ⊥ ∨
    ∃ F ℓ w₀, F ∈ Alg ∧ F = ℓ + w₀ ∧ ℓ ∈ L ∧ w₀ ∈ W i ∧ w₀ ≠ 0
  /-- The dial's classes realize into the space. -/
  realize : Z → H
  /-- Fired rational DC classes land in the decomposed Hodge space. -/
  lands : ∀ z : Z, G.pairing z ≠ 0 → D.DC z → D.Rational z →
    realize z ∈ L ⊔ ⨆ i, W i
  /-- Algebraicity descends along the realization. -/
  descends : ∀ z : Z, realize z ∈ Alg → D.Algebraic z

/-- **Universal reconstruction fills the program's last field**: given the two legs, every
fired rational DC class is algebraic — `sourced_of_pairing`, from the mechanism. -/
theorem sourced_of_sweep {Z : Type*} [Zero Z] {D : HodgeDial Z}
    {G : GeneratingPairingData D} {H : Type*} [AddCommGroup H] [Module ℚ H]
    (R : SweptRealization D G H) :
    ∀ z : Z, G.pairing z ≠ 0 → D.DC z → D.Rational z → D.Algebraic z :=
  fun z hp hdc hrat =>
    R.descends z
      (exhaustion_of_seeds R.Alg R.Corr R.stab R.L R.lefschetz_algebraic R.W
        R.irreducible R.seeded (R.lands z hp hdc hrat))

/-- A sweep realization completes the generating pairing. -/
def GeneratingPairingData.completeSwept {Z : Type*} [Zero Z] {D : HodgeDial Z}
    (G : GeneratingPairingData D) {H : Type*} [AddCommGroup H] [Module ℚ H]
    (R : SweptRealization D G H) : GeneratingPairingData D :=
  { G with sourced_of_pairing := sourced_of_sweep R }

/-- **The terminus through the sweep**: proven retention plus the two legs give source
exhaustion — the Hodge conjecture in the carrier frame, priced at one irreducibility
certificate and one seed per constituent. -/
theorem sourceExhaustion_of_sweep {Z : Type*} [Zero Z] {D : HodgeDial Z}
    (hret : Retention D) (G : GeneratingPairingData D)
    {H : Type*} [AddCommGroup H] [Module ℚ H] (R : SweptRealization D G H) :
    SourceExhaustion D :=
  sourceExhaustion_of_generating_pairing hret (G.completeSwept R)

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.seed_transfer
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.exhaustion_of_seeds
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.kline_seed_transfer
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.seed_without_irreducibility_fails
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.sourced_of_sweep
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.sourceExhaustion_of_sweep
