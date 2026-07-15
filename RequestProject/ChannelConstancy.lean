import Mathlib

/-!
# Channel constancy = the annihilator lattice of the equidistribution subgroup

The constancy-mechanism brick for Mystery #3.  The measured signature "channel
constancy = algebraicity" (the degenerate control's balanced lanes are exact DC with
zero variance) is modelled here as a theorem about characters of a finite abelian group:

  **a lane observable has ZERO VARIANCE under the uniform measure on a subgroup `H`
  iff its frequency lies in the annihilator of `H`.**

The picture: the Frobenius angles live (in this finite model) in a finite abelian group
`G` — think `G = (Fin g) → ZMod N`, the finite torus `𝕋^g`.  The lane characters are the
additive characters `AddChar G ℂ`; the "equidistribution subgroup" `H ⊆ G` (the diagonal
for a degenerate/isogenous motive, the whole group for a generic one) carries the uniform
(Haar) measure; the **variance** of a character is `E[‖ψ‖²] − ‖E[ψ]‖²`.

* `varChar_eq_ite` — **the variance value**: `varChar H ψ = if IsFrozen H ψ then 0 else 1`.
  The exact single-lane Parseval law: a lane contributes `1` to the variance unless it is
  frozen (its frequency annihilates `H`), in which case it contributes `0`.
* `varChar_eq_zero_iff` — **THE THEOREM**: `varChar H ψ = 0 ↔ IsFrozen H ψ`
  (zero variance ⟺ Fourier support in the annihilator of `H`).  The freeze is *measure-
  free*: it is character-theoretic orthogonality, not a property of any particular density.
* `varChar_top_eq_zero_iff` — **full group ⇒ frozen iff DC**: on `H = ⊤` the only frozen
  lane is the trivial character (`ψ = 0`).  The generic motive freezes nothing but DC.
* `algFrozen_diag_iff` — **diagonal subgroup ⇒ frozen iff balanced**: with `G = Fin g →
  ZMod N` the diagonal `Δ`'s annihilator is exactly the balanced frequencies `∑ᵢ εᵢ = 0`
  — the same balanced-lane condition as `EvenWeightDC.dcLane_nonempty_iff_even`.
* `varChar_laneChar_diag_iff` — the two combined through the standard faithful character:
  `varChar Δ (laneChar ε) = 0 ↔ ∑ᵢ εᵢ = 0`.  The degenerate control's zero-variance lanes
  are *exactly* the balanced ones.
* `diag_double_annihilator` — **the inversion**: the annihilator of the frozen (balanced)
  set recovers `Δ` (double annihilator, finite abelian).  From the freeze pattern alone one
  reads back the equidistribution subgroup.
* `algFrozen_readingScale` — **the exact freeze is reading-scale invariant**: scaling the
  reading frequency `ε ↦ c·ε` preserves annihilation.  The genuine lock is a property of the
  support `H`; only the quantitative channel occupancy (the count) is reading-grid sensitive
  — "check the count, not the freeze".
* `isFrozen_laneChar_iff` — the bridge: analytic freeze of `laneChar ε` on `H` ⟺ the
  algebraic annihilation `∀ h ∈ H, ⟨ε, h⟩ = 0`, via the primitive `ZMod.stdAddChar`.

**Scope.**  This is the finite-group model of the freeze mechanism: character orthogonality,
the variance decomposition, the freeze-⟺-annihilator equivalence, and the double-annihilator
inversion, with the house cases (full group ⇒ DC, diagonal ⇒ balanced) instantiated.  It
carries no arithmetic input (Sato–Tate is what makes the arithmetic subgroup `H` the isogeny-
diagonal — not modelled here) and makes no Hodge/Tate claim: the identification of frozen
lanes with algebraic cycle classes is the Hodge/Tate conjectures' territory (a theorem on
products of elliptic curves, open beyond) and is neither assumed nor proven.  Nothing here
assumes or proves RH/GRH.  No `axiom`, no `sorry`.
-/

open scoped BigOperators
open AddChar

namespace ChannelConstancy

/-! ## Part A — the analytic core (an abstract finite abelian group) -/

section Analytic

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The lane `ψ` is **frozen** on `H`: trivial on the subgroup, i.e. its frequency lies in
the annihilator `H^⊥`.  Freeze is the character-theoretic form of "constant on `H`". -/
def IsFrozen (H : AddSubgroup G) (ψ : AddChar G ℂ) : Prop := ∀ h ∈ H, ψ h = 1

/-- Restriction of a global character to a subgroup, as a character of the subgroup. -/
noncomputable def restrictChar (H : AddSubgroup G) (ψ : AddChar G ℂ) : AddChar H ℂ :=
  AddChar.toAddMonoidHomEquiv.symm ((AddChar.toAddMonoidHomEquiv ψ).comp H.subtype)

omit [Fintype G] in
lemma restrictChar_eq_zero_iff (H : AddSubgroup G) (ψ : AddChar G ℂ) :
    restrictChar H ψ = 0 ↔ IsFrozen H ψ := by
  rw [AddChar.eq_zero_iff]
  exact ⟨fun h x hx => by have := h ⟨x, hx⟩; simpa [restrictChar] using this,
         fun h x => by have := h x x.2; simpa [restrictChar] using this⟩

/-- Uniform (Haar) expectation of a `ℂ`-valued observable over the subgroup `H`. -/
noncomputable def meanC (H : AddSubgroup G) [Fintype H] (f : G → ℂ) : ℂ :=
  (∑ h : H, f h) / (Fintype.card H : ℂ)

/-- Uniform (Haar) expectation of an `ℝ`-valued observable over the subgroup `H`. -/
noncomputable def meanR (H : AddSubgroup G) [Fintype H] (f : G → ℝ) : ℝ :=
  (∑ h : H, f h) / (Fintype.card H : ℝ)

/-- **Variance of a lane** under the uniform measure on `H`: `E[‖ψ‖²] − ‖E[ψ]‖²`. -/
noncomputable def varChar (H : AddSubgroup G) [Fintype H] (ψ : AddChar G ℂ) : ℝ :=
  meanR H (fun x => ‖ψ x‖ ^ 2) - ‖meanC H ψ‖ ^ 2

omit [Fintype G] in
lemma cardH_pos (H : AddSubgroup G) [Fintype H] : 0 < Fintype.card H :=
  have : Nonempty H := ⟨⟨0, H.zero_mem⟩⟩
  Fintype.card_pos

omit [Fintype G] in
/-- **Orthogonality over a subgroup**: `∑_{h∈H} ψ h = |H|` if `ψ` is frozen on `H`, else
`0`.  The finite-group orthogonality relation, obtained from `AddChar.sum_eq_ite` on the
restricted character.  (Elementarily this is the geometric-sum / reindexing argument:
if some `h₀∈H` has `ψ h₀ ≠ 1` then `ψ h₀ · S = S`, forcing `S = 0`.) -/
lemma char_sum_over_subgroup (H : AddSubgroup G) (ψ : AddChar G ℂ) [Fintype H]
    [Decidable (IsFrozen H ψ)] :
    (∑ h : H, ψ (h : G)) = if IsFrozen H ψ then (Fintype.card H : ℂ) else 0 := by
  have hcong : (∑ h : H, ψ (h : G)) = ∑ h : H, restrictChar H ψ h :=
    Finset.sum_congr rfl (fun h _ => by simp [restrictChar])
  rw [hcong]; classical
  rw [AddChar.sum_eq_ite]
  simp only [restrictChar_eq_zero_iff]

/-- **The variance value** (the exact single-lane Parseval law): a lane's variance is `0`
if it is frozen and `1` otherwise.  A frozen lane sits in the annihilator and contributes
nothing; every other lane contributes its full unit weight. -/
theorem varChar_eq_ite (H : AddSubgroup G) (ψ : AddChar G ℂ) [Fintype H]
    [Decidable (IsFrozen H ψ)] :
    varChar H ψ = if IsFrozen H ψ then 0 else 1 := by
  have hEsq : meanR H (fun x => ‖ψ x‖ ^ 2) = 1 := by
    have hnorm : ∀ x : G, ‖ψ x‖ ^ 2 = 1 := fun x => by rw [AddChar.norm_apply]; ring
    unfold meanR
    simp only [hnorm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [div_self]; exact_mod_cast (cardH_pos H).ne'
  have hmean : meanC H ψ = if IsFrozen H ψ then 1 else 0 := by
    unfold meanC; rw [char_sum_over_subgroup H ψ]
    by_cases hf : IsFrozen H ψ
    · rw [if_pos hf, if_pos hf, div_self (by exact_mod_cast (cardH_pos H).ne')]
    · rw [if_neg hf, if_neg hf, zero_div]
  unfold varChar; rw [hEsq, hmean]
  by_cases hf : IsFrozen H ψ <;> simp [hf]

/-- **THE THEOREM**: zero variance under the uniform measure on `H` ⟺ the lane's frequency
lies in the annihilator of `H` (Fourier support in `H^⊥`).  Channel constancy *is* the
annihilator condition. -/
theorem varChar_eq_zero_iff (H : AddSubgroup G) (ψ : AddChar G ℂ) [Fintype H] :
    varChar H ψ = 0 ↔ IsFrozen H ψ := by
  classical
  rw [varChar_eq_ite]
  by_cases hf : IsFrozen H ψ <;> simp [hf]

omit [Fintype G] in
/-- On the **full group** the only frozen lane is the trivial character `0` (the DC lane):
`IsFrozen ⊤ ψ ↔ ψ = 0`. -/
theorem isFrozen_top_iff (ψ : AddChar G ℂ) :
    IsFrozen (⊤ : AddSubgroup G) ψ ↔ ψ = 0 := by
  rw [AddChar.eq_zero_iff]
  exact ⟨fun h x => h x (AddSubgroup.mem_top x), fun h x _ => h x⟩

/-- **Full group ⇒ frozen iff DC**: over the whole torus the only zero-variance lane is the
DC/trivial one.  The generic (full-torus) motive freezes nothing but the constant. -/
theorem varChar_top_eq_zero_iff (ψ : AddChar G ℂ) [Fintype (⊤ : AddSubgroup G)] :
    varChar (⊤ : AddSubgroup G) ψ = 0 ↔ ψ = 0 := by
  rw [varChar_eq_zero_iff, isFrozen_top_iff]

end Analytic

/-! ## Part B — the annihilator lattice on `Fin g → ZMod N` -/

section Algebraic

variable {g N : ℕ} [NeZero N]

/-- The leg pairing `⟨ε, x⟩ = ∑ᵢ εᵢ xᵢ` on `Fin g → ZMod N` — the finite-torus dot product
whose vanishing on `H` names the annihilator lattice. -/
def dot (ε x : Fin g → ZMod N) : ZMod N := ∑ i, ε i * x i

/-- The diagonal embedding `t ↦ (t, …, t)`. -/
def diagHom : ZMod N →+ (Fin g → ZMod N) where
  toFun t := fun _ => t
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The **diagonal subgroup** `Δ = { constant vectors }` — the equidistribution subgroup of
a fully degenerate (all-legs-isogenous) motive. -/
def Delta (g N : ℕ) [NeZero N] : AddSubgroup (Fin g → ZMod N) := (diagHom (g := g) (N := N)).range

/-- **Algebraic freeze**: `ε` annihilates every element of `H` under the pairing.  This is
the annihilator-lattice condition `ε ∈ H^⊥`. -/
def AlgFrozen (H : AddSubgroup (Fin g → ZMod N)) (ε : Fin g → ZMod N) : Prop :=
  ∀ h ∈ H, dot ε h = 0

omit [NeZero N] in
lemma sum_single_mul (j : Fin g) (x : Fin g → ZMod N) :
    (∑ i, (Pi.single j 1 : Fin g → ZMod N) i * x i) = x j := by
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, one_mul]
  · intro i _ hi; rw [Pi.single_eq_of_ne hi, zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

omit [NeZero N] in
/-- **Full group ⇒ annihilator is DC only**: `AlgFrozen ⊤ ε ↔ ε = 0`. -/
theorem algFrozen_top_iff (ε : Fin g → ZMod N) :
    AlgFrozen (⊤ : AddSubgroup (Fin g → ZMod N)) ε ↔ ε = 0 := by
  constructor
  · intro h
    funext j
    have := h (Pi.single j 1) trivial
    simpa [dot, Finset.sum_ite_eq', Pi.single_apply] using this
  · rintro rfl h _; simp [dot]

/-- **Diagonal ⇒ annihilator is the balanced lanes**: `AlgFrozen Δ ε ↔ ∑ᵢ εᵢ = 0`.  The
degenerate motive's frozen frequencies are exactly the *balanced* ones — the same `∑ εᵢ = 0`
condition that `EvenWeightDC` reads as the DC/middle lane. -/
theorem algFrozen_diag_iff (ε : Fin g → ZMod N) :
    AlgFrozen (Delta g N) ε ↔ ∑ i, ε i = 0 := by
  constructor
  · intro h
    have := h (fun _ => 1) ⟨1, rfl⟩
    simpa [dot] using this
  · intro hsum h hh
    obtain ⟨t, rfl⟩ := hh
    show ∑ i, ε i * t = 0
    rw [← Finset.sum_mul, hsum, zero_mul]

omit [NeZero N] in
/-- **Reading-scale invariance of the exact freeze** (the model form of "genuine locks are
reading-scale invariant — check the count, not the freeze"): if `ε` annihilates `H` then so
does any reading-scale multiple `c · ε`.  The exact freeze is a property of the support `H`,
invariant under scaling the reading frequency; only the *quantitative* channel occupancy
(the count) is reading-grid sensitive. -/
theorem algFrozen_readingScale (H : AddSubgroup (Fin g → ZMod N)) (c : ZMod N)
    (ε : Fin g → ZMod N) (hε : AlgFrozen H ε) :
    AlgFrozen H (fun i => c * ε i) := by
  intro x hx
  show ∑ i, c * ε i * x i = 0
  have hkey : (∑ i, c * ε i * x i) = c * dot ε x := by
    unfold dot; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hkey, hε x hx, mul_zero]

/-- **The inversion** (double annihilator): the annihilator of the balanced (frozen) set is
exactly the diagonal.  From the frozen pattern `{ε : ∑ εᵢ = 0}` one recovers `Δ = (Δ^⊥)^⊥`,
so the equidistribution subgroup is read back from its zero-variance lanes alone. -/
theorem diag_double_annihilator [NeZero g] (x : Fin g → ZMod N) :
    (∀ ε : Fin g → ZMod N, (∑ i, ε i = 0) → dot ε x = 0) ↔ x ∈ Delta g N := by
  constructor
  · intro h
    refine ⟨x 0, ?_⟩
    funext j
    show x 0 = x j
    have hbal : ∑ i, (Pi.single j 1 - Pi.single (0 : Fin g) 1 : Fin g → ZMod N) i = 0 := by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single',
        Finset.mem_univ, if_true, sub_self]
    have hd := h _ hbal
    have hval : dot (Pi.single j (1 : ZMod N) - Pi.single (0 : Fin g) (1 : ZMod N)) x = x j - x 0 := by
      unfold dot
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [sum_single_mul j x, sum_single_mul 0 x]
    rw [hval] at hd
    exact (sub_eq_zero.mp hd).symm
  · rintro ⟨t, rfl⟩ ε hsum
    show ∑ i, ε i * t = 0
    rw [← Finset.sum_mul, hsum, zero_mul]

end Algebraic

/-! ## Part C — the bridge and the combined house corollaries -/

section Bridge

variable {g N : ℕ} [NeZero N]

/-- `x ↦ ⟨ε, x⟩` as an additive homomorphism. -/
def dotHom (ε : Fin g → ZMod N) : (Fin g → ZMod N) →+ ZMod N where
  toFun x := dot ε x
  map_zero' := by simp [dot]
  map_add' x y := by simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The **lane character** `χ_ε(x) = ψ₀(⟨ε, x⟩)` built from the standard *primitive* (hence
faithful) character `ψ₀ = ZMod.stdAddChar` — the concrete complex lane of frequency `ε`. -/
noncomputable def laneChar (ε : Fin g → ZMod N) : AddChar (Fin g → ZMod N) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm ((AddChar.toAddMonoidHomEquiv ZMod.stdAddChar).comp (dotHom ε))

lemma laneChar_apply (ε x : Fin g → ZMod N) : laneChar ε x = ZMod.stdAddChar (dot ε x) := by
  simp [laneChar, dotHom]

/-- **The bridge**: analytic freeze of the lane `χ_ε` on `H` (zero variance) ⟺ the algebraic
annihilation `∀ h ∈ H, ⟨ε, h⟩ = 0`.  Uses only that `ZMod.stdAddChar` is faithful
(`ψ₀ k = 1 ↔ k = 0`), which holds because it is primitive. -/
theorem isFrozen_laneChar_iff (H : AddSubgroup (Fin g → ZMod N)) (ε : Fin g → ZMod N) :
    IsFrozen H (laneChar ε) ↔ AlgFrozen H ε := by
  have hfaithful : ∀ k : ZMod N, ZMod.stdAddChar k = 1 ↔ k = 0 :=
    (ZMod.isPrimitive_stdAddChar N).zmod_char_eq_one_iff N
  unfold IsFrozen AlgFrozen
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · rw [← hfaithful, ← laneChar_apply]; exact h x hx
  · rw [laneChar_apply, hfaithful]; exact h x hx

/-- **Full group, combined**: the lane `χ_ε` has zero variance on the whole torus iff `ε`
is the DC frequency `0`. -/
theorem varChar_laneChar_top_iff (ε : Fin g → ZMod N)
    [Fintype (⊤ : AddSubgroup (Fin g → ZMod N))] :
    varChar (⊤ : AddSubgroup (Fin g → ZMod N)) (laneChar ε) = 0 ↔ ε = 0 := by
  rw [varChar_eq_zero_iff, isFrozen_laneChar_iff, algFrozen_top_iff]

/-- **Diagonal, combined** (the degenerate control's law): the lane `χ_ε` has zero variance
on the diagonal iff `ε` is *balanced*, `∑ᵢ εᵢ = 0`.  Channel constancy on the degenerate
motive is exactly the balanced-lane condition of `EvenWeightDC`. -/
theorem varChar_laneChar_diag_iff (ε : Fin g → ZMod N) [Fintype (Delta g N)] :
    varChar (Delta g N) (laneChar ε) = 0 ↔ ∑ i, ε i = 0 := by
  rw [varChar_eq_zero_iff, isFrozen_laneChar_iff, algFrozen_diag_iff]

end Bridge

end ChannelConstancy

#print axioms ChannelConstancy.varChar_eq_ite
#print axioms ChannelConstancy.varChar_eq_zero_iff
#print axioms ChannelConstancy.varChar_top_eq_zero_iff
#print axioms ChannelConstancy.algFrozen_top_iff
#print axioms ChannelConstancy.algFrozen_diag_iff
#print axioms ChannelConstancy.algFrozen_readingScale
#print axioms ChannelConstancy.diag_double_annihilator
#print axioms ChannelConstancy.isFrozen_laneChar_iff
#print axioms ChannelConstancy.varChar_laneChar_top_iff
#print axioms ChannelConstancy.varChar_laneChar_diag_iff
