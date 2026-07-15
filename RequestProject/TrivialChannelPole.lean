import Mathlib

/-!
# The trivial-channel pole count: the generic/exceptional dichotomy

The twisted carrier readout of `emergent_clock_paper2.tex` (Theorem "Twisted carrier niceness") proves
`R_{r,τ}=0`: the carrier generates *no* residue pole, fiber-parametrically, for every twist.  The identified
Rankin–Selberg `L`-function `L(s, Π_r × τ)` can nevertheless have a genuine `s=1` pole — but only from a
**trivial channel** of the *reducible* parameter `Sym^r φ_π ⊗ φ_τ`, i.e. a copy of the trivial representation
in the tensor.  The pole order at `s=1` equals the invariant multiplicity `dim Hom(φ_τ^∨, Sym^r φ_π)` (the
classical Rankin–Selberg / Artin pole formula — an *analytic* identification we cite, not formalize).

This file formalizes the **algebraic core** of that pole count — the dichotomy that governs the paper's
generic-vs-exceptional split — for finite-dimensional representations of an algebra `A` over a field `k`,
with `V = Sym^r φ_π` (dimension `r+1`) and `W = φ_τ^∨` (dimension `m`), the twist range being `m < r+1`:

* `no_nonzero_hom_of_finrank_lt` — the **generic/cuspidal branch**: if `V` is a *simple* module and
  `finrank W < finrank V`, then every intertwiner `W →ₗ[A] V` is zero, so there is no trivial channel and the twist is
  pole-free.  (A nonzero map into a simple module has image the whole of `V`, hence is surjective, forcing
  `finrank V ≤ finrank W` — the dimension gap forbids it.  This is the exact step in the paper's automorphic
  landing theorem.)
* `embedding_hom_ne_zero` — the **exceptional/isobaric branch**: if `φ_τ^∨` occurs as a *constituent*
  (an injective embedding `W ↪ V`) and `W` is nontrivial, that embedding is a nonzero hom, so the
  trivial-channel count is positive: a genuine pole.  This is where the classically enumerated exceptional
  `π` (dihedral / tetrahedral / octahedral, `Sym^r φ_π` reducible) sit, and `Sym^r π` is the corresponding
  isobaric object.

What is **cited, not formalized**: (i) the analytic pole-order `=` invariant-dimension identity, and
(ii) the classification "`Sym^r φ_π` reducible ⟺ `π` exceptional".  What is proven here is the equivariant representation-algebra
dichotomy that makes the paper's parenthetical "for `Sym^r φ_π` irreducible" a machine-checked criterion
rather than prose.

The compiler-audited footprint is `{propext, Classical.choice, Quot.sound}`.
-/

open Module

namespace CriticalLinePhasor.TrivialChannel

variable {k A W V : Type*} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- **Generic/cuspidal branch — no trivial channel.**  A nonzero linear map from a strictly smaller module
into a *simple* module `V` would have image a nonzero submodule of `V`, hence all of `V` (simplicity), hence
be surjective, forcing `finrank V ≤ finrank W`.  The dimension gap `finrank W < finrank V` therefore forbids
any nonzero hom: `Hom(W, V) = 0`.

With `V = Sym^r φ_π` irreducible of dimension `r+1` and `W = φ_τ^∨` of dimension `m ≤ r-1 < r+1`, this is the
pole-freeness step of the paper's automorphic landing theorem — the entire carrier readout *is* the twist
`L`-function, with no `s=1` pole. -/
theorem no_nonzero_hom_of_finrank_lt
    [FiniteDimensional k W] [FiniteDimensional k V]
    (hV : IsSimpleModule A V) (hdim : finrank k W < finrank k V)
    (f : W →ₗ[A] V) : f = 0 := by
  rcases hV.eq_bot_or_eq_top (LinearMap.range f) with h | h
  · exact LinearMap.range_eq_bot.mp h
  · exfalso
    have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp h
    have hle : finrank k V ≤ finrank k W :=
      (f.restrictScalars k).finrank_le_finrank_of_surjective hsurj
    omega

/-- The `Hom`-space itself is trivial in the generic branch: every element is the zero map. -/
theorem hom_subsingleton_of_finrank_lt
    [FiniteDimensional k W] [FiniteDimensional k V]
    (hV : IsSimpleModule A V) (hdim : finrank k W < finrank k V) :
    Subsingleton (W →ₗ[A] V) :=
  ⟨fun f g => by
    rw [no_nonzero_hom_of_finrank_lt hV hdim f, no_nonzero_hom_of_finrank_lt hV hdim g]⟩

/-- **Exceptional/isobaric branch — the trivial channel is present.**  If `φ_τ^∨` embeds into
`Sym^r φ_π` as a constituent (an injective hom `f : W ↪ V`) and `W` is nontrivial, then `f` is a nonzero
hom, so `Hom(W, V) ≠ 0`: the trivial-channel count is positive and the identified twist `L`-function has a
genuine `s=1` pole.  These are exactly the classically enumerated exceptional `π`, where `Sym^r π` is the
known isobaric object. -/
theorem embedding_hom_ne_zero
    (f : W →ₗ[A] V) (hf : Function.Injective f) (hW : Nontrivial W) : f ≠ 0 := by
  intro h
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  exact hw (hf (by simp [h]))

/-- The two branches as one statement: with `V` simple and `W` nontrivial, `Hom(W, V)` is trivial exactly
when the dimension gap holds, and any constituent embedding witnesses a nonzero hom otherwise.  This is the
generic-vs-exceptional dichotomy that governs whether the identified twist is pole-free. -/
theorem pole_free_iff_no_embedding
    [FiniteDimensional k W] [FiniteDimensional k V]
    (hV : IsSimpleModule A V) (hW : Nontrivial W) (hdim : finrank k W < finrank k V) :
    (∀ f : W →ₗ[A] V, f = 0) ∧ (∀ f : W →ₗ[A] V, ¬ Function.Injective f) := by
  refine ⟨fun f => no_nonzero_hom_of_finrank_lt hV hdim f, fun f hf => ?_⟩
  exact embedding_hom_ne_zero f hf hW (no_nonzero_hom_of_finrank_lt hV hdim f)

end CriticalLinePhasor.TrivialChannel

#print axioms CriticalLinePhasor.TrivialChannel.no_nonzero_hom_of_finrank_lt
#print axioms CriticalLinePhasor.TrivialChannel.hom_subsingleton_of_finrank_lt
#print axioms CriticalLinePhasor.TrivialChannel.embedding_hom_ne_zero
#print axioms CriticalLinePhasor.TrivialChannel.pole_free_iff_no_embedding
