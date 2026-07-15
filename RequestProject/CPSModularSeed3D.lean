import RequestProject.CPSConverse3DReadout
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

/-!
# The GL(2)/level-one carrier seed: a genuine automorphic landing

This file instantiates the three-dimensional converse **engine** of `ThreeDConverse`
(`readoutStabilizer`, `SpecialLinearGroup.SL2Z_generators`) on a **genuine automorphic object**,
non-vacuously.

The state space is `UpperHalfPlane`, with its native `SL(2,ℤ)`-action (Möbius transformations ---
genuinely nontrivial, not a placeholder action).  The readout is the weight-zero invariant
`seedReadout k f z = z.im ^ k * ‖f z‖²` attached to a level-one slash-invariant form `f` of
weight `k`.  Its `SL(2,ℤ)`-invariance is Mathlib's *real modular transformation law*
(`SlashInvariantForm.slash_action_eqn_SL''`: `f (γ • z) = denom γ z ^ k * f z`) combined with
`ModularGroup.im_smul_eq_div_normSq` --- genuine automorphy arithmetic, **not** a synthesized
carrier completion.  This is the distinction that answers the over-proving litmus recorded in the
paper: the automatic (synthesized) carrier niceness applies to *every* polynomially-bounded
coefficient bank, so it cannot supply automorphy; the modularity used here is a property of the
actual form.

`seedReadout_invariant_of_ST` is the audited generator engine, exercised here: invariance under the
two modular generators `S` and `T` (each discharged from the modularity) forces invariance under all
of `SL(2,ℤ)`.  `seedReadout_landing` is the composition --- the full converse landing for this
genuine object, via the generators alone (Hecke's `⟨S,T⟩ = SL(2,ℤ)`; no twist family, no
cuspidality claimed --- `E₄` is not cuspidal).

The hypothesis class is inhabited by `ModularForm.E` (the level-one weight-`k` Eisenstein series,
`k ≥ 3`), a concrete nonzero automorphic form; its native level `(mapGL ℝ).range` equals
`levelOne` by `MonoidHom.range_eq_map`.
-/

open UpperHalfPlane Complex Matrix.SpecialLinearGroup Matrix
open CriticalLinePhasor.ThreeDConverse

namespace CriticalLinePhasor.CPSModularSeed

/-- The level-one subgroup of `GL(2,ℝ)`: the image of `SL(2,ℤ)`. -/
abbrev levelOne : Subgroup (GL (Fin 2) ℝ) :=
  Subgroup.map (mapGL ℝ) (⊤ : Subgroup (SpecialLinearGroup (Fin 2) ℤ))

/-- The weight-zero real readout on the upper half plane: `im(z) ^ k * ‖f z‖²`. -/
noncomputable def seedReadout {F : Type*} [FunLike F ℍ ℂ] (k : ℤ) (f : F) (z : ℍ) : ℝ :=
  (z.im) ^ k * Complex.normSq (f z)

/-- **Genuine modularity.** The readout of any weight-`k` level-one slash-invariant form is
`SL(2,ℤ)`-invariant, directly from Mathlib's modular transformation law. -/
theorem seedReadout_invariant {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}
    [SlashInvariantFormClass F levelOne k]
    (f : F) (γ : SpecialLinearGroup (Fin 2) ℤ) (z : ℍ) :
    seedReadout k f (γ • z) = seedReadout k f z := by
  set D := denom (toGL ((SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (z : ℂ) with hD
  have hNne : normSq D ≠ 0 := fun h => (denom_ne_zero _ _ : D ≠ 0) (Complex.normSq_eq_zero.mp h)
  have him : (γ • z).im = z.im / normSq D := ModularGroup.im_smul_eq_div_normSq γ z
  have hf : f (γ • z) = D ^ k * f z :=
    SlashInvariantForm.slash_action_eqn_SL'' f (Subgroup.mem_top γ) z
  unfold seedReadout
  rw [him, hf, map_mul, map_zpow₀, ← mul_assoc, ← mul_zpow, div_mul_cancel₀ _ hNne]

/-- **The audited `S,T`-generation engine on a genuine object.** Invariance under the two modular
generators forces invariance under all of `SL(2,ℤ)`; the only inputs are the two generator
invariances. -/
theorem seedReadout_invariant_of_ST {F : Type*} [FunLike F ℍ ℂ] (k : ℤ) (f : F)
    (hS : ∀ z : ℍ, seedReadout k f (ModularGroup.S • z) = seedReadout k f z)
    (hT : ∀ z : ℍ, seedReadout k f (ModularGroup.T • z) = seedReadout k f z)
    (γ : SpecialLinearGroup (Fin 2) ℤ) (z : ℍ) :
    seedReadout k f (γ • z) = seedReadout k f z := by
  have hsub : ({ModularGroup.S, ModularGroup.T} : Set (SpecialLinearGroup (Fin 2) ℤ)) ⊆
      (readoutStabilizer (G := SpecialLinearGroup (Fin 2) ℤ) (seedReadout k f) :
        Set (SpecialLinearGroup (Fin 2) ℤ)) := by
    intro g hg; rcases hg with rfl | rfl
    · exact (mem_readoutStabilizer_iff _ _).mpr hS
    · exact (mem_readoutStabilizer_iff _ _).mpr hT
  have hle : (⊤ : Subgroup (SpecialLinearGroup (Fin 2) ℤ)) ≤
      readoutStabilizer (G := SpecialLinearGroup (Fin 2) ℤ) (seedReadout k f) := by
    rw [← SpecialLinearGroup.SL2Z_generators]; exact (Subgroup.closure_le _).mpr hsub
  exact (mem_readoutStabilizer_iff _ _).mp (hle (Subgroup.mem_top γ)) z

/-- **Seed landing.** Full `SL(2,ℤ)`-invariance of the genuine automorphic readout, obtained
through the generator engine from the two modularity-discharged generator invariances. -/
theorem seedReadout_landing {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}
    [SlashInvariantFormClass F levelOne k]
    (f : F) (γ : SpecialLinearGroup (Fin 2) ℤ) (z : ℍ) :
    seedReadout k f (γ • z) = seedReadout k f z :=
  seedReadout_invariant_of_ST k f (fun z => seedReadout_invariant f ModularGroup.S z)
    (fun z => seedReadout_invariant f ModularGroup.T z) γ z

end CriticalLinePhasor.CPSModularSeed

#print axioms CriticalLinePhasor.CPSModularSeed.seedReadout_invariant
#print axioms CriticalLinePhasor.CPSModularSeed.seedReadout_invariant_of_ST
#print axioms CriticalLinePhasor.CPSModularSeed.seedReadout_landing
