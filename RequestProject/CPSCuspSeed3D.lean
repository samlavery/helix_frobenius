import RequestProject.CPSModularSeed3D
import RequestProject.HeckeCancellation

/-!
# The cusp-form seed: genuine invariance and genuine cusp decay, both derived

The modular seed (`CPSModularSeed3D`) closes the generator-descent engine on genuine level-one
slash-invariant forms; its exhibited instance was Eisenstein, where no cuspidality is claimed.
This file instantiates the seed on an actual `CuspForm` and derives, from Mathlib modularity
alone, **both** substantive engine inputs at the base of the tower:

* `cuspSeedReadout_landing` — full `SL(2,ℤ)`-invariance of the genuine cusp form's readout,
  through the audited `S,T`-generation engine (invariance is a theorem of the slash law, never
  an interface field);
* `cuspSeedReadout_exp_decay` — the readout decays exponentially at the cusp
  (`CuspFormClass.exp_decay_atImInfty`): the cuspidality-side content, derived, not supplied.

This is the base-rung discharge of the audit's warning
(`CPSUnconditionalityAudit3D`: arbitrary actions do not give invariance; integrable kernels
need not be cuspidal) — at GL(2) level one the inputs are Mathlib theorems of the
object.  Higher rank remains the named interface.
-/

open Complex UpperHalfPlane Matrix.SpecialLinearGroup Matrix Filter
open scoped MatrixGroups Real

namespace CriticalLinePhasor.CPSModularSeed

/-- The seed's level-one subgroup is the range subgroup `𝒮ℒ` of the rest of the tree. -/
theorem levelOne_eq : levelOne = 𝒮ℒ :=
  (MonoidHom.range_eq_map _).symm

/-- **Genuine cusp-form invariance, landed.**  The readout of an actual level-one cusp form is
invariant under all of `SL(2,ℤ)`, through the audited generator engine — the substantive
invariance input of the converse landing, derived from Mathlib's slash law. -/
theorem cuspSeedReadout_landing {k : ℤ} (f : CuspForm 𝒮ℒ k)
    (γ : SpecialLinearGroup (Fin 2) ℤ) (z : ℍ) :
    seedReadout k f (γ • z) = seedReadout k f z := by
  haveI : SlashInvariantFormClass (CuspForm 𝒮ℒ k) levelOne k := by
    rw [levelOne_eq]; infer_instance
  exact seedReadout_landing f γ z

/-- **Genuine cusp decay, derived.**  The cusp form's readout is exponentially small at the
cusp: the cuspidality-side content of the seed, a theorem of `CuspFormClass`, not an interface
field. -/
theorem cuspSeedReadout_exp_decay {k : ℤ} (f : CuspForm 𝒮ℒ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z : ℍ in UpperHalfPlane.atImInfty,
      seedReadout k f z ≤ C * z.im ^ k * Real.exp (-(4 * π) * z.im) := by
  have hdecay := CuspFormClass.exp_decay_atImInfty (f := f) (h := 1) one_pos
    one_mem_strictPeriods_SL
  rw [Asymptotics.isBigO_iff] at hdecay
  obtain ⟨C, hC⟩ := hdecay
  refine ⟨C ^ 2, sq_nonneg C, ?_⟩
  filter_upwards [hC] with z hz
  have hE : ‖Real.exp (-2 * π * z.im / 1)‖ = Real.exp (-2 * π * z.im) := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, div_one]
  rw [hE] at hz
  have hsq : ‖f z‖ * ‖f z‖ ≤
      (C * Real.exp (-2 * π * z.im)) * (C * Real.exp (-2 * π * z.im)) :=
    mul_self_le_mul_self (norm_nonneg _) hz
  have hexp : Real.exp (-2 * π * z.im) * Real.exp (-2 * π * z.im) =
      Real.exp (-(4 * π) * z.im) := by
    rw [← Real.exp_add]
    ring_nf
  have hnormSq : Complex.normSq (f z) ≤ C ^ 2 * Real.exp (-(4 * π) * z.im) := by
    calc Complex.normSq (f z) = ‖f z‖ * ‖f z‖ := by
          rw [Complex.normSq_eq_norm_sq]; ring
      _ ≤ (C * Real.exp (-2 * π * z.im)) * (C * Real.exp (-2 * π * z.im)) := hsq
      _ = C ^ 2 * (Real.exp (-2 * π * z.im) * Real.exp (-2 * π * z.im)) := by ring
      _ = C ^ 2 * Real.exp (-(4 * π) * z.im) := by rw [hexp]
  have hpow : (0 : ℝ) ≤ z.im ^ k := zpow_nonneg z.im_pos.le k
  calc seedReadout k f z = z.im ^ k * Complex.normSq (f z) := rfl
    _ ≤ z.im ^ k * (C ^ 2 * Real.exp (-(4 * π) * z.im)) :=
        mul_le_mul_of_nonneg_left hnormSq hpow
    _ = C ^ 2 * z.im ^ k * Real.exp (-(4 * π) * z.im) := by ring

end CriticalLinePhasor.CPSModularSeed

#print axioms CriticalLinePhasor.CPSModularSeed.levelOne_eq
#print axioms CriticalLinePhasor.CPSModularSeed.cuspSeedReadout_landing
#print axioms CriticalLinePhasor.CPSModularSeed.cuspSeedReadout_exp_decay
