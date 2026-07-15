import RequestProject.CPSRestrictedProductAssembly3D
import Mathlib.Topology.Algebra.MulAction

/-!
# Adelic product assembly for the 3D converse carrier

The archimedean carrier and the finite restricted-product carrier combine into one adelic move
group.  Invariance under the archimedean factor and every finite single-place factor implies
invariance under the complete pair.
-/

open scoped RestrictedProduct

namespace CriticalLinePhasor.ThreeDConverse

/-- **Adelic 3D converse assembly.** The archimedean factor and all finite single-place factors
generate readout invariance under the full archimedean-times-restricted-product move group. -/
theorem cpsAdelic3D_readout_invariant
    {ι X Garch : Type*} {G : ι → Type*} {S : ι → Type*}
    [DecidableEq ι] [Group Garch] [TopologicalSpace Garch]
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, SetLike (S i) (G i)] [∀ i, SubgroupClass (S i) (G i)]
    (A : ∀ i, S i)
    [TopologicalSpace X]
    [MulAction (Garch × (Πʳ i, [G i, (A i : Set (G i))])) X]
    [ContinuousSMul (Garch × (Πʳ i, [G i, (A i : Set (G i))])) X]
    (readout : X → ℂ) (hreadout : Continuous readout)
    (harch : ∀ (a : Garch) (x : X),
      readout ((a, (1 : Πʳ i, [G i, (A i : Set (G i))])) • x) = readout x)
    (hfinite : ∀ (i : ι) (a : G i) (x : X),
      readout (((1 : Garch), RestrictedProduct.mulSingle A i a) • x) = readout x)
    (g : Garch × (Πʳ i, [G i, (A i : Set (G i))])) (x : X) :
    readout (g • x) = readout x := by
  let finiteEmbedding :
      (Πʳ i, [G i, (A i : Set (G i))]) →*
        (Garch × (Πʳ i, [G i, (A i : Set (G i))])) :=
    MonoidHom.inr Garch (Πʳ i, [G i, (A i : Set (G i))])
  letI finiteAction : MulAction (Πʳ i, [G i, (A i : Set (G i))]) X :=
    MulAction.compHom X finiteEmbedding
  have hfiniteEmbedding : Continuous finiteEmbedding := by
    change Continuous (fun a : Πʳ i, [G i, (A i : Set (G i))] => ((1 : Garch), a))
    fun_prop
  letI finiteContinuousAction :
      ContinuousSMul (Πʳ i, [G i, (A i : Set (G i))]) X :=
    MulAction.continuousSMul_compHom hfiniteEmbedding
  have hfiniteAll : ∀ (a : Πʳ i, [G i, (A i : Set (G i))]) (y : X),
      readout (((1 : Garch), a) • y) = readout y := by
    intro a y
    have h := cpsRestrictedProduct3D_readout_invariant A readout hreadout
      (fun i b z => by
        simpa [finiteAction, finiteEmbedding, MulAction.compHom_smul_def] using hfinite i b z)
      a y
    simpa [finiteAction, finiteEmbedding, MulAction.compHom_smul_def] using h
  calc
    readout (g • x) = readout
        (((g.1, (1 : Πʳ i, [G i, (A i : Set (G i))])) * ((1 : Garch), g.2)) • x) := by
      simp
    _ = readout ((g.1, (1 : Πʳ i, [G i, (A i : Set (G i))])) •
        (((1 : Garch), g.2) • x)) := by rw [mul_smul]
    _ = readout (((1 : Garch), g.2) • x) := harch g.1 (((1 : Garch), g.2) • x)
    _ = readout x := hfiniteAll g.2 x

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.cpsAdelic3D_readout_invariant
