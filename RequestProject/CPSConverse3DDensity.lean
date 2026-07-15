import RequestProject.CPSFiniteFieldConverse3D
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Continuity descent from finite carrier moves

For a continuous topological action, readout invariance on a dense family of carrier moves extends
to every move.  This is the topological passage used after finite compact-open Fourier separation.
-/

namespace CriticalLinePhasor.ThreeDConverse

/-- A continuous scalar readout invariant under a dense set of moves is invariant under the full
topological move group. -/
theorem readout_invariant_of_dense_moves
    {G X : Type*} [TopologicalSpace G] [Group G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    (moves : Set G) (hmoves : Dense moves)
    (readout : X → ℂ) (hreadout : Continuous readout)
    (hmove : ∀ g ∈ moves, ∀ x : X, readout (g • x) = readout x) :
    ∀ g : G, ∀ x : X, readout (g • x) = readout x := by
  intro g x
  let orbitReadout : G → ℂ := fun a => readout (a • x)
  have horbit : Continuous orbitReadout := by
    dsimp [orbitReadout]
    fun_prop
  have hconstant : Continuous (fun _ : G => readout x) := continuous_const
  have heq : orbitReadout = fun _ : G => readout x :=
    horbit.ext_on hmoves hconstant (by
      intro a ha
      exact hmove a ha x)
  exact congrFun heq g

/-- Dense-range version: invariance under every move produced by a dense parametrization extends
to the whole topological move group. -/
theorem readout_invariant_of_denseRange
    {A G X : Type*} [TopologicalSpace G] [Group G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    (approximation : A → G) (hdense : DenseRange approximation)
    (readout : X → ℂ) (hreadout : Continuous readout)
    (happrox : ∀ a : A, ∀ x : X,
      readout (approximation a • x) = readout x) :
    ∀ g : G, ∀ x : X, readout (g • x) = readout x := by
  apply readout_invariant_of_dense_moves (Set.range approximation) hdense readout hreadout
  intro g hg x
  obtain ⟨a, rfl⟩ := hg
  exact happrox a x

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.readout_invariant_of_dense_moves
#print axioms CriticalLinePhasor.ThreeDConverse.readout_invariant_of_denseRange
