import RequestProject.CPSCuspidalLanding3D

/-!
# The assembled three-dimensional CPS landing theorem

This file composes local-to-adelic carrier invariance, rational-orbit descent, and simultaneous
proper-unipotent constant-term cancellation.
-/

open scoped RestrictedProduct

namespace CriticalLinePhasor.ThreeDConverse

open MeasureTheory

/-- **Assembled 3D CPS landing theorem.** The local archimedean and finite-place generator laws
produce a well-defined readout on the rational adelic quotient.  Nontrivial eigenmoves in every
proper unipotent channel make that quotient readout cuspidal. -/
theorem cpsConverse3D_landing
    {ι X Garch P : Type*} {G : ι → Type*} {S : ι → Type*}
    [DecidableEq ι] [Group Garch] [TopologicalSpace Garch]
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, SetLike (S i) (G i)] [∀ i, SubgroupClass (S i) (G i)]
    (A : ∀ i, S i)
    [TopologicalSpace X]
    [MulAction (Garch × (Πʳ i, [G i, (A i : Set (G i))])) X]
    [ContinuousSMul (Garch × (Πʳ i, [G i, (A i : Set (G i))])) X]
    (H : Subgroup (Garch × (Πʳ i, [G i, (A i : Set (G i))])))
    (readout : X → ℂ) (hreadout : Continuous readout)
    (harch : ∀ (a : Garch) (x : X),
      readout ((a, (1 : Πʳ i, [G i, (A i : Set (G i))])) • x) = readout x)
    (hfinite : ∀ (i : ι) (a : G i) (x : X),
      readout (((1 : Garch), RestrictedProduct.mulSingle A i a) • x) = readout x)
    {U : P → Type*}
    [∀ p, MeasurableSpace (U p)] [∀ p, Group (U p)]
    [∀ p, MeasurableMul (U p)] [∀ p, MeasurableInv (U p)]
    (μ : ∀ p, Measure (U p)) [∀ p, Measure.IsMulLeftInvariant (μ p)]
    (translate : ∀ p,
      RationalOrbitQuotient H X → U p → RationalOrbitQuotient H X)
    (hintegrable : ∀ p q, Integrable
      (quotientUnipotentKernel
        (cpsAdelic3D_rationalQuotientReadout A H readout hreadout harch hfinite)
        translate p q) (μ p))
    (move : ∀ p, RationalOrbitQuotient H X → U p)
    (eigenvalue : P → RationalOrbitQuotient H X → ℂ)
    (heigen : ∀ p q u,
      cpsAdelic3D_rationalQuotientReadout A H readout hreadout harch hfinite
          (translate p q (move p q * u)) =
        eigenvalue p q *
          cpsAdelic3D_rationalQuotientReadout A H readout hreadout harch hfinite
            (translate p q u))
    (hnontrivial : ∀ p q, eigenvalue p q ≠ 1) :
    (∀ x : X,
      cpsAdelic3D_rationalQuotientReadout A H readout hreadout harch hfinite
        (Quotient.mk'' x) = readout x) ∧
    CuspidalAlong3D μ
      (quotientUnipotentKernel
        (cpsAdelic3D_rationalQuotientReadout A H readout hreadout harch hfinite)
        translate) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact cpsAdelic3D_rationalQuotientReadout_mk A H readout hreadout harch hfinite x
  · exact cpsQuotientReadout_cuspidalAlong3D μ
      (cpsAdelic3D_rationalQuotientReadout A H readout hreadout harch hfinite)
      translate hintegrable move eigenvalue heigen hnontrivial

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.cpsConverse3D_landing
