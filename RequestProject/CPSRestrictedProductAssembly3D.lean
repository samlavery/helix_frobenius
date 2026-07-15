import RequestProject.CPSProductAssembly3D
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Restricted-product assembly for the 3D converse carrier

The finite-coordinate moves are dense in the classical restricted-product topology.  Local
single-place invariance therefore composes over finite support and extends by continuity to every
restricted-product move.
-/

open scoped RestrictedProduct

namespace CriticalLinePhasor.ThreeDConverse

/-- Truncate a point in a principal restricted-product stage to finitely many coordinates. -/
def restrictedPrincipalTruncation
    {ι : Type*} {G : ι → Type*} {S : ι → Type*}
    [DecidableEq ι] [∀ i, Group (G i)] [∀ i, SetLike (S i) (G i)]
    [∀ i, SubgroupClass (S i) (G i)]
    (A : ∀ i, S i) (T : Set ι)
    (s : Finset ι) (g : Πʳ i, [G i, (A i : Set (G i))]_[Filter.principal T]) :
    Πʳ i, [G i, (A i : Set (G i))]_[Filter.principal T] := by
  refine RestrictedProduct.mk (finiteMulTruncation s fun i => g i) ?_
  rw [Filter.eventually_principal]
  intro i hiT
  by_cases his : i ∈ s
  · have hg := g.2
    rw [Filter.eventually_principal] at hg
    simp only [finiteMulTruncation, his, if_true]
    change g.val i ∈ (A i : Set (G i))
    exact hg i hiT
  · simpa [finiteMulTruncation, his] using (show (1 : G i) ∈ (A i : Set (G i)) from one_mem _)

/-- Principal-stage truncations converge in the principal restricted-product topology. -/
theorem restrictedPrincipalTruncation_tendsto
    {ι : Type*} {G : ι → Type*} {S : ι → Type*}
    [DecidableEq ι] [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, SetLike (S i) (G i)] [∀ i, SubgroupClass (S i) (G i)]
    (A : ∀ i, S i) (T : Set ι)
    (g : Πʳ i, [G i, (A i : Set (G i))]_[Filter.principal T]) :
    Filter.Tendsto (fun s : Finset ι => restrictedPrincipalTruncation A T s g)
      Filter.atTop (nhds g) := by
  apply RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff.mpr
  change Filter.Tendsto (fun s : Finset ι => finiteMulTruncation s (fun i => g i))
    Filter.atTop (nhds (fun i => g i))
  exact finiteMulTruncation_tendsto (fun i => g i)

/-- Finite-coordinate moves are dense in the classical restricted product. -/
theorem dense_restricted_hasFiniteProductSupport
    {ι : Type*} {G : ι → Type*} {S : ι → Type*}
    [DecidableEq ι] [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, SetLike (S i) (G i)] [∀ i, SubgroupClass (S i) (G i)]
    (A : ∀ i, S i) :
    Dense {g : Πʳ i, [G i, (A i : Set (G i))] |
      HasFiniteProductSupport (fun i => g i)} := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro g
  let T : Set ι := {i | g i ∈ (A i : Set (G i))}
  have hT : Filter.cofinite ≤ Filter.principal T := by
    rw [Filter.le_principal_iff]
    exact g.2
  let gT : Πʳ i, [G i, (A i : Set (G i))]_[Filter.principal T] :=
    RestrictedProduct.mk (fun i => g i) (by
      rw [Filter.eventually_principal]
      intro i hi
      exact hi)
  have hinclusion : RestrictedProduct.inclusion G (fun i => (A i : Set (G i))) hT gT = g := by
    apply RestrictedProduct.ext
    intro i
    rfl
  let approximation : Finset ι → Πʳ i, [G i, (A i : Set (G i))] := fun s =>
    RestrictedProduct.inclusion G (fun i => (A i : Set (G i))) hT
      (restrictedPrincipalTruncation A T s gT)
  have happ : Filter.Tendsto approximation Filter.atTop (nhds g) := by
    rw [← hinclusion]
    exact (RestrictedProduct.continuous_inclusion hT).tendsto gT |>.comp
      (restrictedPrincipalTruncation_tendsto A T gT)
  apply mem_closure_of_tendsto happ
  exact Filter.Eventually.of_forall fun s => by
    change HasFiniteProductSupport
      (fun i => approximation s i)
    simpa [approximation, restrictedPrincipalTruncation] using
      (finiteMulTruncation_hasFiniteMulSupport s (fun i => gT i))

/-- Single-place invariance composes to every finite-support restricted-product move. -/
theorem restricted_readout_invariant_of_single_moves_of_finiteSupport
    {ι X : Type*} {G : ι → Type*} {S : ι → Type*}
    [DecidableEq ι] [∀ i, Group (G i)] [∀ i, SetLike (S i) (G i)]
    [∀ i, SubgroupClass (S i) (G i)]
    (A : ∀ i, S i) [MulAction (Πʳ i, [G i, (A i : Set (G i))]) X]
    (readout : X → ℂ)
    (hsingle : ∀ (i : ι) (a : G i) (x : X),
      readout (RestrictedProduct.mulSingle A i a • x) = readout x)
    (g : Πʳ i, [G i, (A i : Set (G i))])
    (hg : HasFiniteProductSupport (fun i => g i)) (x : X) :
    readout (g • x) = readout x := by
  have hind : ∀ s : Finset ι,
      ∀ (g : Πʳ i, [G i, (A i : Set (G i))]),
      (∀ i, i ∉ s → g i = 1) → ∀ x : X, readout (g • x) = readout x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro g hg x
        have hgone : g = 1 := by
          apply RestrictedProduct.ext
          intro i
          exact hg i (by simp)
        simp [hgone]
    | @insert a s ha ih =>
        intro g hg x
        let single := RestrictedProduct.mulSingle A a (g a)
        let tail : Πʳ i, [G i, (A i : Set (G i))] := single⁻¹ * g
        have htail : ∀ i, i ∉ s → tail i = 1 := by
          intro i hi
          by_cases hia : i = a
          · subst i
            simp [tail, single]
          · simp [tail, single, RestrictedProduct.mulSingle_eq_of_ne A (g a) hia,
              hg i (by simp [hia, hi])]
        have hdecomp : single * tail = g := by
          simp [tail]
        rw [← hdecomp, mul_smul]
        calc
          readout (single • tail • x) = readout (tail • x) :=
            hsingle a (g a) (tail • x)
          _ = readout x := ih tail htail x
  change Set.Finite {i | g i ≠ 1} at hg
  apply hind hg.toFinset g
  intro i hi
  have himem : i ∉ {j | g j ≠ 1} := by
    simpa using hi
  by_contra hgi
  exact himem hgi

/-- **Restricted-product 3D converse assembly.** Continuous readout invariance under every
single-place move extends to every move in the classical restricted product. -/
theorem cpsRestrictedProduct3D_readout_invariant
    {ι X : Type*} {G : ι → Type*} {S : ι → Type*}
    [DecidableEq ι] [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, SetLike (S i) (G i)] [∀ i, SubgroupClass (S i) (G i)]
    (A : ∀ i, S i)
    [TopologicalSpace X]
    [MulAction (Πʳ i, [G i, (A i : Set (G i))]) X]
    [ContinuousSMul (Πʳ i, [G i, (A i : Set (G i))]) X]
    (readout : X → ℂ) (hreadout : Continuous readout)
    (hsingle : ∀ (i : ι) (a : G i) (x : X),
      readout (RestrictedProduct.mulSingle A i a • x) = readout x)
    (g : Πʳ i, [G i, (A i : Set (G i))]) (x : X) :
    readout (g • x) = readout x := by
  apply readout_invariant_of_dense_moves
    {g : Πʳ i, [G i, (A i : Set (G i))] |
      HasFiniteProductSupport (fun i => g i)}
    (dense_restricted_hasFiniteProductSupport A) readout hreadout
  intro a ha y
  exact restricted_readout_invariant_of_single_moves_of_finiteSupport A readout hsingle a ha y

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.restrictedPrincipalTruncation_tendsto
#print axioms CriticalLinePhasor.ThreeDConverse.dense_restricted_hasFiniteProductSupport
#print axioms CriticalLinePhasor.ThreeDConverse.restricted_readout_invariant_of_single_moves_of_finiteSupport
#print axioms CriticalLinePhasor.ThreeDConverse.cpsRestrictedProduct3D_readout_invariant
