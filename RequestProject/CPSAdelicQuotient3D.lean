import RequestProject.CPSUnipotentConstantTerm3D

/-!
# Rational-orbit quotient descent for the adelic 3D carrier

An invariant adelic readout descends canonically to the quotient by any designated rational
subgroup.  Applying the adelic assembly theorem supplies the invariance needed for this descent.
-/

open scoped RestrictedProduct

namespace CriticalLinePhasor.ThreeDConverse

/-- The orbit quotient of a carrier state space by a rational subgroup. -/
abbrev RationalOrbitQuotient
    {G : Type*} [Group G] (H : Subgroup G) (X : Type*) [MulAction G X] :=
  MulAction.orbitRel.Quotient H X

/-- An invariant scalar readout descends to the rational orbit quotient. -/
noncomputable def rationalQuotientReadout
    {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (readout : X → ℂ)
    (hinvariant : ∀ (h : H) (x : X), readout (h.1 • x) = readout x) :
    RationalOrbitQuotient H X → ℂ :=
  Quotient.lift readout (by
    intro a b hab
    change a ∈ MulAction.orbit H b at hab
    rw [MulAction.mem_orbit_iff] at hab
    obtain ⟨h, rfl⟩ := hab
    exact hinvariant h b)

/-- The quotient readout agrees with the original readout on every representative. -/
theorem rationalQuotientReadout_mk
    {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (readout : X → ℂ)
    (hinvariant : ∀ (h : H) (x : X), readout (h.1 • x) = readout x)
    (x : X) :
    rationalQuotientReadout H readout hinvariant (Quotient.mk'' x) = readout x :=
  rfl

/-- Full carrier invariance supplies the rational-subgroup invariance required for quotient descent. -/
theorem rationalSubgroup_invariant_of_full_invariant
    {G X : Type*} [Group G] [MulAction G X]
    (readout : X → ℂ) (hall : ∀ (g : G) (x : X), readout (g • x) = readout x)
    (H : Subgroup G) :
    ∀ (h : H) (x : X), readout (h.1 • x) = readout x :=
  fun h x => hall h.1 x

/-- **Adelic rational-quotient descent.** The local 3D generator identities assemble adelically,
then descend the resulting readout to any rational subgroup orbit quotient. -/
noncomputable def cpsAdelic3D_rationalQuotientReadout
    {ι X Garch : Type*} {G : ι → Type*} {S : ι → Type*}
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
      readout (((1 : Garch), RestrictedProduct.mulSingle A i a) • x) = readout x) :
    RationalOrbitQuotient H X → ℂ :=
  rationalQuotientReadout H readout fun h x =>
    cpsAdelic3D_readout_invariant A readout hreadout harch hfinite h.1 x

/-- The adelic quotient construction reads every representative by the original 3D readout. -/
theorem cpsAdelic3D_rationalQuotientReadout_mk
    {ι X Garch : Type*} {G : ι → Type*} {S : ι → Type*}
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
    (x : X) :
    cpsAdelic3D_rationalQuotientReadout A H readout hreadout harch hfinite
      (Quotient.mk'' x) = readout x :=
  rfl

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.rationalQuotientReadout_mk
#print axioms CriticalLinePhasor.ThreeDConverse.rationalSubgroup_invariant_of_full_invariant
#print axioms CriticalLinePhasor.ThreeDConverse.cpsAdelic3D_rationalQuotientReadout_mk
