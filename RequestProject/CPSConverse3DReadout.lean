import RequestProject.CPSConverse3DQuotient

/-!
# Readout descent through the rank-n CPS carrier quotient

A scalar readout that is unchanged by every diagonal completion clock and every transvection
winding is unchanged by every `GL(n)` move.  Consequently it factors through the 3D carrier
coinvariant.  This is the readout form of the CPS generator descent.
-/

namespace CriticalLinePhasor.ThreeDConverse

/-- The subgroup of linear moves invisible to a readout. -/
def readoutStabilizer
    {G X Y : Type*} [Group G] [MulAction G X]
    (readout : X → Y) : Subgroup G where
  carrier := {g | ∀ x, readout (g • x) = readout x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb x
    rw [mul_smul, ha (b • x), hb x]
  inv_mem' := by
    intro g hg x
    have h := hg (g⁻¹ • x)
    rw [smul_smul, mul_inv_cancel, one_smul] at h
    exact h.symm

/-- Membership in the readout stabilizer is pointwise readout invariance. -/
theorem mem_readoutStabilizer_iff
    {G X Y : Type*} [Group G] [MulAction G X]
    (readout : X → Y) (g : G) :
    g ∈ readoutStabilizer readout ↔ ∀ x, readout (g • x) = readout x :=
  Iff.rfl

/-- Diagonal-clock and transvection-winding invariance imply full readout invariance. -/
theorem cps3D_readout_invariant
    {n K X Y : Type*} [Fintype n] [DecidableEq n] [Field K]
    [MulAction (Matrix.GeneralLinearGroup n K) X]
    (readout : X → Y)
    (hdiag : ∀ (D : n → K) (hD : Matrix.det (Matrix.diagonal D) ≠ 0) (x : X),
      readout
          (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal D) hD • x) =
        readout x)
    (htrans : ∀ (t : Matrix.TransvectionStruct n K) (x : X),
      readout
          (Matrix.GeneralLinearGroup.mkOfDetNeZero t.toMatrix (by simp) • x) =
        readout x)
    (g : Matrix.GeneralLinearGroup n K) (x : X) :
    readout (g • x) = readout x := by
  have hgens : glCarrierGenerators n K ≤
      readoutStabilizer (G := Matrix.GeneralLinearGroup n K) readout := by
    intro y hy
    change ∀ x, readout (y • x) = readout x
    rcases hy with ⟨D, hD, rfl⟩ | ⟨t, rfl⟩
    · exact hdiag D hD
    · exact htrans t
  have hclosure : Subgroup.closure (glCarrierGenerators n K) ≤
      readoutStabilizer (G := Matrix.GeneralLinearGroup n K) readout := by
    rw [Subgroup.closure_le]
    exact hgens
  exact mem_readoutStabilizer_iff readout g |>.mp
    (hclosure (generalLinear_mem_cpsCarrierMoveGroup g)) x

/-- A generator-invariant scalar readout descends canonically to the 3D CPS coinvariant. -/
noncomputable def cps3DReadoutDescend
    {n K X Y : Type*} [Fintype n] [DecidableEq n] [Field K]
    [MulAction (Matrix.GeneralLinearGroup n K) X]
    (readout : X → Y)
    (hdiag : ∀ (D : n → K) (hD : Matrix.det (Matrix.diagonal D) ≠ 0) (x : X),
      readout
          (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal D) hD • x) =
        readout x)
    (htrans : ∀ (t : Matrix.TransvectionStruct n K) (x : X),
      readout
          (Matrix.GeneralLinearGroup.mkOfDetNeZero t.toMatrix (by simp) • x) =
        readout x) :
    CPSCarrierCoinvariant n K X → Y :=
  fun q => Quotient.liftOn' q readout fun a b hab => by
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab
      obtain ⟨g, rfl⟩ := hab
      exact cps3D_readout_invariant readout hdiag htrans g.1 b

/-- Descending and then reading a represented 3D state returns its original scalar readout. -/
theorem cps3DReadoutDescend_mk
    {n K X Y : Type*} [Fintype n] [DecidableEq n] [Field K]
    [MulAction (Matrix.GeneralLinearGroup n K) X]
    (readout : X → Y)
    (hdiag : ∀ (D : n → K) (hD : Matrix.det (Matrix.diagonal D) ≠ 0) (x : X),
      readout
          (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal D) hD • x) =
        readout x)
    (htrans : ∀ (t : Matrix.TransvectionStruct n K) (x : X),
      readout
          (Matrix.GeneralLinearGroup.mkOfDetNeZero t.toMatrix (by simp) • x) =
        readout x)
    (x : X) :
    cps3DReadoutDescend readout hdiag htrans (Quotient.mk'' x) = readout x :=
  rfl

/-- The descended readout assigns the same value to every full `GL(n)` translate. -/
theorem cps3DReadoutDescend_smul
    {n K X Y : Type*} [Fintype n] [DecidableEq n] [Field K]
    [MulAction (Matrix.GeneralLinearGroup n K) X]
    (readout : X → Y)
    (hdiag : ∀ (D : n → K) (hD : Matrix.det (Matrix.diagonal D) ≠ 0) (x : X),
      readout
          (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal D) hD • x) =
        readout x)
    (htrans : ∀ (t : Matrix.TransvectionStruct n K) (x : X),
      readout
          (Matrix.GeneralLinearGroup.mkOfDetNeZero t.toMatrix (by simp) • x) =
        readout x)
    (g : Matrix.GeneralLinearGroup n K) (x : X) :
    cps3DReadoutDescend readout hdiag htrans (Quotient.mk'' (g • x)) =
      cps3DReadoutDescend readout hdiag htrans (Quotient.mk'' x) := by
  rw [cpsCarrierCoinvariant_mk_smul_eq]

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.readoutStabilizer
#print axioms CriticalLinePhasor.ThreeDConverse.cps3D_readout_invariant
#print axioms CriticalLinePhasor.ThreeDConverse.cps3DReadoutDescend_mk
#print axioms CriticalLinePhasor.ThreeDConverse.cps3DReadoutDescend_smul
