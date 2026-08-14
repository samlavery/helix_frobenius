import RequestProject.UpperHalfPlaneOpenPos

/-!
# A vanishing Petersson norm forces the density to vanish on the open domain

The topological upgrade, now that `upperHalfPlane_isOpenPosMeasure` is available.

A continuous function that vanishes almost everywhere on an open set vanishes on it identically —
because the set where it does *not* vanish is open, and a nonempty open set has positive measure.
No approximation is involved: the two hypotheses are exactly complementary, one saying a set is
null and the other saying it cannot be unless it is empty.

**Scope.**  This gives vanishing on `𝒟ᵒ`.  Extending to the closed `𝒟` — which is what
`maassP_not_all_zero_on_fd` would contradict — needs the nonvanishing set to meet `𝒟ᵒ`, i.e. that
the translates of the open domain are co-null.  That is not proved here.

This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.ThreeDConverse

/-- The open modular domain is open. -/
lemma isOpen_fdo : IsOpen ModularGroup.fdo := by
  have h1 : IsOpen {z : ℍ | 1 < Complex.normSq (z : ℂ)} :=
    isOpen_lt continuous_const
      (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  have h2 : IsOpen {z : ℍ | |z.re| < 1 / 2} :=
    isOpen_lt UpperHalfPlane.continuous_re.abs continuous_const
  exact h1.inter h2

/-- **A vanishing Petersson norm forces the density to vanish on the open domain.** -/
theorem maassP_eq_zero_on_fdo (M : GenuineMaassCuspForm3D)
    (h : maassPetersson M = 0) :
    ∀ z ∈ ModularGroup.fdo, maassP M z = 0 := by
  intro z₀ hz₀
  by_contra hne
  -- the nonvanishing part of the open domain is open and nonempty
  have hopen : IsOpen (ModularGroup.fdo ∩ {z : ℍ | maassP M z ≠ 0}) :=
    isOpen_fdo.inter (isOpen_compl_singleton.preimage (continuous_maassP M))
  have hnonempty : (ModularGroup.fdo ∩ {z : ℍ | maassP M z ≠ 0}).Nonempty :=
    ⟨z₀, hz₀, hne⟩
  have hpos : 0 < (volume : Measure ℍ) (ModularGroup.fdo ∩ {z : ℍ | maassP M z ≠ 0}) :=
    hopen.measure_pos volume hnonempty
  -- but the a.e. statement says that set is null
  have hae := maassP_ae_zero_on_fdo M h
  rw [Filter.EventuallyEq, ae_restrict_iff' (isOpen_fdo.measurableSet)] at hae
  have hnull : (volume : Measure ℍ) (ModularGroup.fdo ∩ {z : ℍ | maassP M z ≠ 0}) = 0 := by
    refine measure_mono_null (fun z hz => ?_) hae
    exact fun hcon => hz.2 (hcon hz.1)
  exact hpos.ne' hnull

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.isOpen_fdo
#print axioms CriticalLinePhasor.Unfolding.maassP_eq_zero_on_fdo
