import RequestProject.GeneralThetaInvariance
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.NumberTheory.Modular

/-!
# The vertical strip is a fundamental domain for the translation subgroup

Slice two of the Rankin–Selberg unfolding chain (brick (iv)).  The subgroup
`Γ∞ = ⟨T⟩ ≤ SL(2,ℤ)` of upper-triangular translations acts on `ℍ` by `z ↦ z + n`, and the
vertical strip `0 ≤ Re z < 1` is a genuine measure-theoretic fundamental domain for this
action (`isFundamentalDomain_strip`) with respect to the invariant hyperbolic measure —
covering by the integer part, *exact* (not just a.e.) disjointness of translates by the
`Re`-window.  Note `-1 ∉ ⟨T⟩`, so the translation subgroup avoids the `±1`-kernel obstruction
that blocks a fundamental domain for the full modular group; the full-domain side of the
unfolding is handled by tiling the strip with coset translates of `ModularGroup.fd` in the
next slice.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups Pointwise

namespace CriticalLinePhasor.Unfolding

/-- The vertical strip `0 ≤ Re z < 1`: the fundamental domain of the translations. -/
def strip : Set ℍ := {z : ℍ | z.re ∈ Set.Ico (0 : ℝ) 1}

/-- The translation subgroup `Γ∞ = ⟨T⟩` of the modular group. -/
def gammaInfty : Subgroup SL(2, ℤ) := Subgroup.zpowers ModularGroup.T

lemma measurableSet_strip : MeasurableSet strip :=
  (measurableSet_Ico).preimage (UpperHalfPlane.continuous_re.measurable)

/-- Membership in a translate of the strip reads off the `Re`-window. -/
lemma mem_T_zpow_smul_strip {w : ℍ} {m : ℤ} :
    w ∈ (ModularGroup.T ^ m) • strip ↔ w.re ∈ Set.Ico (m : ℝ) ((m : ℝ) + 1) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Set.mem_Ico]
    have hre := ModularGroup.re_T_zpow_smul u m
    rw [hre]
    obtain ⟨h0, h1⟩ := hu
    constructor
    · linarith
    · linarith
  · intro hw
    rw [Set.mem_Ico] at hw
    refine ⟨(ModularGroup.T ^ (-m)) • w, ?_, ?_⟩
    · have hre := ModularGroup.re_T_zpow_smul w (-m)
      show ((ModularGroup.T ^ (-m)) • w).re ∈ Set.Ico (0 : ℝ) 1
      rw [Set.mem_Ico, hre]
      push_cast
      constructor
      · linarith [hw.1]
      · linarith [hw.2]
    · show ModularGroup.T ^ m • ModularGroup.T ^ (-m) • w = w
      rw [smul_smul, ← zpow_add, add_neg_cancel, zpow_zero, one_smul]

/-- **The strip is a fundamental domain for the translation subgroup**, with exact
disjointness of translates. -/
theorem isFundamentalDomain_strip :
    IsFundamentalDomain gammaInfty strip (volume : Measure ℍ) where
  nullMeasurableSet := measurableSet_strip.nullMeasurableSet
  ae_covers := by
    refine Filter.Eventually.of_forall fun z => ?_
    refine ⟨⟨ModularGroup.T ^ (-⌊z.re⌋), Subgroup.zpow_mem_zpowers _ _⟩, ?_⟩
    show (ModularGroup.T ^ (-⌊z.re⌋)) • z ∈ strip
    have hre := ModularGroup.re_T_zpow_smul z (-⌊z.re⌋)
    show ((ModularGroup.T ^ (-⌊z.re⌋)) • z).re ∈ Set.Ico (0 : ℝ) 1
    rw [Set.mem_Ico, hre]
    push_cast
    constructor
    · linarith [Int.floor_le z.re]
    · linarith [Int.lt_floor_add_one z.re]
  aedisjoint := by
    intro g g' hne
    apply Disjoint.aedisjoint
    obtain ⟨δ, hδ⟩ := g
    obtain ⟨m, rfl⟩ := hδ
    obtain ⟨δ', hδ'⟩ := g'
    obtain ⟨n, rfl⟩ := hδ'
    have hmn : m ≠ n := by
      rintro rfl
      exact hne rfl
    rw [Set.disjoint_left]
    intro w hw hw'
    have h1 : w ∈ (ModularGroup.T ^ m) • strip := hw
    have h2 : w ∈ (ModularGroup.T ^ n) • strip := hw'
    rw [mem_T_zpow_smul_strip, Set.mem_Ico] at h1 h2
    have hfm : ⌊w.re⌋ = m := by
      rw [Int.floor_eq_iff]
      exact ⟨h1.1, h1.2⟩
    have hfn : ⌊w.re⌋ = n := by
      rw [Int.floor_eq_iff]
      exact ⟨h2.1, h2.2⟩
    exact hmn (hfm ▸ hfn)

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.isFundamentalDomain_strip
