import RequestProject.RadialBoundedness
import RequestProject.XiCarrierShadow

/-!
# Reflected radial bounds produce carrier shadows

This layer isolates the separation step missing from the reflected-pair product identity.
A uniform bound on the two reciprocal radial modes forces their exponent to vanish.  The
area law then turns that vanishing exponent into carrier-scale balance and an explicit
geometry-produced shadow of the analytic zero.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor
open CriticalLinePhasor.Phasor3D
open CriticalLinePhasor.ThreeDFocal
open CriticalLinePhasor.XiChannel
open Filter Topology

/- Search audit for the unfolded target:

`rg -n -i "reflected.*radial.*bound|radial.*pair.*bound|rpow.*pair.*bound|XiZeroIndex|
  NontrivialZeros|one_sub_conj|radialMagnitude|carrierScaleBalanced" RequestProject`

`rg -n -i "rpow.*bounded|bounded.*rpow|rpow.*add.*neg|pow.*inverse.*bounded|
  NontrivialZeros|RiemannHypothesis" .lake/packages/mathlib/Mathlib`
-/

/-- The reflected reciprocal powers are uniformly bounded exactly when the analytic exponent is
the area-law half-unit. -/
theorem reflectedRadialPairBounded_iff_re_eq_half (rho : XiZeroIndex) :
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ^ (1 / 2 - rho.val.re) +
        (n : ℝ) ^ (-(1 / 2 - rho.val.re)) ≤ C) ↔
      rho.val.re = 1 / 2 := by
  constructor
  · rintro ⟨C, hC⟩
    have hzero : 1 / 2 - rho.val.re = 0 :=
      RadialBoundedness.eq_zero_of_rpow_pair_bounded hC
    linarith
  · intro hre
    refine ⟨2, ?_⟩
    intro n hn
    rw [hre]
    norm_num

/-- The quantified reflected radial bound is exactly the pointwise carrier-scale balance
condition on the analytic zero ledger. -/
theorem all_reflectedRadialPairBounded_iff_all_carrierScaleBalanced :
    (∀ rho : XiZeroIndex, ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ^ (1 / 2 - rho.val.re) +
        (n : ℝ) ^ (-(1 / 2 - rho.val.re)) ≤ C) ↔
      ∀ rho : XiZeroIndex, CarrierScaleBalanced rho.val.re := by
  constructor
  · intro hbound rho
    apply (carrierScaleBalanced_iff rho.val.re).2
    exact (reflectedRadialPairBounded_iff_re_eq_half rho).1 (hbound rho)
  · intro hbalanced rho
    apply (reflectedRadialPairBounded_iff_re_eq_half rho).2
    exact (carrierScaleBalanced_iff rho.val.re).1 (hbalanced rho)

/-- Coverage of the analytic zero ledger by geometry-produced shadows supplies the global
reflected radial bound with the explicit constant `2` on every mode. -/
theorem all_reflectedRadialPairBounded_of_carrierShadowCoverage
    (hcoverage : Function.Surjective XiCarrierShadow.toXiZeroIndex) :
    ∀ rho : XiZeroIndex, ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ^ (1 / 2 - rho.val.re) +
        (n : ℝ) ^ (-(1 / 2 - rho.val.re)) ≤ C := by
  intro rho
  obtain ⟨shadow, rfl⟩ := hcoverage rho
  apply (reflectedRadialPairBounded_iff_re_eq_half shadow.toXiZeroIndex).2
  exact shadow.toXiZeroIndex_re

/-- A uniform reflected-pair radial bound forces the zero's analytic fiber to be balanced
against the arclength carrier scale. -/
theorem carrierScaleBalanced_of_reflectedRadialPairBounded
    (rho : XiZeroIndex) {C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ^ (1 / 2 - rho.val.re) +
        (n : ℝ) ^ (-(1 / 2 - rho.val.re)) ≤ C) :
    CarrierScaleBalanced rho.val.re := by
  have hradial : 1 / 2 - rho.val.re = 0 :=
    RadialBoundedness.eq_zero_of_rpow_pair_bounded hbound
  apply (carrierScaleBalanced_iff rho.val.re).2
  linarith

/-- The same bound yields the positive finite area-normalized magnitude limit of the literal
three-dimensional analytic fiber. -/
theorem radialMagnitudeBalanced_of_reflectedRadialPairBounded
    (rho : XiZeroIndex) {C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ^ (1 / 2 - rho.val.re) +
        (n : ℝ) ^ (-(1 / 2 - rho.val.re)) ≤ C) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto
        (fun n : ℕ =>
          mag3 ((principalZeroAnalyticFiber3D rho.property).state n) *
            Geometry.carrierRadius 1 3 n)
        atTop (nhds L) := by
  apply
    (PrincipalZeroAnalyticFiber3D.carrierScaleBalanced_iff_radialMagnitude
      (principalZeroAnalyticFiber3D rho.property)).1
  exact carrierScaleBalanced_of_reflectedRadialPairBounded rho hbound

/-- A reflected-pair radial bound constructs a positive carrier height whose projection is the
given analytic zero. -/
theorem exists_carrierShadow_of_reflectedRadialPairBounded
    (rho : XiZeroIndex) {C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ^ (1 / 2 - rho.val.re) +
        (n : ℝ) ^ (-(1 / 2 - rho.val.re)) ≤ C) :
    ∃ shadow : XiCarrierShadow, shadow.toXiZeroIndex = rho := by
  have hbalanced : CarrierScaleBalanced rho.val.re :=
    carrierScaleBalanced_of_reflectedRadialPairBounded rho hbound
  have hre : rho.val.re = 1 / 2 :=
    (carrierScaleBalanced_iff rho.val.re).1 hbalanced
  let height : ℝ := Real.exp rho.val.im
  have height_pos : 0 < height := Real.exp_pos rho.val.im
  have hpoint : carrierPointAtHeight height = rho.val := by
    rw [show height = Real.exp rho.val.im by rfl, carrierPointAtHeight_exp]
    apply Complex.ext
    · simpa [carrierPoint, carrierAbscissa_eq_half] using hre.symm
    · simp [carrierPoint]
  let shadow : XiCarrierShadow :=
    { height := height
      height_pos := height_pos
      xi_zero := by
        rw [hpoint]
        exact (ZD.riemannXi_eq_zero_iff rho.val).mpr rho.property }
  refine ⟨shadow, ?_⟩
  apply Subtype.ext
  exact hpoint

/-- Pointwise reflected radial bounds cover the entire analytic zero ledger by geometry-produced
carrier shadows. -/
theorem xiCarrierShadow_surjective_of_all_reflectedRadialPairBounded
    (hbound : ∀ rho : XiZeroIndex, ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ^ (1 / 2 - rho.val.re) +
        (n : ℝ) ^ (-(1 / 2 - rho.val.re)) ≤ C) :
    Function.Surjective XiCarrierShadow.toXiZeroIndex := by
  intro rho
  obtain ⟨C, hC⟩ := hbound rho
  exact exists_carrierShadow_of_reflectedRadialPairBounded rho hC

/-- The global reflected-pair radial bound discharges Mathlib's zeta-zero-line theorem through
the explicit carrier-shadow construction. -/
theorem riemannHypothesis_of_all_reflectedRadialPairBounded
    (hbound : ∀ rho : XiZeroIndex, ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ^ (1 / 2 - rho.val.re) +
        (n : ℝ) ^ (-(1 / 2 - rho.val.re)) ≤ C) :
    RiemannHypothesis := by
  apply RHBridge.no_offline_zeros_implies_rh
  intro rho hrho
  let indexedZero : XiZeroIndex := ⟨rho, hrho⟩
  obtain ⟨shadow, hshadow⟩ :=
    xiCarrierShadow_surjective_of_all_reflectedRadialPairBounded hbound indexedZero
  have hre := shadow.toXiZeroIndex_re
  rw [hshadow] at hre
  exact hre

end CriticalLinePhasor.ContourArgument

section AxiomAudit

#print axioms
  CriticalLinePhasor.ContourArgument.reflectedRadialPairBounded_iff_re_eq_half
#print axioms
  CriticalLinePhasor.ContourArgument.all_reflectedRadialPairBounded_iff_all_carrierScaleBalanced
#print axioms
  CriticalLinePhasor.ContourArgument.all_reflectedRadialPairBounded_of_carrierShadowCoverage
#print axioms
  CriticalLinePhasor.ContourArgument.carrierScaleBalanced_of_reflectedRadialPairBounded
#print axioms
  CriticalLinePhasor.ContourArgument.radialMagnitudeBalanced_of_reflectedRadialPairBounded
#print axioms
  CriticalLinePhasor.ContourArgument.exists_carrierShadow_of_reflectedRadialPairBounded
#print axioms
  CriticalLinePhasor.ContourArgument.xiCarrierShadow_surjective_of_all_reflectedRadialPairBounded
#print axioms
  CriticalLinePhasor.ContourArgument.riemannHypothesis_of_all_reflectedRadialPairBounded

end AxiomAudit
