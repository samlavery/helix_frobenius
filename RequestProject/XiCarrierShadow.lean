import RequestProject.ZetaZeroNative3DSourceTransfer

/-!
# Geometry-first xi zero shadows

The physical carrier height is primary.  Its complex analytic parameter is the carrier
projection, rather than independent data later welded to the carrier.  Consequently the
real coordinate and zero radial drift are geometric theorems.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor
open CriticalLinePhasor.ThreeDFocal
open CriticalLinePhasor.XiChannel

/-- A xi zero represented by a positive physical carrier height. -/
structure XiCarrierShadow where
  height : ℝ
  height_pos : 0 < height
  xi_zero : ZD.riemannXi (carrierPointAtHeight height) = 0

/-- The analytic parameter is produced by the carrier projection. -/
def XiCarrierShadow.analyticParameter (shadow : XiCarrierShadow) : ℂ :=
  carrierPointAtHeight shadow.height

@[ext] theorem XiCarrierShadow.ext {a b : XiCarrierShadow}
    (height_eq : a.height = b.height) : a = b := by
  cases a with
  | mk aHeight aPos aZero =>
      cases b with
      | mk bHeight bPos bZero =>
          simp only at height_eq
          subst bHeight
          rfl

/-- Positive physical heights have distinct analytic projection shadows. -/
theorem XiCarrierShadow.analyticParameter_injective :
    Function.Injective XiCarrierShadow.analyticParameter := by
  intro a b hab
  apply XiCarrierShadow.ext
  have hlog : Real.log a.height = Real.log b.height := by
    have him := congrArg Complex.im hab
    simpa [XiCarrierShadow.analyticParameter] using him
  calc
    a.height = Real.exp (Real.log a.height) := (Real.exp_log a.height_pos).symm
    _ = Real.exp (Real.log b.height) := by rw [hlog]
    _ = b.height := Real.exp_log b.height_pos

@[simp] theorem XiCarrierShadow.analyticParameter_re (shadow : XiCarrierShadow) :
    shadow.analyticParameter.re = 1 / 2 := by
  rw [XiCarrierShadow.analyticParameter, carrierPointAtHeight_re, carrierAbscissa_eq_half]

/-- A geometry-produced analytic parameter has no radial drift. -/
theorem XiCarrierShadow.noRadialDrift (shadow : XiCarrierShadow) (n : ℝ) :
    n ^ (shadow.analyticParameter.re - carrierAbscissa) = 1 := by
  rw [shadow.analyticParameter_re, carrierAbscissa_eq_half, sub_self, Real.rpow_zero]

/-- The radial-drift operator on geometry-produced xi shadows. -/
noncomputable def xiCarrierShadowRadialDriftOperator :
    (XiCarrierShadow →₀ ℂ) →ₗ[ℂ] (XiCarrierShadow →₀ ℂ) :=
  UnconditionalFrobenius.diagOp fun shadow => shadow.analyticParameter.re - 1 / 2

/-- Geometry fixes every projection shadow, so the whole radial-drift operator vanishes. -/
theorem xiCarrierShadowRadialDriftOperator_eq_zero :
    xiCarrierShadowRadialDriftOperator = 0 := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro shadow
  simp [xiCarrierShadowRadialDriftOperator, UnconditionalFrobenius.diagOp_apply]

/-- Forgetting the carrier height embeds a geometry-produced shadow in the analytic zero ledger. -/
def XiCarrierShadow.toXiZeroIndex (shadow : XiCarrierShadow) : XiZeroIndex :=
  ⟨shadow.analyticParameter,
    (ZD.riemannXi_eq_zero_iff shadow.analyticParameter).mp shadow.xi_zero⟩

@[simp] theorem XiCarrierShadow.toXiZeroIndex_re (shadow : XiCarrierShadow) :
    shadow.toXiZeroIndex.val.re = 1 / 2 :=
  shadow.analyticParameter_re

/-- The shadow embedding covers the analytic zero ledger exactly when every ledger parameter is
the carrier projection at its own ordinate. -/
theorem XiCarrierShadow.toXiZeroIndex_surjective_iff :
    Function.Surjective XiCarrierShadow.toXiZeroIndex ↔
      ∀ rho : XiZeroIndex, rho.val.re = 1 / 2 := by
  constructor
  · intro hsurj rho
    obtain ⟨shadow, rfl⟩ := hsurj rho
    exact shadow.toXiZeroIndex_re
  · intro honline rho
    let height : ℝ := Real.exp rho.val.im
    have height_pos : 0 < height := Real.exp_pos rho.val.im
    have hpoint : carrierPointAtHeight height = rho.val := by
      rw [show height = Real.exp rho.val.im by rfl, carrierPointAtHeight_exp]
      apply Complex.ext
      · simpa [carrierPoint, carrierAbscissa_eq_half] using (honline rho).symm
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

/-- Coverage of the analytic zero ledger by carrier shadows has exactly the content needed by
Mathlib's zeta-zero predicate. -/
theorem XiCarrierShadow.toXiZeroIndex_surjective_iff_riemannHypothesis :
    Function.Surjective XiCarrierShadow.toXiZeroIndex ↔ RiemannHypothesis := by
  rw [XiCarrierShadow.toXiZeroIndex_surjective_iff]
  constructor
  · intro honline
    apply RHBridge.no_offline_zeros_implies_rh
    intro rho hrho
    exact honline ⟨rho, hrho⟩
  · intro hRH rho
    exact CriticalLinePhasor.XiChannel.rh_implies_line hRH rho.property

end CriticalLinePhasor.ContourArgument

section AxiomAudit

#print axioms CriticalLinePhasor.ContourArgument.XiCarrierShadow.analyticParameter_re
#print axioms CriticalLinePhasor.ContourArgument.XiCarrierShadow.analyticParameter_injective
#print axioms CriticalLinePhasor.ContourArgument.XiCarrierShadow.noRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.xiCarrierShadowRadialDriftOperator_eq_zero
#print axioms CriticalLinePhasor.ContourArgument.XiCarrierShadow.toXiZeroIndex_re
#print axioms CriticalLinePhasor.ContourArgument.XiCarrierShadow.toXiZeroIndex_surjective_iff
#print axioms
  CriticalLinePhasor.ContourArgument.XiCarrierShadow.toXiZeroIndex_surjective_iff_riemannHypothesis

end AxiomAudit
