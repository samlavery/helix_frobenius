import RequestProject.ZetaZeroNative3DSourceTransfer

open Complex

noncomputable section

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor
open CriticalLinePhasor.ThreeDFocal
open CriticalLinePhasor.XiChannel

/-- A xi zero whose analytic parameter is the projection shadow of a positive carrier height. -/
structure XiCarrierShadow where
  height : ℝ
  height_pos : 0 < height
  xi_zero : ZD.riemannXi (carrierPointAtHeight height) = 0

/-- The analytic parameter is produced by the geometric projection. -/
def XiCarrierShadow.analyticParameter (shadow : XiCarrierShadow) : ℂ :=
  carrierPointAtHeight shadow.height

@[simp] theorem XiCarrierShadow.analyticParameter_re (shadow : XiCarrierShadow) :
    shadow.analyticParameter.re = 1 / 2 := by
  rw [XiCarrierShadow.analyticParameter, carrierPointAtHeight_re, carrierAbscissa_eq_half]

theorem XiCarrierShadow.noRadialDrift (shadow : XiCarrierShadow) (n : ℝ) :
    n ^ (shadow.analyticParameter.re - carrierAbscissa) = 1 := by
  rw [shadow.analyticParameter_re, carrierAbscissa_eq_half, sub_self, Real.rpow_zero]

/-- The radial-drift operator on geometry-produced xi shadows. -/
noncomputable def xiCarrierShadowRadialDriftOperator :
    (XiCarrierShadow →₀ ℂ) →ₗ[ℂ] (XiCarrierShadow →₀ ℂ) :=
  UnconditionalFrobenius.diagOp fun shadow => shadow.analyticParameter.re - 1 / 2

/-- Geometry fixes the projection shadow, so its radial-drift operator vanishes. -/
theorem xiCarrierShadowRadialDriftOperator_eq_zero :
    xiCarrierShadowRadialDriftOperator = 0 := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro shadow
  simp [xiCarrierShadowRadialDriftOperator, UnconditionalFrobenius.diagOp_apply]

/-- A geometry-produced shadow is an ordinary analytic zero index. -/
def XiCarrierShadow.toXiZeroIndex (shadow : XiCarrierShadow) : XiZeroIndex :=
  ⟨shadow.analyticParameter, (ZD.riemannXi_eq_zero_iff shadow.analyticParameter).mp shadow.xi_zero⟩

@[simp] theorem XiCarrierShadow.toXiZeroIndex_re (shadow : XiCarrierShadow) :
    shadow.toXiZeroIndex.val.re = 1 / 2 := shadow.analyticParameter_re

end CriticalLinePhasor.ContourArgument

section AxiomAudit
#print axioms CriticalLinePhasor.ContourArgument.XiCarrierShadow.analyticParameter_re
#print axioms CriticalLinePhasor.ContourArgument.XiCarrierShadow.noRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.xiCarrierShadowRadialDriftOperator_eq_zero
#print axioms CriticalLinePhasor.ContourArgument.XiCarrierShadow.toXiZeroIndex_re
end AxiomAudit
