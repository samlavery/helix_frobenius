import RequestProject.HarmonizedCellTelescoping
import RequestProject.ZetaContourGlobalIdentification3D
import RequestProject.ZetaContourXiReceiverIdentification3D
import RequestProject.ZetaZeroNative3DSourceTransfer

/-!
# The ledger assembly: every face of the S(t) identification, one residual Prop

The assembly hub of the S(t) thread.  The single residual proposition of the thread is
named once — `IntegratedDefectSublinear`, sublinearity of the running integral of the
off-line defect ledger — and every compiled face of the identification is proven
equivalent to it: the good-height coordinate identity, parameter-preserving kernel
coupling of every upper zero, the no-radial-drift equation, the complete native 3D
certificate, and off-real regularity of the ξ-channel receiver.  Any one face proven
= all faces proven = every zero rides the carrier.

**Search record for the residual (per the prove-absence rule).**  The residual cannot
be discharged from census bounds: the compiled regime dichotomy
(`identification_or_linear_defect`) shows one off-carrier zero costs the integral
linearly regardless of any pointwise census control, so even the beyond-classical
lower Jensen target of `CarrierJensen.lean` (`N_off(t) ≤ C·log t`) would not close
it.  `CarrierJensen.lean` types the two-sided ledger bound and registers its lower
side as "quantitative zero-set exhaustion, far beyond classical knowledge";
`SpectralExhaustion.lean` isolates unrestricted spectral exhaustion as its own named
input; `HingeKernel.lean` records the per-cell crossing rate as
measured ("no zero-location claims").  Littlewood's classical bound stays cited, not
formalized (per direction, 2026-07-31).

Proven in this file: every equivalence, unconditionally — composition of the
compiled criterion (`IntegratedRegistrationReduction`) with the compiled equivalence
web (`ZetaContourGlobalIdentification3D`, `ZetaContourXiReceiverIdentification3D`).
-/

open Complex MeasureTheory Filter Asymptotics Topology

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor
open CriticalLinePhasor.ResidueJump
open CriticalLinePhasor.SpectralCarrierCoupling
open CriticalLinePhasor.ThreeDFocal

/-- **The single residual proposition of the S(t) thread**: the running integral of the
off-line defect ledger is sublinear.  By the compiled regime dichotomy this is
equivalent to the defect vanishing identically; by the hub theorems below it is
equivalent to every compiled face of the global identification. -/
abbrev IntegratedDefectSublinear : Prop :=
  (fun T => ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ))
    =o[atTop] fun T : ℝ => T

/-- Face 0: the good-height coordinate identity. -/
theorem integratedDefectSublinear_iff_globalCoordinateIdentification :
    IntegratedDefectSublinear ↔
      ∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T :=
  globalCoordinateIdentification_iff_integral_sublinear.symm

/-- Face 1: parameter-preserving kernel coupling of every upper zero. -/
theorem integratedDefectSublinear_iff_upperKernelCoupling
    (χ₁ : DirichletCharacter ℂ 1) :
    IntegratedDefectSublinear ↔
      ∀ ρ ∈ ZD.NontrivialZeros, 0 < ρ.im →
        Nonempty (SpectralCarrierKernelCoupling3D χ₁ 1 1 ρ) :=
  integratedDefectSublinear_iff_globalCoordinateIdentification.trans
    (globalCoordinateIdentification_iff_upperKernelCoupling χ₁)

/-- Face 2: the no-radial-drift equation at every upper zero. -/
theorem integratedDefectSublinear_iff_upperNoRadialDrift
    (χ₁ : DirichletCharacter ℂ 1) (n : ℝ) (hn : 1 < n) :
    IntegratedDefectSublinear ↔
      ∀ ρ ∈ ZD.NontrivialZeros, 0 < ρ.im →
        n ^ (ρ.re - carrierAbscissa) = 1 :=
  integratedDefectSublinear_iff_globalCoordinateIdentification.trans
    (globalCoordinateIdentification_iff_upperNoRadialDrift χ₁ n hn)

/-- Face 3: the complete native 3D certificate at every upper zero. -/
theorem integratedDefectSublinear_iff_upperNative3DCertificate
    (χ₁ : DirichletCharacter ℂ 1) :
    IntegratedDefectSublinear ↔
      ∀ ρ ∈ ZD.NontrivialZeros, 0 < ρ.im →
        Nonempty (PrincipalContourNative3DCertificate χ₁ ρ) :=
  integratedDefectSublinear_iff_globalCoordinateIdentification.trans
    (globalCoordinateIdentification_iff_upperNative3DCertificate χ₁)

/-- Face 4: off-real regularity of the ξ-channel receiver. -/
theorem integratedDefectSublinear_iff_xiChannel_offReal_regular
    (χ₁ : DirichletCharacter ℂ 1) :
    IntegratedDefectSublinear ↔
      ∀ z : ℂ, z.im ≠ 0 →
        ∃ L, Tendsto CriticalLinePhasor.XiChannel.xiChannel (𝓝[≠] z) (𝓝 L) :=
  integratedDefectSublinear_iff_globalCoordinateIdentification.trans
    (globalCoordinateIdentification_iff_xiChannel_offReal_regular χ₁)

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.integratedDefectSublinear_iff_globalCoordinateIdentification
#print axioms CriticalLinePhasor.ContourArgument.integratedDefectSublinear_iff_upperKernelCoupling
#print axioms CriticalLinePhasor.ContourArgument.integratedDefectSublinear_iff_upperNoRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.integratedDefectSublinear_iff_upperNative3DCertificate
#print axioms CriticalLinePhasor.ContourArgument.integratedDefectSublinear_iff_xiChannel_offReal_regular
