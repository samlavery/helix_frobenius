import RequestProject.ZetaContourCouplingDefect3D
import RequestProject.HelixSource

/-!
# Globalization of the contour/carrier identification

The finite-window defect theorem is promoted here to every upper nontrivial zero.  The result is
stated in three equivalent, independently useful languages:

* every good-height contour coordinate agrees with the native carrier coordinate;
* every upper analytic zero has a parameter-preserving full-kernel/3D coupling;
* every upper analytic zero obeys the area-law no-radial-drift equation.

The last statement contains no numerical midpoint.  The half-unit is recovered only inside the
compiled coupling constructor through `noRadialDrift_iff_carrierAbscissa` and the area law.
-/

open Complex

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor
open CriticalLinePhasor.ResidueJump
open CriticalLinePhasor.SpectralCarrierCoupling
open CriticalLinePhasor.ThreeDFocal

/-- The analytic coordinate of a conservative source mode, based at the area-law-selected carrier
abscissa.  Unlike the legacy source coordinate, this definition contains no literal half-unit. -/
noncomputable def conservativeCarrierCoord (ψ : HelixSource.SourceMode) : ℂ :=
  (carrierAbscissa : ℂ) + ψ.rate

/-- Conservation forces the real coordinate of a source mode to be exactly the area-law carrier
abscissa. -/
theorem conservativeCarrierCoord_re (ψ : HelixSource.SourceMode) :
    (conservativeCarrierCoord ψ).re = carrierAbscissa := by
  simp [conservativeCarrierCoord, ψ.noDrift]

/-- A conservative source has zero radial drift at every base greater than one. -/
theorem conservativeCarrierCoord_noRadialDrift
    (ψ : HelixSource.SourceMode) (n : ℝ) (hn : 1 < n) :
    n ^ ((conservativeCarrierCoord ψ).re - carrierAbscissa) = 1 :=
  (noRadialDrift_iff_carrierAbscissa n (conservativeCarrierCoord ψ).re hn).2
    (conservativeCarrierCoord_re ψ)

/-- Direct midpoint-free construction of the complete native 3D certificate from analytic
vanishing and no radial drift.  The numerical half-unit is produced only after the area-law
carrier abscissa has been derived. -/
noncomputable def principalContourNative3DCertificate_of_noRadialDrift
    (χ₁ : DirichletCharacter ℂ 1) {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros)
    (n : ℝ) (hn : 1 < n) (hnoDrift : n ^ (ρ.re - carrierAbscissa) = 1) :
    PrincipalContourNative3DCertificate χ₁ ρ := by
  have hre : ρ.re = carrierAbscissa :=
    (noRadialDrift_iff_carrierAbscissa n ρ.re hn).1 hnoDrift
  have hline : ρ.re = 1 / 2 := by
    simpa only [carrierAbscissa_eq_half] using hre
  exact principalContourNative3DCertificate_of_nontrivialZero_on_line χ₁ hρ hline

/-- Direct source-to-certificate landing.  A conservative carrier source representing an analytic
zero produces the entire physical-height 3D/operator certificate. -/
noncomputable def principalContourNative3DCertificate_of_conservativeSource
    (χ₁ : DirichletCharacter ℂ 1) {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros)
    (ψ : HelixSource.SourceMode) (hρψ : ρ = conservativeCarrierCoord ψ) :
    PrincipalContourNative3DCertificate χ₁ ρ := by
  apply principalContourNative3DCertificate_of_noRadialDrift χ₁ hρ 2 (by norm_num)
  rw [hρψ]
  exact conservativeCarrierCoord_noRadialDrift ψ 2 (by norm_num)

/-- Global coordinate identification is exactly full parameter-preserving 3D coupling for every
upper nontrivial analytic zero. -/
theorem globalCoordinateIdentification_iff_upperKernelCoupling
    (χ₁ : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      ∀ ρ ∈ ZD.NontrivialZeros, 0 < ρ.im →
        Nonempty (SpectralCarrierKernelCoupling3D χ₁ 1 1 ρ) := by
  constructor
  · intro hglobal ρ hρ hρim
    rcases upper_nontrivialZero_kernelCoupling_or_globalCoordinateDefect χ₁ hρ hρim with
      hcoupling | ⟨T, hT, _hρT, hdefect⟩
    · exact hcoupling
    · exact False.elim (hdefect (hglobal T hT))
  · intro hall T hT
    apply (classicalSContour_eq_Smult_iff_everyKernelCoupled χ₁ hT).2
    intro ρ hρstrip
    have hstrip := (stripZeroWindow_finite T).mem_toFinset.mp hρstrip
    exact hall ρ hstrip.1 hstrip.2.1

/-- Independent no-drift globalization.  Every good-height coordinate agrees exactly when every
upper analytic zero has unit radial projection at any chosen base `n > 1`. -/
theorem globalCoordinateIdentification_iff_upperNoRadialDrift
    (χ₁ : DirichletCharacter ℂ 1) (n : ℝ) (hn : 1 < n) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      ∀ ρ ∈ ZD.NontrivialZeros, 0 < ρ.im →
        n ^ (ρ.re - carrierAbscissa) = 1 := by
  constructor
  · intro hglobal ρ hρ hρim
    obtain ⟨T, hρT, hT⟩ := exists_goodHeight_gt ρ.im
    have hρstrip : ρ ∈ stripZeroFinset T := by
      apply (stripZeroWindow_finite T).mem_toFinset.mpr
      exact ⟨hρ, hρim, hρT.le⟩
    exact ((classicalSContour_eq_Smult_iff_everyKernelNoRadialDrift χ₁ hT hn).1
      (hglobal T hT)) ρ hρstrip
  · intro hall T hT
    apply (classicalSContour_eq_Smult_iff_everyKernelNoRadialDrift χ₁ hT hn).2
    intro ρ hρstrip
    have hstrip := (stripZeroWindow_finite T).mem_toFinset.mp hρstrip
    exact hall ρ hstrip.1 hstrip.2.1

/-- The global coordinate equality is also exactly the existence of the complete native 3D
certificate for every upper zero: physical height, focal event, ambient eigenvector, harmonic
rank drops, twin trace, analytic multiplicity, and the full analytic-kernel coupling. -/
theorem globalCoordinateIdentification_iff_upperNative3DCertificate
    (χ₁ : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      ∀ ρ ∈ ZD.NontrivialZeros, 0 < ρ.im →
        Nonempty (PrincipalContourNative3DCertificate χ₁ ρ) := by
  constructor
  · intro hglobal ρ hρ hρim
    rcases upper_nontrivialZero_native3DCertificate_or_globalCoordinateDefect χ₁ hρ hρim with
      hcertificate | ⟨T, hT, _hρT, hdefect⟩
    · exact hcertificate
    · exact False.elim (hdefect (hglobal T hT))
  · intro hall T hT
    apply (classicalSContour_eq_Smult_iff_everyKernelCoupled χ₁ hT).2
    intro ρ hρstrip
    have hstrip := (stripZeroWindow_finite T).mem_toFinset.mp hρstrip
    obtain ⟨C⟩ := hall ρ hstrip.1 hstrip.2.1
    exact ⟨C.kernelCoupling⟩

/-- Source-mode form of the global identification.  Coordinate equality at every good height is
equivalent to every upper analytic zero being the coordinate of a conservative mode based at the
area-law carrier.  Conservation, not a supplied midpoint equality, fixes the real coordinate. -/
theorem globalCoordinateIdentification_iff_upperConservativeSource
    (χ₁ : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      ∀ ρ ∈ ZD.NontrivialZeros, 0 < ρ.im →
        ∃ ψ : HelixSource.SourceMode, ρ = conservativeCarrierCoord ψ := by
  rw [globalCoordinateIdentification_iff_upperNoRadialDrift χ₁ 2 (by norm_num)]
  constructor
  · intro hall ρ hρ hρim
    have hre : ρ.re = carrierAbscissa :=
      (noRadialDrift_iff_carrierAbscissa 2 ρ.re (by norm_num)).1 (hall ρ hρ hρim)
    refine ⟨HelixSource.SourceMode.ofReal ρ.im, ?_⟩
    apply Complex.ext
    · simpa [conservativeCarrierCoord] using hre
    · simp [conservativeCarrierCoord, HelixSource.SourceMode.ofReal]
  · intro hall ρ hρ hρim
    obtain ⟨ψ, hρψ⟩ := hall ρ hρ hρim
    rw [hρψ]
    exact conservativeCarrierCoord_noRadialDrift ψ 2 (by norm_num)

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_upperKernelCoupling
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_upperNoRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_upperNative3DCertificate
#print axioms CriticalLinePhasor.ContourArgument.conservativeCarrierCoord_re
#print axioms CriticalLinePhasor.ContourArgument.conservativeCarrierCoord_noRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.principalContourNative3DCertificate_of_noRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.principalContourNative3DCertificate_of_conservativeSource
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_upperConservativeSource
