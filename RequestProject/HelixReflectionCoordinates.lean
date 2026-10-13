import RequestProject.GlobalHelixLogReadout
import RequestProject.FoliatedPolarization
import RequestProject.CompletedReflectionFiber

/-!
# Origin reflection and the single analytic readout translation

Native coordinates come first: `(r, theta, h)` is sent to `(r, -theta, -h)`.
The native signed midpoint is zero. `centeredReadout = i h` also negates.
Only `stripReadout = 1/2 + centeredReadout` adds a translation.

For a general analytic parameter s, put u = s - 1/2. The full reflection
`s -> 1-s` sends u to -u. The same-height reflection `s -> 1-conj(s)` sends
u to -conj(u). Both negate the real displacement, but they act differently
on height. In the rotated spectral coordinate t=-i u the latter is conjugation.

Proof decomposition A starts with `rw [centeredReadout_globalHelixInvolution_neg]`
and uses `neg_eq_self`. Independent decomposition B starts with
`apply Complex.ext` and checks real/imaginary components. Both are used below.
No statement here locates an analytic zero or changes a native involution.
-/

open Complex

namespace CriticalLinePhasor.GlobalHelix
open ConeProjection

/-- The native global fixed locus has zero phase and zero signed height; radius is retained. -/
theorem globalHelixInvolution_fixed_iff_zero (f : Fiber) :
    globalHelixInvolution f = f ↔ phase f = 0 ∧ height f = 0 := by
  rcases f with ⟨r, θ, h⟩
  simp [globalHelixInvolution, radial, phase, height, neg_eq_self]

/-- The fixed signed ordinate is zero, before the analytic readout translation. -/
theorem analyticOrdinate_fixed_iff_zero (f : Fiber) :
    analyticOrdinate (globalHelixInvolution f) = analyticOrdinate f ↔
      analyticOrdinate f = 0 := by
  rw [analyticOrdinate_globalHelixInvolution]
  exact neg_eq_self

/-- Reflection of the centered readout fixes precisely its origin. -/
theorem centeredReadout_fixed_iff_zero (f : Fiber) :
    centeredReadout (globalHelixInvolution f) = centeredReadout f ↔
      centeredReadout f = 0 := by
  rw [centeredReadout_globalHelixInvolution_neg]
  exact neg_eq_self

/-- The half-unit in the translated readout denotes the native centered origin. -/
theorem stripReadout_eq_half_iff_centered_zero (f : Fiber) :
    stripReadout f = (1 / 2 : ℂ) ↔ centeredReadout f = 0 := by
  rw [stripReadout_eq_half_add_centeredReadout]
  simp

/-- Applying an affine half-unit reflection to an already centered value is a different map. -/
theorem centeredReadout_neg_ne_one_sub (f : Fiber) :
    centeredReadout (globalHelixInvolution f) ≠ 1 - centeredReadout f := by
  rw [centeredReadout_globalHelixInvolution_neg]
  intro h
  have hzero : (0 : ℂ) = 1 := by linear_combination h
  exact zero_ne_one hzero

end CriticalLinePhasor.GlobalHelix

namespace CriticalLinePhasor.HelixReflectionCoordinates

/-- Center an analytic parameter once. This is a downstream chart conversion. -/
noncomputable def toCentered (s : ℂ) : ℂ := s - 1 / 2

/-- Translate a centered parameter once to the normalized analytic chart. -/
noncomputable def toStrip (u : ℂ) : ℂ := 1 / 2 + u

@[simp] theorem toCentered_toStrip (u : ℂ) : toCentered (toStrip u) = u := by
  simp [toCentered, toStrip]

@[simp] theorem toStrip_toCentered (s : ℂ) : toStrip (toCentered s) = s := by
  simp [toCentered, toStrip]

/-- The actual helix readout uses exactly one translation. -/
theorem toCentered_stripReadout (f : ConeProjection.Fiber) :
    toCentered (GlobalHelix.stripReadout f) = GlobalHelix.centeredReadout f := by
  rw [GlobalHelix.stripReadout_eq_half_add_centeredReadout]
  simp [toCentered]

/-- Full reflection in the analytic chart is origin reflection in the centered chart. -/
theorem toCentered_one_sub (s : ℂ) : toCentered (1 - s) = -toCentered s := by
  unfold toCentered
  ring

/-- Transport origin reflection forward without centering twice. -/
theorem toStrip_neg (u : ℂ) : toStrip (-u) = 1 - toStrip u := by
  unfold toStrip
  ring

/-- Same-height analytic reflection is negative conjugation in the centered chart. -/
theorem toCentered_feReflect (s : ℂ) :
    toCentered (FoliatedPolarization.feReflect s) =
      -(starRingEnd ℂ) (toCentered s) := by
  apply Complex.ext
  · simp [toCentered, FoliatedPolarization.feReflect]
    ring
  · simp [toCentered, FoliatedPolarization.feReflect]

/-- In the real transverse displacement both analytic reflections negate the displacement. -/
theorem transverse_reflection (σ : ℝ) : (1 - σ) - 1 / 2 = -(σ - 1 / 2) := by
  ring

/-- Centering leaves height unchanged. -/
@[simp] theorem toCentered_im (s : ℂ) : (toCentered s).im = s.im := by
  simp [toCentered]

/-- The real centered coordinate is the transverse displacement, not signed height. -/
@[simp] theorem toCentered_re (s : ℂ) : (toCentered s).re = s.re - 1 / 2 := by
  simp [toCentered]

/-- The existing spectral coordinate rotates the once-centered chart; it adds no translation. -/
theorem spectralCoord_eq_rotated_centered (s : ℂ) :
    FoliatedPolarization.spectralCoord s = -I * toCentered s := rfl

/-- The full reflection negates the rotated spectral parameter as well. -/
theorem spectralCoord_one_sub (s : ℂ) :
    FoliatedPolarization.spectralCoord (1 - s) = -FoliatedPolarization.spectralCoord s := by
  simp only [spectralCoord_eq_rotated_centered, toCentered_one_sub]
  ring

/-- The same-height reflection is conjugation, not negation, in the rotated coordinate. -/
theorem spectralCoord_sameHeight (s : ℂ) :
    FoliatedPolarization.spectralCoord (FoliatedPolarization.feReflect s) =
      (starRingEnd ℂ) (FoliatedPolarization.spectralCoord s) :=
  FoliatedPolarization.spectralCoord_feReflect s

/-- On the carrier image the same-height reflection fixes the readout at every height. -/
theorem sameHeight_fixes_stripReadout (f : ConeProjection.Fiber) :
    FoliatedPolarization.feReflect (GlobalHelix.stripReadout f) =
      GlobalHelix.stripReadout f := by
  apply Complex.ext <;>
    norm_num [FoliatedPolarization.feReflect, GlobalHelix.stripReadout,
      Complex.mul_re, Complex.mul_im]

/-- Recentring writes the existing paired-moment coefficient as 2 times centered displacement². -/
theorem paired_moment_coefficient_centered (s : ℂ) :
    2 * (s.re - 1 / 2) ^ 2 = 2 * (toCentered s).re ^ 2 := by
  rw [toCentered_re]

/-- The existing local reflecting variable is `c^u` after exactly one chart conversion. -/
theorem reflVar_toStrip (c u : ℂ) :
    FiniteWeightFiber.reflVar c (toStrip u) = c ^ u := by
  simp [FiniteWeightFiber.reflVar, toStrip]

/-- In centered coordinates the existing completion pairs the two arguments `u` and `-u`. -/
theorem clockCompletion_toStrip (α : ℂ) (ℓ : ℝ) (u : ℂ) :
    FiniteWeightFiber.clockCompletion α ℓ (toStrip u) =
      ChiralityHB.symClock α ℓ u * ChiralityHB.symClock α ℓ (-u) := by
  simp [FiniteWeightFiber.clockCompletion, toStrip]

/-- Origin reflection exchanges the two completion legs and preserves their product. -/
theorem clockCompletion_toStrip_neg (α : ℂ) (ℓ : ℝ) (u : ℂ) :
    FiniteWeightFiber.clockCompletion α ℓ (toStrip (-u)) =
      FiniteWeightFiber.clockCompletion α ℓ (toStrip u) := by
  rw [clockCompletion_toStrip, clockCompletion_toStrip, neg_neg, mul_comm]

end CriticalLinePhasor.HelixReflectionCoordinates

#print axioms CriticalLinePhasor.GlobalHelix.globalHelixInvolution_fixed_iff_zero
#print axioms CriticalLinePhasor.GlobalHelix.analyticOrdinate_fixed_iff_zero
#print axioms CriticalLinePhasor.GlobalHelix.centeredReadout_fixed_iff_zero
#print axioms CriticalLinePhasor.GlobalHelix.stripReadout_eq_half_iff_centered_zero
#print axioms CriticalLinePhasor.GlobalHelix.centeredReadout_neg_ne_one_sub
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.toCentered_toStrip
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.toStrip_toCentered
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.toCentered_stripReadout
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.toCentered_one_sub
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.toStrip_neg
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.toCentered_feReflect
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.transverse_reflection
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.toCentered_im
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.toCentered_re
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.spectralCoord_eq_rotated_centered
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.spectralCoord_one_sub
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.spectralCoord_sameHeight
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.sameHeight_fixes_stripReadout
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.paired_moment_coefficient_centered
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.reflVar_toStrip
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.clockCompletion_toStrip
#print axioms CriticalLinePhasor.HelixReflectionCoordinates.clockCompletion_toStrip_neg
