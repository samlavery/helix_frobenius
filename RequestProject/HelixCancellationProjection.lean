import RequestProject.HelixFootMass
import RequestProject.FocalLineGate
import RequestProject.GlobalHelixIntertwiner
import RequestProject.EventProjection

/-!
# The two-ended cancellation, carried through the existing projection (ledger 1263)

Trace of `HelixTwoEndedCancellation` (1261–1262) through the two compiled projection systems, using existing
declarations. Physical height `Z`; analytic coordinates only at the last step.

**The chain.** The configuration `twoEndedConfig Z hc` (two feet at height `Z`) cancels; then
`twoEnded_channels_of_cancels` gives the standing mode `(0, M)` at `Z`, and `HelixFootMass.cancellationEigenstate`
the eigenstate `(M, Z)`. Its mass is positive at every cut and every height (`HelixFootMass.twoEnded_mass_pos`: the
bank's zero mode, booked at the cut, dominates its other modes), so the chain carries no hypothesis on `M`. Then:

**(A) The carrier projection** (`EventProjection`, `FocalLine.chartOf`). The eigenstate's chart point is the
carrier point at its height, `carrierPointAtHeight Z` (`eigenstate_chart`). Projection keeps `Z`; the dropped
radius and angle are functions of `Z` (`EventProjection.project_event`, `event_point_of_height`). The real part is
the carrier's balance exponent, derived first (`EventProjection.event_transverse_balanced`); its value `½` is
attached last. The chart point is blind to `M` (`FocalLine.chartOf_mass_blind`).
* `projection_commutes`: **the square commutes.** Native cancellation at height `Z` implies the projected chart
  point of the post-cancellation eigenstate is a zero of the analytic readout.
* `chart_zero_iff_cancels`: conversely, for every eigenstate, its projected chart point is a zero exactly when the
  two-ended configuration at its height cancels.
* `zero_on_chart_line_iff`: a point on the chart's line (`Re = carrierAbscissa`) is a zero exactly when the
  native configuration at height `e^{Im}` cancels. The projection's image of the native cancellations is
  exactly the set of zeros on that line.

**(B) The Cayley pipeline** (`GlobalHelixIntertwiner`). A foot is the 3D cone point
`footFiber F Z = (‖F‖, arg F, log Z)`.
* `foot_circleReadout`: its 2D Cayley readout is `cayley (log Z)`, a function of the height alone. So
  `feet_same_circle`: both feet project to the same point of the unit circle.
* `foot_stripReadout`: the full 3D → 2D → 1D chain gives `½ + i·log Z`.
* `cayley_chain_commutes`: native cancellation implies the chain's readout is a zero.
* J on the feet flips the phase at a fixed height (`FocalFeet.phasorFoot_conj`). `globalHelixInvolution` also
  flips the height. It is the double carrier's symmetry, not the feet pair.

**The missing implications.** The first one in the chain, cancellation → eigenstate, needed `M > 0`. It is proved
(`HelixFootMass`). Every arrow above now runs from a native cancellation to a zero on the chart's line, and back
again for points on that line. What is not established: that every zero of the analytic readout lies on the
projection's image (coverage). The compiled projection cannot supply it. Its chart point has the same
real part for every eigenstate by construction (`FocalLine.chartOf_re_const`), and it does not read the mass
(`FocalLine.chartOf_mass_blind`). This is a statement about the projection as defined, not about where zeros lie.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.HelixCancellationProjection

open CriticalLinePhasor CriticalLinePhasor.ThreeDFocal CriticalLinePhasor.FocalLine CriticalLinePhasor.FocalFeet
  CriticalLinePhasor.HelixTwoEndedCancellation CriticalLinePhasor.GlobalHelix ConeProjection

/-- The carrier point at physical height `Z`, written out at the readout: `½ + i·log Z`. -/
theorem carrierPointAtHeight_eq (Z : ℝ) : carrierPointAtHeight Z = 1 / 2 + (Real.log Z : ℂ) * I := by
  apply Complex.ext
  · rw [carrierPointAtHeight_re, carrierAbscissa_eq_half]
    simp
  · rw [carrierPointAtHeight_im]
    simp

/-! ## (A) The carrier projection -/

/-- The post-cancellation eigenstate projects to the carrier point at its height. -/
theorem eigenstate_chart (Z hc : ℝ) (hZ : 0 < Z) :
    chartOf (HelixFootMass.cancellationEigenstate Z hc hZ) = carrierPointAtHeight Z := rfl

/-- **The square commutes**: native cancellation ⟹ the projected chart point of the post-cancellation eigenstate
is an analytic zero. No hypothesis on the mass. -/
theorem projection_commutes {Z hc : ℝ} (hZ : 0 < Z) (h : (twoEndedConfig Z hc).Cancels) :
    riemannZeta (chartOf (HelixFootMass.cancellationEigenstate Z hc hZ)) = 0 := by
  rw [eigenstate_chart, carrierPointAtHeight_eq]
  exact (twoEnded_cancels_iff Z hc).mp h

/-- For every eigenstate, its projected chart point is a zero exactly when the two-ended configuration at its
height cancels. -/
theorem chart_zero_iff_cancels (d : FocalEigenstate) (hc : ℝ) :
    riemannZeta (chartOf d) = 0 ↔ (twoEndedConfig d.height hc).Cancels := by
  rw [chartOf, carrierPointAtHeight_eq, twoEnded_cancels_iff]

/-- A point on the chart's line is a zero exactly when the native configuration at height `e^{Im}` cancels. -/
theorem zero_on_chart_line_iff {s : ℂ} (hs : s.re = carrierAbscissa) (hc : ℝ) :
    riemannZeta s = 0 ↔ (twoEndedConfig (Real.exp s.im) hc).Cancels := by
  have hpt : s = carrierPointAtHeight (Real.exp s.im) := by
    apply Complex.ext
    · rw [carrierPointAtHeight_re, hs]
    · rw [carrierPointAtHeight_im, Real.log_exp]
  rw [twoEnded_cancels_iff, ← carrierPointAtHeight_eq, ← hpt]

/-! ## (B) The Cayley pipeline -/

/-- A foot as a 3D cone point: weight, direction, signed height `log Z`. -/
def footFiber (F : ℂ) (Z : ℝ) : Fiber := (‖F‖, Complex.arg F, Real.log Z)

/-- The 2D Cayley readout of a foot depends on its height alone. -/
theorem foot_circleReadout (F : ℂ) (Z : ℝ) :
    circleReadout (footFiber F Z) = Readout.cayley ((Real.log Z : ℝ) : ℂ) := rfl

/-- Both feet project to the same point of the unit circle. -/
theorem feet_same_circle (Z hc : ℝ) :
    circleReadout (footFiber (helixFoot Z hc) Z) = circleReadout (footFiber (antiHelixFoot Z hc) Z) :=
  (foot_circleReadout _ Z).trans (foot_circleReadout _ Z).symm

/-- The full 3D → 2D → 1D chain reads `½ + i·log Z`. -/
theorem foot_stripReadout (F : ℂ) (Z : ℝ) :
    stripReadout (footFiber F Z) = 1 / 2 + (Real.log Z : ℂ) * I := by
  rw [stripReadout, analyticOrdinate_eq_height]
  show (1 / 2 : ℂ) + I * ((Real.log Z : ℝ) : ℂ) = _
  ring

/-- **The Cayley chain commutes**: native cancellation ⟹ the chain's readout of the helix foot is a zero. -/
theorem cayley_chain_commutes {Z hc : ℝ} (h : (twoEndedConfig Z hc).Cancels) :
    riemannZeta (stripReadout (footFiber (helixFoot Z hc) Z)) = 0 := by
  rw [foot_stripReadout]
  exact (twoEnded_cancels_iff Z hc).mp h

end CriticalLinePhasor.HelixCancellationProjection

end

#print axioms CriticalLinePhasor.HelixCancellationProjection.projection_commutes
#print axioms CriticalLinePhasor.HelixCancellationProjection.chart_zero_iff_cancels
#print axioms CriticalLinePhasor.HelixCancellationProjection.zero_on_chart_line_iff
#print axioms CriticalLinePhasor.HelixCancellationProjection.feet_same_circle
#print axioms CriticalLinePhasor.HelixCancellationProjection.foot_stripReadout
#print axioms CriticalLinePhasor.HelixCancellationProjection.cayley_chain_commutes
