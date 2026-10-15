import RequestProject.HelixWrittenZeros
import RequestProject.FiberIsTheFunction

/-!
# The full fiber's vanishing and the two-ended focal event (ledger 1267)

A trace between two existing objects; nothing new is constructed.
* The full 3D fiber `laneChart3D σ y` (`CarrierReadout.fiber3D_eq_function`): the planar sum of the 3D phasors at
  `(σ, y)`. It reads `(1 − 2^{1−s})ζ(s)` with `s = σ + iy`.
* The two-ended focal event at physical height `Z` (`HelixTwoEndedCancellation.twoEnded_cancels_iff`) and what the
  construction writes (`HelixWrittenZeros.Written`).

Results:
* `fiber_vanishes_iff`: in the strip, the full fiber vanishes at `(σ, y)` exactly when `ζ(σ + iy) = 0`.
* `fiber_on_line_iff_event`: on the line the two **vanishing conditions** agree. The full fiber vanishes at `(½, y)`
  exactly when the two-ended configuration at height `Z = e^y` cancels, at every cut.
* `written_of_fiber_vanishing_iff`: a vanishing of the full fiber in the strip is written by the two-ended
  construction exactly when it lies on the line.

Scope (ledger 1268). These equivalences are readout-level: both sides are reduced to `ζ = 0`. The full fiber goes
through `DVP.etaLim_eq_zeta`; the two-ended configuration goes through Mathlib's `completedRiemannZeta`. They do not
identify the two 3D events.
* The two objects are built differently. `laneChart3D` sums Dirichlet phasors whose amplitude `n^{-σ}` carries `σ`
  as a free parameter. The two-ended configuration integrates the Gaussian bank above a cut at the fixed centre
  `k/2`.
* They cancel different partitions: odd against even sites, versus the bank above the cut against the J-image of
  the bank above the reflected cut.
* A mode-by-mode Mellin map between the two banks is compiled only for `Re s > 1` (`LatticeSelfDualJ.latticeSeries`)
  and for finite heads (`HelixWindowCompletion.head_two_ended`).
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.HelixFiberEventTrace

open CriticalLinePhasor CarrierReadout CriticalLinePhasor.HelixTwoEndedCancellation
  CriticalLinePhasor.HelixWrittenZeros

/-- In the strip, the full fiber vanishes at `(σ, y)` exactly when `ζ(σ + iy) = 0`. -/
theorem fiber_vanishes_iff {σ y : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    laneChart3D σ y = 0 ↔ riemannZeta ((σ : ℂ) + y * I) = 0 := by
  set s : ℂ := (σ : ℂ) + y * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre, Complex.one_re] at this
    linarith
  have h := fiber3D_eq_function 1 one_pos σ y hσ0 hs1
  unfold CarrierParity.carrierFiber at h
  rw [Complex.ofReal_one, Complex.one_cpow, one_mul, one_mul] at h
  have hfac : (1 : ℂ) - (2 : ℂ) ^ (1 - s) ≠ 0 := by
    intro h0
    have h2 : ((2 : ℝ) : ℂ) ^ (1 - s) = 1 := by
      push_cast
      linear_combination -h0
    have hn := congrArg norm h2
    rw [Complex.norm_cpow_eq_rpow_re_of_pos two_pos, norm_one, Complex.sub_re, Complex.one_re, hsre] at hn
    have : (1 : ℝ) < 2 ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith)
    linarith
  rw [h]
  constructor
  · intro h0
    exact (mul_eq_zero.mp h0).resolve_left hfac
  · intro h0
    rw [h0, mul_zero]

/-- **On the line, the full fiber's vanishing condition and the two-ended configuration's cancellation agree**, at
every cut. Both sides reduce to `ζ(½ + iy) = 0`; this is not an identification of the two 3D events. -/
theorem fiber_on_line_iff_event (y hc : ℝ) :
    laneChart3D (1 / 2) y = 0 ↔ (twoEndedConfig (Real.exp y) hc).Cancels := by
  rw [fiber_vanishes_iff (by norm_num) (by norm_num), twoEnded_cancels_iff, Real.log_exp]
  have : (((1 / 2 : ℝ)) : ℂ) = 1 / 2 := by push_cast; ring
  rw [this]

/-- **A vanishing of the full fiber in the strip is written by the two-ended construction exactly when it lies on
the line.** -/
theorem written_of_fiber_vanishing_iff {σ y : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (h : laneChart3D σ y = 0) :
    Written ((σ : ℂ) + y * I) ↔ σ = 1 / 2 := by
  rw [written_iff, (fiber_vanishes_iff hσ0 hσ1).mp h]
  simp

end CriticalLinePhasor.HelixFiberEventTrace

end

#print axioms CriticalLinePhasor.HelixFiberEventTrace.fiber_vanishes_iff
#print axioms CriticalLinePhasor.HelixFiberEventTrace.fiber_on_line_iff_event
#print axioms CriticalLinePhasor.HelixFiberEventTrace.written_of_fiber_vanishing_iff
