import RequestProject.DVPCarrierContinuation

/-!
# A construction-native harmonic that vanishes off the axis: the η-rail's lane points (ledger 1333)

Sam (2026-10-14): "vanishing can only flip the sign on the real axis, the fiber is also a harmonic — make sense?
… prove it." The claim to prove is the control: a bank built by the construction's own rules — sites `n + 1`,
phasors `(n+1)^{−s}`, alternating signs, summed IN ORDER as the sites enter (`etaPartial`, `etaLim`, 513–515) —
cancels at points OFF the axis, so "being a harmonic of this construction" does not by itself force the axis.

* `lanePoint k = 1 + 2πik/log 2`, real part `1`, not on the axis (`lanePoint_re`, `lanePoint_not_on_axis`).
* `two_cpow_one_sub_lanePoint`: `2^{1 − lanePoint k} = 1`.
* `etaLim_lanePoint`: the ordered readout `etaLim` vanishes at every lane point `k ≠ 0`
  (via `etaLim_eq_zeta`: `etaLim s = (1 − 2^{1−s})ζ(s)` on `Re s > 0`, `s ≠ 1`).
* `etaPartial_tendsto_lanePoint`: the ordered partial sums themselves converge to `0` there — a genuine ordered
  cancellation of the bank at tilt `δ = ½` (`etaPartial_tendsto`, 513).

Reading: the η-rail is real on its own axis and vanishes there only by flipping; its tilted reading vanishes at the
lane points without any flip. For ζ's bank the leaf says this never happens; the reason must be the Euler product's
structure across the primes (the lane factor `1 − 2^{1−s}` is the prime 2 alone), not the ordered summation.
No `sorry`, no `axiom`, no window.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.HelixEtaRailOffAxis

open CriticalLinePhasor.DVP

/-- The lane points of the η-rail: `1 + 2πik/log 2`. -/
def lanePoint (k : ℤ) : ℂ := 1 + ((2 * Real.pi * k / Real.log 2 : ℝ) : ℂ) * Complex.I

theorem lanePoint_re (k : ℤ) : (lanePoint k).re = 1 := by
  simp only [lanePoint, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem lanePoint_im (k : ℤ) : (lanePoint k).im = 2 * Real.pi * k / Real.log 2 := by
  simp only [lanePoint, Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The lane points are not on the axis. -/
theorem lanePoint_not_on_axis (k : ℤ) : (lanePoint k).re ≠ 1 / 2 := by
  rw [lanePoint_re]; norm_num

theorem log_two_ne_zero : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'

/-- `lanePoint k ≠ 1` for `k ≠ 0`: its height is `2πk/log 2 ≠ 0`. -/
theorem lanePoint_ne_one {k : ℤ} (hk : k ≠ 0) : lanePoint k ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  rw [lanePoint_im, Complex.one_im] at him
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have : 2 * Real.pi * (k : ℝ) / Real.log 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hk') log_two_ne_zero
  exact this him

/-- **The lane factor closes**: `2^{1 − lanePoint k} = 1`. -/
theorem two_cpow_one_sub_lanePoint (k : ℤ) : (2 : ℂ) ^ ((1 : ℂ) - lanePoint k) = 1 := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  have hlog : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast
    rfl
  rw [hlog]
  have harg : ((Real.log 2 : ℝ) : ℂ) * ((1 : ℂ) - lanePoint k) = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    unfold lanePoint
    have hl : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast log_two_ne_zero
    push_cast
    field_simp
    ring
  rw [harg, Complex.exp_int_mul_two_pi_mul_I]

/-- **The ordered native bank vanishes at every lane point**: a construction-native harmonic cancelling off the axis. -/
theorem etaLim_lanePoint {k : ℤ} (hk : k ≠ 0) : etaLim (lanePoint k) = 0 := by
  rw [etaLim_eq_zeta (by rw [lanePoint_re]; norm_num) (lanePoint_ne_one hk), two_cpow_one_sub_lanePoint]
  ring

/-- The ordered partial sums converge to `0` at the lane point: the cancellation is an ordered one. -/
theorem etaPartial_tendsto_lanePoint {k : ℤ} (hk : k ≠ 0) :
    Tendsto (etaPartial (lanePoint k)) atTop (𝓝 0) := by
  have h := etaPartial_tendsto (s := lanePoint k) (by rw [lanePoint_re]; norm_num)
  have hz : (∑' j : ℕ, pairTerm (lanePoint k) j) = 0 := etaLim_lanePoint hk
  rwa [hz] at h

end CriticalLinePhasor.HelixEtaRailOffAxis

end

#print axioms CriticalLinePhasor.HelixEtaRailOffAxis.etaLim_lanePoint
#print axioms CriticalLinePhasor.HelixEtaRailOffAxis.etaPartial_tendsto_lanePoint
#print axioms CriticalLinePhasor.HelixEtaRailOffAxis.lanePoint_not_on_axis
