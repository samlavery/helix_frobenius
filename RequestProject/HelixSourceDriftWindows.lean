import RequestProject.HelixSourceEndSwap
import RequestProject.SeatingShell
import RequestProject.FiberZeroMidpointWindow

/-!
# Where the no-drift law for cancellations is already a theorem (ledger 1315)

The last clause of Sam's fact (1314) is: a drifted evaluation of the native feet does not cancel. Two regions of
it are compiled in the tree and are restated here in the event's vocabulary, so that the region that is not yet
a theorem is visible as a region, not as a slogan.

* `source_drift_zero_below`: for every zero with `|Im ρ| ≤ 1269/2`, the source's evaluation carries no drift
  (DVP station ladder, `DVP.online_below_1269o2`).
* `oneVanishing_source_below`: in that height window, at each height the sources of at most one abscissa cancel —
  the proposition of 1314, discharged there.
* `source_drift_edge_bound`: every zero with `|Im ρ| > 3` has its source's drift inside `¼ − A/(2 log⁹|Im ρ|)`
  (`SeatingLedger.offline_depth_bound`, from PNT+ `ZetaZeroFree`: the prime-site perfect squares, 1307–1308).
* `source_not_cancel_of_edge_drift`: a drifted evaluation with drift at least `¼ − A/(2 log⁹(2|Im v|))` does not
  cancel. `source_not_cancel_mirror`: the mirror statement from the end swap alone.

Remaining region of the clause: heights `|y| > 1269/2` and drifts `0 < |Re v| < ¼ − A/(2 log⁹|y|)`.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixSourceDriftWindows

open CriticalLinePhasor.HelixZetaSource CriticalLinePhasor.HelixSourceEndSwap CriticalLinePhasor.SeatingLedger
open FocalFeet

/-- **No drift in the certified height window.** -/
theorem source_drift_zero_below {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) (hy : |ρ.im| ≤ 1269 / 2) :
    (ρ / 2 - 1 / 4).re = 0 :=
  (source_on_axis_iff ρ).mpr (DVP.online_below_1269o2 ρ hρ hy)

/-- **One cancelling abscissa per height, in the certified window.** -/
theorem oneVanishing_source_below {y : ℝ} (hy : |y| ≤ 1269 / 2) {σ₁ σ₂ : ℝ}
    (h10 : 0 < σ₁) (h11 : σ₁ < 1) (h20 : 0 < σ₂) (h21 : σ₂ < 1)
    (c1 : (sourceConfig (((σ₁ : ℂ) + y * I) / 2 - 1 / 4) (Real.exp y) 0).Cancels)
    (c2 : (sourceConfig (((σ₂ : ℂ) + y * I) / 2 - 1 / 4) (Real.exp y) 0).Cancels) : σ₁ = σ₂ :=
  CarrierReadout.oneVanishingPerHeight3D_below hy h10 h11 h20 h21
    ((laneChart3D_zero_iff_source h10 h11 0).mpr c1) ((laneChart3D_zero_iff_source h20 h21 0).mpr c2)

/-- **The drift of every zero's source stays inside the arithmetic edge band.** -/
theorem source_drift_edge_bound :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1 / 2 ∧ ∀ ρ ∈ ZD.NontrivialZeros, 3 < |ρ.im| →
      |(ρ / 2 - 1 / 4).re| < 1 / 4 - A / (2 * (Real.log |ρ.im|) ^ 9) := by
  obtain ⟨A, hA0, hA1, h⟩ := offline_depth_bound
  refine ⟨A, hA0, hA1, fun ρ hρ ht => ?_⟩
  have := h ρ hρ ht
  rw [source_offset_re, abs_div, abs_two]
  have h2 : A / (2 * (Real.log |ρ.im|) ^ 9) = (A / (Real.log |ρ.im|) ^ 9) / 2 := by ring
  rw [h2]
  linarith

/-- **A drifted evaluation at the edge band does not cancel.** For `|Re v| < ¼` and `3/2 < |Im v|`: if the drift
is at least `¼ − A/(2 log⁹(2|Im v|))`, the source at `v` does not cancel. -/
theorem source_not_cancel_of_edge_drift :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1 / 2 ∧ ∀ (v : ℂ) (Z hc : ℝ), |v.re| < 1 / 4 → 3 / 2 < |v.im| →
      1 / 4 - A / (2 * (Real.log (2 * |v.im|)) ^ 9) ≤ |v.re| → ¬ (sourceConfig v Z hc).Cancels := by
  obtain ⟨A, hA0, hA1, h⟩ := source_drift_edge_bound
  refine ⟨A, hA0, hA1, fun v Z hc hv ht hdrift hcancel => ?_⟩
  have hζ : riemannZeta (1 / 2 + 2 * v) = 0 := (sourceConfig_cancels_iff hv Z hc).mp hcancel
  have hre : (1 / 2 + 2 * v : ℂ).re = 1 / 2 + 2 * v.re := by simp
  have him : (1 / 2 + 2 * v : ℂ).im = 2 * v.im := by simp
  have hv1 := (abs_lt.mp hv).1
  have hv2 := (abs_lt.mp hv).2
  have hρ : (1 / 2 + 2 * v : ℂ) ∈ ZD.NontrivialZeros :=
    ⟨by rw [hre]; linarith, by rw [hre]; linarith, hζ⟩
  have hρim : 3 < |(1 / 2 + 2 * v : ℂ).im| := by
    rw [him, abs_mul, abs_two]; linarith
  have hb := h _ hρ hρim
  have hoff : ((1 / 2 + 2 * v : ℂ) / 2 - 1 / 4).re = v.re := by
    simp; ring
  rw [hoff, him, abs_mul, abs_two] at hb
  linarith

/-- **The mirror band comes from the end swap**, not from the functional equation: if the source at `v` does not
cancel, neither does its J-partner. -/
theorem source_not_cancel_mirror {v : ℂ} {Z hc : ℝ} (h : ¬ (sourceConfig v Z hc).Cancels) :
    ¬ (sourceConfig (-conj v) Z (-hc)).Cancels :=
  fun hc' => h ((partnerSource_cancels_iff v Z hc).mp hc')

end CriticalLinePhasor.HelixSourceDriftWindows

end

#print axioms CriticalLinePhasor.HelixSourceDriftWindows.source_drift_zero_below
#print axioms CriticalLinePhasor.HelixSourceDriftWindows.oneVanishing_source_below
#print axioms CriticalLinePhasor.HelixSourceDriftWindows.source_drift_edge_bound
#print axioms CriticalLinePhasor.HelixSourceDriftWindows.source_not_cancel_of_edge_drift
#print axioms CriticalLinePhasor.HelixSourceDriftWindows.source_not_cancel_mirror
