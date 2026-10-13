import RequestProject.WarpZeroNativeGap
import RequestProject.DVPLadder1269o2

/-!
# The missing theorem of ledger 1182, on the verified window (ledger 1184)

Ledger 1182 stated the missing theorem: a lane-chart cancellation of the warped bank at `s`
(`0 < Re s < 1`) has native no drift at its real time, `NativeNoDrift (Re s)`. With
`zeta_zero_iff_bankΔ_mem_ker` and `zeroBank_native_iff_half` it is equivalent to `Re s = ½` for
every zero in the strip.

`laneChart_cancellation_is_native_window` proves it for `|Im s| ≤ 1269/2`, unconditionally. The input
is the house's verified window `DVP.online_below_1269o2` (Hardy-function sign changes plus the
argument-principle census, ledger 931), not a native mechanism. Above the window it is not proved.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.WarpZeroGap

open CarrierReadout CriticalLinePhasor.NoDriftFree

/-- **On the verified window, a lane-chart cancellation on the warp orbit occurs only at the
no-drift real time.** -/
theorem laneChart_cancellation_is_native_window {Δ : ℝ} (hΔ : 0 < Δ) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1) (hwin : |s.im| ≤ 1269 / 2) (hker : laneChart (bankΔ Δ s) = 0) :
    NativeNoDrift s.re := by
  have hz : riemannZeta s = 0 := (zeta_zero_iff_bankΔ_mem_ker Δ hΔ hs0 hs1).2 hker
  exact (nativeNoDrift_iff_half _).2 (DVP.online_below_1269o2 s ⟨hs0, hs1, hz⟩ hwin)

/-- The same, read as the transport of 1183: on the window, the zero's bank IS a native bank at its
height. -/
theorem zeroBank_is_native_window {Δ : ℝ} (hΔ : 0 < Δ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hwin : |s.im| ≤ 1269 / 2) (hker : laneChart (bankΔ Δ s) = 0) :
    ∃ σ : ℝ, NativeNoDrift σ ∧ bankΔ Δ s = bankΔ Δ ((σ : ℂ) + (s.im : ℂ) * I) :=
  (zeroBank_native_iff hΔ s).2 (laneChart_cancellation_is_native_window hΔ hs0 hs1 hwin hker)

end CriticalLinePhasor.WarpZeroGap

#print axioms CriticalLinePhasor.WarpZeroGap.laneChart_cancellation_is_native_window
#print axioms CriticalLinePhasor.WarpZeroGap.zeroBank_is_native_window
