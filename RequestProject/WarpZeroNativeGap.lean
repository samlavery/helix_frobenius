import RequestProject.FiberIsTheFunction
import RequestProject.NoDriftFreeExponent

/-!
# The Euler/warp zero equivalence against the native no-drift fiber (ledger 1182)

The compiled cancellation representation of ζ zeros (`CarrierReadout.zeta_zero_iff_bankΔ_mem_ker`):
in the strip, `ζ(s) = 0 ⟺ bankΔ Δ s ∈ ker(lane chart)`, where `bankΔ Δ s n = (Δ(n+1))^{−s}` is the
warp `e^{−sH_Δ}𝟙` at complex time `s` (`bankΔ_eq_exp`). Its real part is a real warp time acting on
the amplitude.

* `bankΔ_norm`: the bank's amplitude at site `n + 1` is `(Δ(n+1))^{−Re s}`.
* `bankΔ_eq_iff`: the bank at `s` is the bank at `σ + i·Im s` exactly when `Re s = σ`. The first
  point where a zero's bank and another bank at the same height differ is the amplitude.
* `zeroBank_native_iff`: the bank at `s` equals a native (no-drift) bank at the same height
  exactly when `NativeNoDrift (Re s)`; `zeroBank_native_iff_half`: exactly when `Re s = ½`
  (the area law).

So the compiled representation's cancellation is the warp at the zero's own real time `Re s`; it is
literally the native no-drift cancellation only when that real time is the constructed one. The
missing theorem is stated in ledger 1182.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.WarpZeroGap

open CarrierReadout CriticalLinePhasor.NoDriftFree

/-- **The bank's amplitude at site `n + 1` is `(Δ(n+1))^{−Re s}`.** -/
theorem bankΔ_norm {Δ : ℝ} (hΔ : 0 < Δ) (s : ℂ) (n : ℕ) :
    ‖bankΔ Δ s n‖ = (Δ * ((n : ℝ) + 1)) ^ (-s.re) := by
  unfold bankΔ
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]

/-- **A zero's bank and the bank at the same height with real time `σ` agree exactly when
`Re s = σ`.** -/
theorem bankΔ_eq_iff {Δ : ℝ} (hΔ : 0 < Δ) (s : ℂ) (σ : ℝ) :
    bankΔ Δ s = bankΔ Δ ((σ : ℂ) + (s.im : ℂ) * I) ↔ s.re = σ := by
  constructor
  · intro h
    have hre : ((σ : ℂ) + (s.im : ℂ) * I).re = σ := by simp
    have h0 := congrArg (fun f => ‖f 0‖) h
    have h1 := congrArg (fun f => ‖f 1‖) h
    simp only [bankΔ_norm hΔ, hre] at h0 h1
    norm_num at h0 h1
    have hΔ2 : 0 < Δ * 2 := by positivity
    have l0 := congrArg Real.log h0
    have l1 := congrArg Real.log h1
    rw [Real.log_rpow hΔ, Real.log_rpow hΔ] at l0
    rw [Real.log_rpow hΔ2, Real.log_rpow hΔ2, Real.log_mul hΔ.ne' two_ne_zero] at l1
    have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    have key : (-s.re) * Real.log 2 = (-σ) * Real.log 2 := by linarith
    have := mul_right_cancel₀ hl2 key
    linarith
  · intro h
    rw [← h, Complex.re_add_im]

/-- **The zero's bank is a native no-drift bank at its height exactly when its real time has no
drift.** -/
theorem zeroBank_native_iff {Δ : ℝ} (hΔ : 0 < Δ) (s : ℂ) :
    (∃ σ : ℝ, NativeNoDrift σ ∧ bankΔ Δ s = bankΔ Δ ((σ : ℂ) + (s.im : ℂ) * I)) ↔
      NativeNoDrift s.re := by
  constructor
  · rintro ⟨σ, hσ, h⟩
    rw [(bankΔ_eq_iff hΔ s σ).1 h]
    exact hσ
  · intro h
    exact ⟨s.re, h, (bankΔ_eq_iff hΔ s s.re).2 rfl⟩

/-- With the area law. -/
theorem zeroBank_native_iff_half {Δ : ℝ} (hΔ : 0 < Δ) (s : ℂ) :
    (∃ σ : ℝ, NativeNoDrift σ ∧ bankΔ Δ s = bankΔ Δ ((σ : ℂ) + (s.im : ℂ) * I)) ↔ s.re = 1 / 2 := by
  rw [zeroBank_native_iff hΔ, nativeNoDrift_iff_half]

end CriticalLinePhasor.WarpZeroGap

#scan_abscissa CriticalLinePhasor.WarpZeroGap.bankΔ_eq_iff
  CriticalLinePhasor.WarpZeroGap.zeroBank_native_iff
  CriticalLinePhasor.WarpZeroGap.zeroBank_native_iff_half
  CarrierReadout.zeta_zero_iff_bankΔ_mem_ker
  CarrierReadout.fiber_eq_function

#print axioms CriticalLinePhasor.WarpZeroGap.bankΔ_norm
#print axioms CriticalLinePhasor.WarpZeroGap.bankΔ_eq_iff
#print axioms CriticalLinePhasor.WarpZeroGap.zeroBank_native_iff
#print axioms CriticalLinePhasor.WarpZeroGap.zeroBank_native_iff_half
