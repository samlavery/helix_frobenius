import RequestProject.SelfAdjointGeneratorReadout
import RequestProject.ClosedForm

/-!
# Spectral cancellation always includes a sign flip, and sign flips only happen on the real axis

This file records, **unconditionally** (no GRH, no RH), two facts about the *signed spectral mode*
`specBchan γ s = γ − specHeight s` of the self-adjoint fibre generator (here `specHeight s =
-i(s - 1/2)` is the spectral height parameter, real exactly on the critical line `Re s = 1/2`).

The signed mode is the determinant / resolvent value of the one-dimensional self-adjoint operator
`specOp (vonNeumannOp γ) s` (`SelfAdjointGenerator.specBchan_eq_det`); a **spectral cancellation**
is a kernel event of that operator, equivalently a zero of `specBchan` (`specOp_kernel_iff_specBchan_zero`).

Main results.

* `specBchan_re`, `specBchan_im` — the coordinates of the signed mode:
  `Re(specBchan γ s) = γ − Im s`, `Im(specBchan γ s) = Re s − 1/2`.
* `specBchan_im_eq_zero_iff_on_line` — the signed mode is **real** (`Im = 0`) iff `Re s = 1/2`:
  a *sign* (hence a *sign flip*) is defined for the spectral mode **only on the critical line**
  `Re s = 1/2`, i.e. on the **real axis** of the spectral height parameter `specHeight`.
* `specBchan_not_real_off_line` — off the critical line the signed mode has nonzero imaginary part,
  so no sign can be assigned there: **no sign flip can occur off the real axis**.
* `lineMode` and `specBchan_on_line` — on the critical line `s = 1/2 + i u` the signed mode is the
  genuine real number `lineMode γ u = γ − u`.
* `spectral_cancellation_sign_flip` — **the requested "always a sign flip"**: at a spectral
  cancellation (a zero `u = γ` of the real on-line mode) the real spectral mode `lineMode γ` changes
  sign: there is a punctured neighbourhood on which the values to the left and to the right have
  strictly opposite signs.  (It crosses transversally: derivative `-1 ≠ 0`.)
* `sign_flip_only_on_real_axis` — **the requested "only on the real axis"**: a spectral cancellation
  `specBchan γ s = 0` forces `Re s = 1/2`; the cancellation/sign-flip site lies on the critical line.

No `axiom`, no `sorry`.
-/

open Complex Filter Topology
open scoped BigOperators

namespace CriticalLinePhasor.SelfAdjointGenerator

open CriticalLinePhasor CriticalLinePhasor.UnconditionalFrobenius

/-! ## 1. Coordinates of the signed spectral mode -/

/-- The real part of the signed spectral mode: `Re(γ − specHeight s) = γ − Im s`. -/
theorem specBchan_re (γ : ℝ) (s : ℂ) : (specBchan γ s).re = γ - s.im := by
  simp [specBchan, specHeight, Complex.sub_re]
  ring

/-- The imaginary part of the signed spectral mode: `Im(γ − specHeight s) = Re s − 1/2`. -/
theorem specBchan_im (γ : ℝ) (s : ℂ) : (specBchan γ s).im = s.re - 1 / 2 := by
  simp [specBchan, specHeight, Complex.sub_im, Complex.mul_im]

/-- **The signed mode is real exactly on the critical line.**  `Im(specBchan γ s) = 0 ↔ Re s = 1/2`.
A sign (and hence a sign flip) is defined for the spectral mode **only** where it is a genuine real
number, i.e. on the critical line `Re s = 1/2` — the real axis of the spectral height parameter. -/
theorem specBchan_im_eq_zero_iff_on_line (γ : ℝ) (s : ℂ) :
    (specBchan γ s).im = 0 ↔ s.re = 1 / 2 := by
  rw [specBchan_im]; constructor <;> intro h <;> linarith

/-- **Off the critical line the signed mode is not real.**  For `Re s ≠ 1/2` the spectral mode has
nonzero imaginary part, so it admits no sign: **no sign flip can occur off the real axis.** -/
theorem specBchan_not_real_off_line (γ : ℝ) {s : ℂ} (hoff : s.re ≠ 1 / 2) :
    (specBchan γ s).im ≠ 0 := by
  rw [specBchan_im]; intro h; apply hoff; linarith

/-! ## 2. The real on-line mode and the sign flip at a cancellation -/

/-- **The real on-line spectral mode** `lineMode γ u = γ − u`: the value of `specBchan γ` along the
critical line `s = 1/2 + i u`, as a genuine real number of the real height `u`. -/
noncomputable def lineMode (γ : ℝ) (u : ℝ) : ℝ := γ - u

/-- On the critical line `s = 1/2 + i u`, the signed spectral mode is the real number
`lineMode γ u = γ − u`. -/
theorem specBchan_on_line (γ u : ℝ) :
    specBchan γ (1 / 2 + Complex.I * (u : ℂ)) = ((lineMode γ u : ℝ) : ℂ) := by
  simp only [specBchan, specHeight, lineMode]
  ring_nf
  rw [Complex.I_sq]
  push_cast
  ring

/--
**Spectral cancellation always includes a sign flip.**

A spectral cancellation on the critical line is a zero of the real on-line mode `lineMode γ`, which
occurs precisely at the height `u = γ`.  There the mode crosses transversally (derivative `-1 ≠ 0`),
so it **changes sign**: there is a punctured neighbourhood `(γ − δ, γ) ∪ (γ, γ + δ)` on which every
value to the left and every value to the right have strictly opposite signs.  Hence every spectral
cancellation carries a genuine sign flip of the spectral mode.
-/
theorem spectral_cancellation_sign_flip (γ : ℝ) :
    lineMode γ γ = 0 ∧
      ∃ δ > 0, ∀ y ∈ Set.Ioo (γ - δ) γ, ∀ z ∈ Set.Ioo γ (γ + δ),
        lineMode γ y * lineMode γ z < 0 := by
  refine ⟨by simp [lineMode], 1, one_pos, ?_⟩
  intro y hy z hz
  simp only [lineMode]
  exact mul_neg_of_pos_of_neg (by linarith [hy.2]) (by linarith [hz.1])

/-! ## 3. The cancellation event, and that sign flips only occur on the real axis -/

/-- A **spectral cancellation** of the one-dimensional self-adjoint fibre operator
`specOp (vonNeumannOp γ) s` (a nonzero kernel vector) is exactly a zero of the signed mode
`specBchan γ s`. -/
theorem specOp_kernel_iff_specBchan_zero (γ : ℝ) (s : ℂ) :
    (∃ ψ : ℂ, ψ ≠ 0 ∧ specOp (vonNeumannOp γ) s ψ = 0) ↔ specBchan γ s = 0 := by
  constructor
  · rintro ⟨ψ, hψ, hker⟩
    have hop : specOp (vonNeumannOp γ) s ψ = specBchan γ s * ψ := by
      rw [specOp_apply, vonNeumannOp]
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, specBchan]
      ring
    rw [hop] at hker
    exact (mul_eq_zero.mp hker).resolve_right hψ
  · intro h
    refine ⟨1, one_ne_zero, ?_⟩
    rw [specOp_apply, vonNeumannOp]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mul_one]
    have : (γ : ℂ) - specHeight s = 0 := h
    linear_combination this

/--
**Sign flips can only occur on the real axis.**

A spectral cancellation `specBchan γ s = 0` (equivalently a nonzero kernel vector of
`specOp (vonNeumannOp γ) s`) forces `Re s = 1/2`: the cancellation — and therefore the accompanying
sign flip of the spectral mode — lies on the critical line, the real axis of the spectral height
parameter `specHeight`.  Off that axis (`Re s ≠ 1/2`) the signed mode is non-real and cannot vanish
or change sign.
-/
theorem sign_flip_only_on_real_axis (γ : ℝ) {s : ℂ} (h : specBchan γ s = 0) :
    s.re = 1 / 2 := by
  have him : (specBchan γ s).im = 0 := by rw [h]; simp
  exact (specBchan_im_eq_zero_iff_on_line γ s).mp him

/-- **Sign flips only on the real axis (kernel form).**  A spectral cancellation realised as a
nonzero kernel vector of the self-adjoint fibre operator forces the critical line `Re s = 1/2`. -/
theorem spectral_cancellation_on_real_axis (γ : ℝ) {s : ℂ}
    (h : ∃ ψ : ℂ, ψ ≠ 0 ∧ specOp (vonNeumannOp γ) s ψ = 0) : s.re = 1 / 2 :=
  sign_flip_only_on_real_axis γ ((specOp_kernel_iff_specBchan_zero γ s).mp h)

end CriticalLinePhasor.SelfAdjointGenerator
