import RequestProject.StOscillation

/-!
# Carrier parity quantization: axis-reality of the EXACT fiber on the `Δ`-scaled carrier

This is obligation **(1a)** of the certified-extractor programme, proved for the **exact limit
object** rather than for a finite head of the phasor bank.  The point of doing it here and not at
the bank is that the statement is *structural*: it is an identity between the carrier fiber and the
completed zeta, so it holds with no truncation, no window, and no error term.  The finite-head
approximation is a separate obligation, and it only has to stay off a decision boundary that this
file locates exactly.

## The geometry

The carrier is the numberline scaled by the harmonic constant `Δ` (the house value is `π/3`); the
sites sit at arclength `x_n = Δ·n`; the P and M lanes are the odd and even sites, entering with
opposite sign.  Summing the lanes against `x_n^{-s}` gives

`carrierFiber Δ s = Δ^{-s} · (1 - 2^{1-s}) · ζ(s)`,

the `Δ^{-s}` being the carrier's scale and the alternating factor being the P/M lane split (the
Dirichlet eta function).  The **weld factor** is the purely geometric prefactor obtained by
dividing out the archimedean local factor,

`weldFactor Δ t = Δ^{-(½+it)} · (1 - 2^{½-it}) / Γℝ(½+it)`,

and the content of this file is that the carrier fiber is exactly this factor times the completed
zeta:  `carrierFiber Δ (½+it) = weldFactor Δ t · Λ(½+it)`.

## What follows

Since `Λ(½+it)` is real (`HelixCollapse.completedRiemannZeta_critical_line_im_zero`, proved from the
functional equation and Schwarz reflection), rotating the fiber by the weld factor's own argument
lands it on the real axis, with the **exactly computable positive modulus** `‖weldFactor Δ t‖` as
the common mode:

`e^{-i·arg(weldFactor Δ t)} · carrierFiber Δ (½+it) = ‖weldFactor Δ t‖ · Λ(½+it)`.

* `weld_gauge_exact` — the identity above, with the modulus in closed form.
* `weld_gauge_im_zero` — **axis-reality of the exact object**.
* `weldReadout_eq_zero_iff` — the readout vanishes exactly at the on-line zeros of `ζ`, at no other
  height, and for every carrier scale.
* `carrier_phase_quantized` — the phase of the gauged fiber is `0` or `π` wherever it is nonzero.
  This is the parity bit: it is read from the fiber's own argument and consumes no prime data.
* `weldReadout_carrier_ratio`, `weldReadout_sign_carrier_free` — the readout at two carrier scales
  differs by a **positive** factor, so the parity bit is a carrier-scale gauge invariant.  `Δ = π/3`
  and `Δ = π/6` give the same bit, as the measurements record.
* `weldFactor_norm` — the common mode evaluated exactly: `Δ^{-1/2}·‖1-2^{½-it}‖/‖Γℝ(½+it)‖`.

Nothing here is asymptotic.  In particular the Riemann–Siegel theta never appears: its role is
played by `arg Γℝ(½+it)`, which it equals, and the argument is taken of an exactly defined factor.
-/

open Complex

namespace CriticalLinePhasor.CarrierParity

/-- The carrier fiber at scale `Δ`: the P/M lane-balanced phasor bank, read at `s`.
`Δ^{-s}` is the carrier's arclength scale, `1 - 2^{1-s}` the lane split. -/
noncomputable def carrierFiber (Δ : ℝ) (s : ℂ) : ℂ :=
  (Δ : ℂ) ^ (-s) * ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)

/-- The weld factor: the carrier fiber's purely geometric prefactor on the line, with the
archimedean local factor divided out.  Its argument is the house weld gauge `ψ`, up to `2πℤ`. -/
noncomputable def weldFactor (Δ : ℝ) (t : ℝ) : ℂ :=
  (Δ : ℂ) ^ (-(1 / 2 + (t : ℂ) * I)) * (1 - (2 : ℂ) ^ (1 / 2 - (t : ℂ) * I))
    / Gammaℝ (1 / 2 + (t : ℂ) * I)

/-- The reflected line point. -/
theorem one_sub_line (t : ℝ) : 1 - (1 / 2 + (t : ℂ) * I) = 1 / 2 - (t : ℂ) * I := by ring

/-- The lane-split factor never vanishes on the line: `‖2^{½-it}‖ = √2 ≠ 1`. -/
theorem lane_factor_ne_zero (t : ℝ) : (1 : ℂ) - (2 : ℂ) ^ (1 / 2 - (t : ℂ) * I) ≠ 0 := by
  intro h
  have h1 : (2 : ℂ) ^ ((1 : ℂ) / 2 - (t : ℂ) * I) = 1 := by
    have := sub_eq_zero.mp h
    exact this.symm
  have hnorm : ‖(2 : ℂ) ^ ((1 : ℂ) / 2 - (t : ℂ) * I)‖ = (2 : ℝ) ^ (1 / 2 : ℝ) := by
    have hb := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)
      ((1 : ℂ) / 2 - (t : ℂ) * I)
    rw [show (((2 : ℝ)) : ℂ) = (2 : ℂ) by norm_num] at hb
    rw [hb]
    congr 1
    simp [Complex.sub_re, Complex.mul_re]
  rw [h1] at hnorm
  have hgt : (1 : ℝ) < (2 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, by norm_num⟩)
  rw [← hnorm] at hgt
  simp at hgt

/-- The carrier scale factor never vanishes. -/
theorem carrier_scale_ne_zero {Δ : ℝ} (hΔ : 0 < Δ) (s : ℂ) : (Δ : ℂ) ^ (-s) ≠ 0 := by
  have : ‖(Δ : ℂ) ^ (-s)‖ = Δ ^ (-s).re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hΔ _
  intro h
  rw [h, norm_zero] at this
  exact absurd this.symm (ne_of_gt (Real.rpow_pos_of_pos hΔ _))

/-- The weld factor is never zero, at any height and any positive carrier scale. -/
theorem weldFactor_ne_zero {Δ : ℝ} (hΔ : 0 < Δ) (t : ℝ) : weldFactor Δ t ≠ 0 := by
  rw [weldFactor]
  exact div_ne_zero (mul_ne_zero (carrier_scale_ne_zero hΔ _) (lane_factor_ne_zero t))
    (StOscillation.gauge_ne_zero_on_line t)

/-- **The factorization.**  On the critical line the carrier fiber is the weld factor times the
completed zeta — exactly, with no truncation and at every carrier scale. -/
theorem carrierFiber_eq_weldFactor_mul (Δ : ℝ) (t : ℝ) :
    carrierFiber Δ (1 / 2 + (t : ℂ) * I)
      = weldFactor Δ t * completedRiemannZeta (1 / 2 + (t : ℂ) * I) := by
  rw [carrierFiber, weldFactor, one_sub_line,
    riemannZeta_def_of_ne_zero (StOscillation.line_ne_zero t)]
  ring

/-- Rotating by a nonzero number's own argument lands it on its modulus. -/
theorem exp_neg_arg_mul_self (w : ℂ) :
    Complex.exp (-(w.arg : ℂ) * I) * w = (‖w‖ : ℂ) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
  rw [mul_left_comm, ← Complex.exp_add]
  simp

/-- **The weld gauge, exactly.**  The carrier fiber rotated by the weld factor's argument equals
the (positive, exactly computable) modulus times the completed zeta.  The common mode is evaluated
outright; nothing is estimated. -/
theorem weld_gauge_exact (Δ : ℝ) (t : ℝ) :
    Complex.exp (-((weldFactor Δ t).arg : ℂ) * I) * carrierFiber Δ (1 / 2 + (t : ℂ) * I)
      = (‖weldFactor Δ t‖ : ℂ) * completedRiemannZeta (1 / 2 + (t : ℂ) * I) := by
  rw [carrierFiber_eq_weldFactor_mul Δ t, ← mul_assoc, exp_neg_arg_mul_self]

/-- **Axis-reality of the exact object.**  The weld-gauged carrier fiber is real at every height,
for every positive carrier scale.  This is obligation (1a) for the limit object: no finite head, no
window, no error term. -/
theorem weld_gauge_im_zero (Δ : ℝ) (t : ℝ) :
    (Complex.exp (-((weldFactor Δ t).arg : ℂ) * I)
      * carrierFiber Δ (1 / 2 + (t : ℂ) * I)).im = 0 := by
  have hL : (completedRiemannZeta (1 / 2 + (t : ℂ) * I)).im = 0 :=
    HelixCollapse.completedRiemannZeta_critical_line_im_zero t
  rw [weld_gauge_exact Δ t, Complex.mul_im, hL]
  simp

/-- The real readout of the two-ended carrier: the weld-gauged fiber, as a real number. -/
noncomputable def weldReadout (Δ : ℝ) (t : ℝ) : ℝ :=
  ‖weldFactor Δ t‖ * (completedRiemannZeta (1 / 2 + (t : ℂ) * I)).re

/-- The readout IS the whole gauged value, not just its real part. -/
theorem weldReadout_eq_gauged (Δ : ℝ) (t : ℝ) :
    ((weldReadout Δ t : ℝ) : ℂ)
      = Complex.exp (-((weldFactor Δ t).arg : ℂ) * I) * carrierFiber Δ (1 / 2 + (t : ℂ) * I) := by
  have hL : ((completedRiemannZeta (1 / 2 + (t : ℂ) * I)).re : ℂ)
      = completedRiemannZeta (1 / 2 + (t : ℂ) * I) := by
    apply Complex.ext
    · exact Complex.ofReal_re _
    · rw [Complex.ofReal_im]
      exact (HelixCollapse.completedRiemannZeta_critical_line_im_zero t).symm
  rw [weld_gauge_exact Δ t, weldReadout, Complex.ofReal_mul, hL]

/-- The completed zeta factors through the archimedean local factor on the line. -/
theorem completed_eq_gauge_mul_zeta (t : ℝ) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * I)
      = Gammaℝ (1 / 2 + (t : ℂ) * I) * riemannZeta (1 / 2 + (t : ℂ) * I) := by
  rw [riemannZeta_def_of_ne_zero (StOscillation.line_ne_zero t),
    mul_div_cancel₀ _ (StOscillation.gauge_ne_zero_on_line t)]

/-- **The readout locates exactly the on-line zeros**, at every carrier scale: it vanishes at a
height precisely when `ζ` does, and nowhere else. -/
theorem weldReadout_eq_zero_iff {Δ : ℝ} (hΔ : 0 < Δ) (t : ℝ) :
    weldReadout Δ t = 0 ↔ riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  have hw : ‖weldFactor Δ t‖ ≠ 0 := norm_ne_zero_iff.mpr (weldFactor_ne_zero hΔ t)
  have hre : ((completedRiemannZeta (1 / 2 + (t : ℂ) * I)).re = 0)
      ↔ completedRiemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
    constructor
    · intro h
      exact Complex.ext h (HelixCollapse.completedRiemannZeta_critical_line_im_zero t)
    · intro h; rw [h]; simp
  rw [weldReadout, mul_eq_zero, or_iff_right hw, hre, completed_eq_gauge_mul_zeta t, mul_eq_zero,
    or_iff_right (StOscillation.gauge_ne_zero_on_line t)]

/-- **The parity bit.**  Away from the zeros the weld-gauged carrier fiber has phase exactly `0` or
`π`.  It is read from the fiber's own argument together with the weld factor's, and consumes no
prime data at all. -/
theorem carrier_phase_quantized {Δ : ℝ} (hΔ : 0 < Δ) (t : ℝ)
    (h0 : riemannZeta (1 / 2 + (t : ℂ) * I) ≠ 0) :
    (Complex.exp (-((weldFactor Δ t).arg : ℂ) * I)
        * carrierFiber Δ (1 / 2 + (t : ℂ) * I)).arg = 0 ∨
      (Complex.exp (-((weldFactor Δ t).arg : ℂ) * I)
        * carrierFiber Δ (1 / 2 + (t : ℂ) * I)).arg = Real.pi := by
  refine StOscillation.real_arg_quantized (weld_gauge_im_zero Δ t) ?_
  rw [← weldReadout_eq_gauged Δ t]
  simpa using fun h => h0 ((weldReadout_eq_zero_iff hΔ t).mp h)

/-- **The common mode, evaluated exactly.**  No estimate enters the modulus. -/
theorem weldFactor_norm {Δ : ℝ} (hΔ : 0 < Δ) (t : ℝ) :
    ‖weldFactor Δ t‖
      = Δ ^ (-(1 / 2) : ℝ) * ‖1 - (2 : ℂ) ^ (1 / 2 - (t : ℂ) * I)‖
          / ‖Gammaℝ (1 / 2 + (t : ℂ) * I)‖ := by
  rw [weldFactor, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hΔ]
  congr 2
  simp [Complex.neg_re, Complex.add_re, Complex.mul_re]

/-- **Carrier-scale gauge invariance.**  Two carrier scales give readouts differing by a positive
factor, so the sign — and hence the parity bit — is the same for every `Δ > 0`.  `π/3` and `π/6`
give the same bit. -/
theorem weldReadout_carrier_ratio {Δ Δ' : ℝ} (hΔ : 0 < Δ) (_hΔ' : 0 < Δ') (t : ℝ) :
    weldReadout Δ' t = (‖weldFactor Δ' t‖ / ‖weldFactor Δ t‖) * weldReadout Δ t := by
  have hw : ‖weldFactor Δ t‖ ≠ 0 := norm_ne_zero_iff.mpr (weldFactor_ne_zero hΔ t)
  rw [weldReadout, weldReadout]
  field_simp

/-- The ratio in `weldReadout_carrier_ratio` is strictly positive. -/
theorem weldReadout_carrier_ratio_pos {Δ Δ' : ℝ} (hΔ : 0 < Δ) (hΔ' : 0 < Δ') (t : ℝ) :
    0 < ‖weldFactor Δ' t‖ / ‖weldFactor Δ t‖ :=
  div_pos (norm_pos_iff.mpr (weldFactor_ne_zero hΔ' t))
    (norm_pos_iff.mpr (weldFactor_ne_zero hΔ t))

/-- **The parity bit is carrier-free**: positivity of the readout does not depend on the scale. -/
theorem weldReadout_sign_carrier_free {Δ Δ' : ℝ} (hΔ : 0 < Δ) (hΔ' : 0 < Δ') (t : ℝ) :
    (0 < weldReadout Δ' t ↔ 0 < weldReadout Δ t) := by
  rw [weldReadout_carrier_ratio hΔ hΔ' t]
  exact mul_pos_iff_of_pos_left (weldReadout_carrier_ratio_pos hΔ hΔ' t)

end CriticalLinePhasor.CarrierParity
