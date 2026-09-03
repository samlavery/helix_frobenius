import RequestProject.BankDoorClassLaw
import RequestProject.ClockPoissonBarycenter

/-!
# The door-law floor for every face of modulus at least one (the barycenter faces included)

`BankDoorClassLaw.bank_logDeriv_re_le` gives, for UNIMODULAR faces and `Re s < ½`, the floor
`Re logDeriv_s(clock) ≤ −clockFloor ℓ σ`.  att530 (ledger 530) measured the same floor on the
Poisson-barycenter face left of the line — the anti-Euler / conduction clock with face `r⁻¹`,
`r = p^{−½}` (`unitaryClocks_poisson_barycenter_antiEulerFace`) — with slack `−0.059`.

This file proves it, and more: the floor holds for EVERY face `‖α‖ ≥ 1`, with no integral.
In the face form the clock's log-derivative in `s` is `(ℓ/2)·(1+w)/(1−w)` with
`w = α·e^{−i z ℓ}`, `z = spectralCoord s`, and `‖w‖ = ‖α‖·e^{ℓ(½−σ)} ≥ e^{ℓ(½−σ)} > 1`; above the
unit circle the Herglotz kernel's real part is `(1−‖w‖²)/‖1−w‖² ≤ −(‖w‖−1)/(‖w‖+1)`, and
`x ↦ (x−1)/(x+1)` is increasing, so a larger face gives a stronger floor.

* `herglotzKernel_re_le_of_one_lt` — the kernel bound above the circle.
* `symClock_eq_exp_mul` — `symClock α ℓ z = e^{izℓ/2}(1 − α e^{−izℓ})`.
* `clockFace_logDeriv_re_le` — the floor for one clock of face `‖α‖ ≥ 1`.
* `bankFace_logDeriv_re_le` — the floor sum for a finite bank of such clocks.
* `antiEulerFace_logDeriv_re_le` — the instance measured by att530: face `(r:ℂ)⁻¹`, `0 < r ≤ 1`.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.BankLimit

open CriticalLinePhasor.ChiralityHB

/-- Above the unit circle the Herglotz kernel's real part is at most `−(‖w‖−1)/(‖w‖+1)`. -/
theorem herglotzKernel_re_le_of_one_lt {w : ℂ} (hw : 1 < ‖w‖) :
    ((1 + w) / (1 - w)).re ≤ -((‖w‖ - 1) / (‖w‖ + 1)) := by
  rw [herglotzKernel_re]
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    have h1 : w = 1 := by linear_combination -h
    rw [h1, norm_one] at hw
    exact lt_irrefl _ hw
  have hpos : 0 < ‖1 - w‖ := norm_pos_iff.mpr hne
  have hle : ‖1 - w‖ ≤ 1 + ‖w‖ := by
    calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ = 1 + ‖w‖ := by rw [norm_one]
  have hneg : 1 - ‖w‖ ^ 2 ≤ 0 := by nlinarith
  have hsq : ‖1 - w‖ ^ 2 ≤ (1 + ‖w‖) ^ 2 := by gcongr
  have h1w : 0 < 1 + ‖w‖ := by linarith [norm_nonneg w]
  have h1 : (1 - ‖w‖ ^ 2) / ‖1 - w‖ ^ 2 ≤ (1 - ‖w‖ ^ 2) / (1 + ‖w‖) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonpos_left hsq hneg
  have h2 : (1 - ‖w‖ ^ 2) / (1 + ‖w‖) ^ 2 = -((‖w‖ - 1) / (‖w‖ + 1)) := by
    have hne' : 1 + ‖w‖ ≠ 0 := h1w.ne'
    have hne'' : ‖w‖ + 1 ≠ 0 := by linarith [norm_nonneg w]
    field_simp
    ring
  calc (1 - ‖w‖ ^ 2) / ‖1 - w‖ ^ 2 ≤ (1 - ‖w‖ ^ 2) / (1 + ‖w‖) ^ 2 := h1
    _ = -((‖w‖ - 1) / (‖w‖ + 1)) := h2

/-- `symClock α ℓ z = e^{izℓ/2}·(1 − α e^{−izℓ})`. -/
theorem symClock_eq_exp_mul (α : ℂ) (ℓ : ℝ) (z : ℂ) :
    symClock α ℓ z
      = Complex.exp (Complex.I * z * ℓ / 2) * (1 - α * Complex.exp (-(Complex.I * z * ℓ))) := by
  unfold symClock
  have h : Complex.exp (Complex.I * z * ℓ / 2) * Complex.exp (-(Complex.I * z * ℓ))
      = Complex.exp (-(Complex.I * z * ℓ / 2)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  linear_combination α * h

/-- The disk point of a clock at the spectral coordinate: `‖α e^{−izℓ}‖ = ‖α‖·e^{ℓ(½−σ)}`. -/
theorem face_disk_point_norm (α : ℂ) (ℓ : ℝ) (s : ℂ) :
    ‖α * Complex.exp (-(Complex.I * HilbertPolya.spectralCoord s * ℓ))‖
      = ‖α‖ * Real.exp (ℓ * (1 / 2 - s.re)) := by
  rw [norm_mul, Complex.norm_exp]
  congr 1
  have h : (-(Complex.I * HilbertPolya.spectralCoord s * (ℓ : ℂ))).re
      = ℓ * (HilbertPolya.spectralCoord s).im := by
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [h, spectralCoord_im]

/-- A clock of face `‖α‖ ≥ 1` does not vanish at a spectral point left of the line. -/
theorem symClock_ne_zero_of_face_ge {α : ℂ} (hα : 1 ≤ ‖α‖) {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ}
    (hs : s.re < 1 / 2) : symClock α ℓ (HilbertPolya.spectralCoord s) ≠ 0 := by
  rw [symClock_eq_exp_mul]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  intro h
  have hw1 : α * Complex.exp (-(Complex.I * HilbertPolya.spectralCoord s * ℓ)) = 1 := by
    linear_combination -h
  have hn := congrArg norm hw1
  rw [face_disk_point_norm, norm_one] at hn
  have hR : 1 < Real.exp (ℓ * (1 / 2 - s.re)) := Real.one_lt_exp_iff.mpr (by nlinarith)
  nlinarith [hα, hR, norm_nonneg α]

/-- **The door-law floor for a face of modulus at least one.**  For `‖α‖ ≥ 1`, `ℓ > 0` and
`Re s < ½`, `Re logDeriv_s(symClock α ℓ ∘ spectralCoord) ≤ −clockFloor ℓ (Re s)`. -/
theorem clockFace_logDeriv_re_le {α : ℂ} (hα : 1 ≤ ‖α‖) {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ}
    (hs : s.re < 1 / 2) :
    (logDeriv (fun w => symClock α ℓ (HilbertPolya.spectralCoord w)) s).re
      ≤ -clockFloor ℓ s.re := by
  set z := HilbertPolya.spectralCoord s with hz
  set w : ℂ := α * Complex.exp (-(Complex.I * z * ℓ)) with hw
  set R : ℝ := Real.exp (ℓ * (1 / 2 - s.re)) with hRdef
  have hR : 1 < R := Real.one_lt_exp_iff.mpr (by nlinarith)
  have hR0 : 0 < R := by linarith
  have hwn : ‖w‖ = ‖α‖ * R := face_disk_point_norm α ℓ s
  have hRw : R ≤ ‖w‖ := by
    rw [hwn]
    nlinarith [hα, hR0]
  have hw1 : 1 < ‖w‖ := lt_of_lt_of_le hR hRw
  have hne : 1 - w ≠ 0 := by
    intro h
    have h1 : w = 1 := by linear_combination -h
    rw [h1, norm_one] at hw1
    exact lt_irrefl _ hw1
  have hcomp : logDeriv (fun w => symClock α ℓ (HilbertPolya.spectralCoord w)) s
      = logDeriv (symClock α ℓ) z * deriv HilbertPolya.spectralCoord s :=
    logDeriv_comp (symClock_differentiableAt α ℓ _) (spectralCoord_hasDerivAt s).differentiableAt
  rw [hcomp, (spectralCoord_hasDerivAt s).deriv, symClock_logDeriv_face_form α ℓ z hne]
  have hK : (Complex.I * ℓ / 2) * ((1 + w) / (1 - w)) * (-Complex.I)
      = ((ℓ / 2 : ℝ) : ℂ) * ((1 + w) / (1 - w)) := by
    push_cast
    linear_combination (-(ℓ : ℂ) / 2 * ((1 + w) / (1 - w))) * Complex.I_sq
  rw [hK, Complex.re_ofReal_mul]
  have hRinv : 0 < R⁻¹ := inv_pos.mpr hR0
  have hkey : (1 - R⁻¹) / (1 + R⁻¹) = (R - 1) / (R + 1) := by
    rw [div_eq_div_iff (ne_of_gt (by linarith : (0 : ℝ) < 1 + R⁻¹))
      (ne_of_gt (by linarith : (0 : ℝ) < R + 1))]
    linear_combination (-2 : ℝ) * (inv_mul_cancel₀ hR0.ne')
  have hfloor : clockFloor ℓ s.re = (ℓ / 2) * ((R - 1) / (R + 1)) := by
    unfold clockFloor
    rw [Real.exp_neg, ← hRdef, hkey]
  rw [hfloor]
  have hK1 := herglotzKernel_re_le_of_one_lt hw1
  have hmono : (R - 1) / (R + 1) ≤ (‖w‖ - 1) / (‖w‖ + 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hℓ2 : 0 ≤ ℓ / 2 := by positivity
  calc (ℓ / 2) * ((1 + w) / (1 - w)).re
      ≤ (ℓ / 2) * (-((‖w‖ - 1) / (‖w‖ + 1))) := mul_le_mul_of_nonneg_left hK1 hℓ2
    _ ≤ (ℓ / 2) * (-((R - 1) / (R + 1))) := by
        apply mul_le_mul_of_nonneg_left _ hℓ2
        linarith [hmono]
    _ = -((ℓ / 2) * ((R - 1) / (R + 1))) := by ring

/-- **The bank floor for faces of modulus at least one.** -/
theorem bankFace_logDeriv_re_le {ι : Type*} (t : Finset ι) (α : ι → ℂ) (ℓ : ι → ℝ)
    (hα : ∀ i ∈ t, 1 ≤ ‖α i‖) (hℓ : ∀ i ∈ t, 0 < ℓ i) {s : ℂ} (hs : s.re < 1 / 2) :
    (logDeriv (fun w => ∏ i ∈ t,
        symClock (α i) (ℓ i) (HilbertPolya.spectralCoord w)) s).re
      ≤ -∑ i ∈ t, clockFloor (ℓ i) s.re := by
  have hstep : logDeriv (fun w => ∏ i ∈ t,
      symClock (α i) (ℓ i) (HilbertPolya.spectralCoord w)) s
      = ∑ i ∈ t, logDeriv (fun w =>
          symClock (α i) (ℓ i) (HilbertPolya.spectralCoord w)) s := by
    exact logDeriv_prod
      (fun i hi => symClock_ne_zero_of_face_ge (hα i hi) (hℓ i hi) hs)
      (fun i hi => (symClock_differentiableAt (α i) (ℓ i) _).comp s
        (spectralCoord_hasDerivAt s).differentiableAt)
  rw [hstep, Complex.re_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum (fun i hi => clockFace_logDeriv_re_le (hα i hi) (hℓ i hi) hs)

/-- **The instance att530 measured**: the anti-Euler / conduction face `r⁻¹`, `0 < r ≤ 1`
(`r = p^{−½}` gives the conduction clock `e^{izℓ/2}(1 − p^{1−s})` of the ordered readout, by
`unitaryClocks_poisson_barycenter_antiEulerFace` the Poisson barycenter of unitary faces left of
the line). -/
theorem antiEulerFace_logDeriv_re_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {s : ℂ} (hs : s.re < 1 / 2) :
    (logDeriv (fun w => symClock ((r : ℂ)⁻¹) ℓ (HilbertPolya.spectralCoord w)) s).re
      ≤ -clockFloor ℓ s.re := by
  apply clockFace_logDeriv_re_le _ hℓ hs
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  exact one_le_inv_iff₀.mpr ⟨hr0, hr1⟩

end CriticalLinePhasor.BankLimit

#print axioms CriticalLinePhasor.BankLimit.herglotzKernel_re_le_of_one_lt
#print axioms CriticalLinePhasor.BankLimit.clockFace_logDeriv_re_le
#print axioms CriticalLinePhasor.BankLimit.bankFace_logDeriv_re_le
#print axioms CriticalLinePhasor.BankLimit.antiEulerFace_logDeriv_re_le
