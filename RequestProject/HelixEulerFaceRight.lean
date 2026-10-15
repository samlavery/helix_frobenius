import RequestProject.BankDoorFaceLaw

/-!
# The Euler face right of the line: the clock floor by reflection about the origin (ledger 1332)

Sam (2026-10-14): "the scaled carrier represents the Euler product". In the house's clock register each prime is a
clock `symClock α ℓ z = e^{izℓ/2} − α e^{−izℓ/2}` of winding `ℓ = log p` (the carrier scaled by `log p`), and the
Euler factor is the clock with face `α = p^{−½}` (`symClock_eq_exp_mul`, 520): on the spectral coordinate
`z = −i(s − ½)`,

  `symClock α ℓ z = e^{(s−½)ℓ/2} · (1 − α e^{−(s−½)ℓ})`,   α = p^{−½}, ℓ = log p  ⟹  `= p^{(s−½)/2}(1 − p^{−s})`.

The prefactor `p^{(s−½)/2}` is the carrier scaling (DC `ℓ/2 = log √p`); the second factor is the Euler factor.

Compiled left of the line (BankDoorFaceLaw, 531): for faces `‖α‖ ≥ 1` and `Re s < ½`,
`Re logDeriv_s(clock) ≤ −clockFloor ℓ (Re s)`. Here the MIRROR, right of the line, for faces `‖α‖ ≤ 1` — which
include every Euler face `p^{−½}` and every unitary face — obtained from the same Herglotz kernel with the disk
point now inside the unit disk (`herglotzKernel_re_ge`):

* `clockFace_logDeriv_re_ge` — for `‖α‖ ≤ 1`, `ℓ > 0`, `Re s > ½`:
  `clockFloor ℓ (1 − Re s) ≤ Re logDeriv_s(symClock α ℓ ∘ spectralCoord)`. The floor is the LEFT floor at the
  mirror abscissa `1 − Re s`: the reflection about the origin exchanges the two laws.
* `bankFace_logDeriv_re_ge` — the finite bank (a finite Euler product with its carrier scalings) has real
  log-derivative at least the sum of the floors; in particular it never vanishes right of the line.
* `logDeriv_symClock_spectral_split` — the clock's log-derivative is `ℓ/2 + logDeriv(Euler factor)`: DC + AC.
* `eulerFactor_logDeriv_re_ge` — the AC floor: `Re logDeriv_s(1 − α e^{−(s−½)ℓ}) ≥ clockFloor ℓ (1 − Re s) − ℓ/2`,
  i.e. for the prime `p` at `σ = Re s`: `log p · Re Σ_k p^{−ks} ≥ −log p · p^{−σ}/(1 + p^{−σ})`, sharp.

What this gives: the per-clock envelope of the prime coherence `C(s) = Σ_p log p · Re Σ_k p^{−ks}` (1323) right of
the line, from the geometry (face inside the disk ⟺ right of the line). What it does not give: the leaf
`C ≤ W` needs the SUM of the clocks against the winding density; the per-clock envelopes sum to the pole
`−ζ′/ζ(σ)` (the END), which reproduces only the classical region. No `sorry`, no `axiom`, no window.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.HelixEulerFaceRight

open CriticalLinePhasor.BankLimit CriticalLinePhasor.ChiralityHB

/-- A clock of face `‖α‖ ≤ 1` does not vanish right of the line. -/
theorem symClock_ne_zero_of_face_le {α : ℂ} (hα : ‖α‖ ≤ 1) {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ}
    (hs : 1 / 2 < s.re) : symClock α ℓ (HilbertPolya.spectralCoord s) ≠ 0 := by
  rw [symClock_eq_exp_mul]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  intro h
  have hw1 : α * Complex.exp (-(Complex.I * HilbertPolya.spectralCoord s * ℓ)) = 1 := by
    linear_combination -h
  have hn := congrArg norm hw1
  rw [face_disk_point_norm, norm_one] at hn
  have hR : Real.exp (ℓ * (1 / 2 - s.re)) < 1 :=
    Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg hℓ (by linarith))
  have hR0 : 0 < Real.exp (ℓ * (1 / 2 - s.re)) := Real.exp_pos _
  nlinarith [hα, hR, norm_nonneg α, hR0]

/-- **The right-side floor** for a face of modulus at most one: the left floor at the mirror abscissa. -/
theorem clockFace_logDeriv_re_ge {α : ℂ} (hα : ‖α‖ ≤ 1) {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    clockFloor ℓ (1 - s.re)
      ≤ (logDeriv (fun w => symClock α ℓ (HilbertPolya.spectralCoord w)) s).re := by
  set z := HilbertPolya.spectralCoord s with hz
  set w : ℂ := α * Complex.exp (-(Complex.I * z * ℓ)) with hw
  set R : ℝ := Real.exp (ℓ * (1 / 2 - s.re)) with hRdef
  have hR : R < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg hℓ (by linarith))
  have hR0 : 0 < R := Real.exp_pos _
  have hwn : ‖w‖ = ‖α‖ * R := face_disk_point_norm α ℓ s
  have hwR : ‖w‖ ≤ R := by
    rw [hwn]; exact mul_le_of_le_one_left hR0.le hα
  have hw1 : ‖w‖ < 1 := lt_of_le_of_lt hwR hR
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
  have hfloor : clockFloor ℓ (1 - s.re) = (ℓ / 2) * ((1 - R) / (1 + R)) := by
    unfold clockFloor
    have : -(ℓ * (1 / 2 - (1 - s.re))) = ℓ * (1 / 2 - s.re) := by ring
    rw [this]
  rw [hfloor]
  have hK1 := herglotzKernel_re_ge hw1
  have hmono : (1 - R) / (1 + R) ≤ (1 - ‖w‖) / (1 + ‖w‖) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith [norm_nonneg w])]
    nlinarith [hwR, mul_nonneg (norm_nonneg w) hR0.le, mul_comm R ‖w‖]
  have hℓ2 : 0 ≤ ℓ / 2 := by positivity
  calc (ℓ / 2) * ((1 - R) / (1 + R))
      ≤ (ℓ / 2) * ((1 - ‖w‖) / (1 + ‖w‖)) := mul_le_mul_of_nonneg_left hmono hℓ2
    _ ≤ (ℓ / 2) * ((1 + w) / (1 - w)).re := mul_le_mul_of_nonneg_left hK1 hℓ2

/-- **The bank floor right of the line**: a finite Euler product with its carrier scalings. -/
theorem bankFace_logDeriv_re_ge {ι : Type*} (t : Finset ι) (α : ι → ℂ) (ℓ : ι → ℝ)
    (hα : ∀ i ∈ t, ‖α i‖ ≤ 1) (hℓ : ∀ i ∈ t, 0 < ℓ i) {s : ℂ} (hs : 1 / 2 < s.re) :
    ∑ i ∈ t, clockFloor (ℓ i) (1 - s.re)
      ≤ (logDeriv (fun w => ∏ i ∈ t,
          symClock (α i) (ℓ i) (HilbertPolya.spectralCoord w)) s).re := by
  have hstep : logDeriv (fun w => ∏ i ∈ t,
      symClock (α i) (ℓ i) (HilbertPolya.spectralCoord w)) s
      = ∑ i ∈ t, logDeriv (fun w =>
          symClock (α i) (ℓ i) (HilbertPolya.spectralCoord w)) s := by
    exact logDeriv_fun_prod
      (fun i hi => symClock_ne_zero_of_face_le (hα i hi) (hℓ i hi) hs)
      (fun i hi => (symClock_differentiableAt (α i) (ℓ i) _).comp s
        (spectralCoord_hasDerivAt s).differentiableAt)
  rw [hstep, Complex.re_sum]
  exact Finset.sum_le_sum (fun i hi => clockFace_logDeriv_re_ge (hα i hi) (hℓ i hi) hs)

/-- The Euler face `0 < r ≤ 1` (`r = p^{−½}`) right of the line. -/
theorem eulerFace_logDeriv_re_ge {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    clockFloor ℓ (1 - s.re)
      ≤ (logDeriv (fun w => symClock (r : ℂ) ℓ (HilbertPolya.spectralCoord w)) s).re := by
  apply clockFace_logDeriv_re_ge _ hℓ hs
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  exact hr1

/-! ## DC + AC: carrier scaling times Euler factor -/

/-- The clock on the spectral coordinate is the carrier scaling times the Euler factor. -/
theorem symClock_spectral_split (α : ℂ) (ℓ : ℝ) (w : ℂ) :
    symClock α ℓ (HilbertPolya.spectralCoord w)
      = Complex.exp ((w - 1 / 2) * ℓ / 2) * (1 - α * Complex.exp (-((w - 1 / 2) * ℓ))) := by
  rw [symClock_eq_exp_mul]
  unfold HilbertPolya.spectralCoord
  have h1 : Complex.I * (-Complex.I * (w - 1 / 2)) * ℓ / 2 = (w - 1 / 2) * ℓ / 2 := by
    linear_combination (-(w - 1 / 2) * ℓ / 2) * Complex.I_sq
  have h2 : -(Complex.I * (-Complex.I * (w - 1 / 2)) * ℓ) = -((w - 1 / 2) * ℓ) := by
    linear_combination ((w - 1 / 2) * ℓ) * Complex.I_sq
  rw [h1, h2]

/-- The Euler factor does not vanish right of the line for a face of modulus at most one. -/
theorem eulerFactor_ne_zero {α : ℂ} (hα : ‖α‖ ≤ 1) {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : 1 / 2 < s.re) :
    1 - α * Complex.exp (-((s - 1 / 2) * ℓ)) ≠ 0 := by
  intro h
  have h1 : α * Complex.exp (-((s - 1 / 2) * ℓ)) = 1 := by linear_combination -h
  have hn := congrArg norm h1
  rw [norm_mul, Complex.norm_exp, norm_one] at hn
  have hre : (-((s - 1 / 2) * (ℓ : ℂ))).re = -((s.re - 1 / 2) * ℓ) := by
    simp [Complex.mul_re, Complex.sub_re]
  rw [hre] at hn
  have hR : Real.exp (-((s.re - 1 / 2) * ℓ)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos (by linarith) hℓ))
  have hR0 : 0 < Real.exp (-((s.re - 1 / 2) * ℓ)) := Real.exp_pos _
  nlinarith [hα, hR, norm_nonneg α, hR0]

/-- **DC + AC**: `logDeriv_s(clock) = ℓ/2 + logDeriv_s(Euler factor)` right of the line. -/
theorem logDeriv_symClock_spectral_split {α : ℂ} (hα : ‖α‖ ≤ 1) {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    logDeriv (fun w => symClock α ℓ (HilbertPolya.spectralCoord w)) s
      = (ℓ / 2 : ℂ) + logDeriv (fun w => 1 - α * Complex.exp (-((w - 1 / 2) * ℓ))) s := by
  have hfun : (fun w => symClock α ℓ (HilbertPolya.spectralCoord w))
      = (fun w => Complex.exp ((w - 1 / 2) * ℓ / 2))
        * (fun w => 1 - α * Complex.exp (-((w - 1 / 2) * ℓ))) :=
    funext fun w => symClock_spectral_split α ℓ w
  rw [hfun]
  have hin1 : HasDerivAt (fun w : ℂ => (w - 1 / 2) * ℓ / 2) (1 * (ℓ : ℂ) / 2) s :=
    (((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).mul_const (ℓ : ℂ)).div_const 2
  have hd1 : HasDerivAt (fun w : ℂ => Complex.exp ((w - 1 / 2) * ℓ / 2))
      (Complex.exp ((s - 1 / 2) * ℓ / 2) * (1 * (ℓ : ℂ) / 2)) s := hin1.cexp
  have hin2 : HasDerivAt (fun w : ℂ => -((w - 1 / 2) * ℓ)) (-(1 * (ℓ : ℂ))) s :=
    (((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).mul_const (ℓ : ℂ)).neg
  have hd2 : HasDerivAt (fun w : ℂ => 1 - α * Complex.exp (-((w - 1 / 2) * ℓ)))
      (-(α * (Complex.exp (-((s - 1 / 2) * ℓ)) * (-(1 * (ℓ : ℂ)))))) s :=
    (hin2.cexp.const_mul α).const_sub 1
  have hf : (fun w : ℂ => Complex.exp ((w - 1 / 2) * ℓ / 2)) s ≠ 0 := Complex.exp_ne_zero _
  have hg : (fun w : ℂ => 1 - α * Complex.exp (-((w - 1 / 2) * ℓ))) s ≠ 0 :=
    eulerFactor_ne_zero hα hℓ hs
  rw [logDeriv_mul s hf hg hd1.differentiableAt hd2.differentiableAt]
  congr 1
  rw [logDeriv_apply, hd1.deriv]
  field_simp
  try ring

/-- **The AC floor of a prime clock**: `Re logDeriv_s(1 − α e^{−(s−½)ℓ}) ≥ clockFloor ℓ (1 − Re s) − ℓ/2`. -/
theorem eulerFactor_logDeriv_re_ge {α : ℂ} (hα : ‖α‖ ≤ 1) {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    clockFloor ℓ (1 - s.re) - ℓ / 2
      ≤ (logDeriv (fun w => 1 - α * Complex.exp (-((w - 1 / 2) * ℓ))) s).re := by
  have h := clockFace_logDeriv_re_ge hα hℓ hs
  rw [logDeriv_symClock_spectral_split hα hℓ hs, Complex.add_re] at h
  have : ((ℓ / 2 : ℂ)).re = ℓ / 2 := by simp
  rw [this] at h
  linarith

end CriticalLinePhasor.HelixEulerFaceRight

end

#print axioms CriticalLinePhasor.HelixEulerFaceRight.clockFace_logDeriv_re_ge
#print axioms CriticalLinePhasor.HelixEulerFaceRight.bankFace_logDeriv_re_ge
#print axioms CriticalLinePhasor.HelixEulerFaceRight.logDeriv_symClock_spectral_split
#print axioms CriticalLinePhasor.HelixEulerFaceRight.eulerFactor_logDeriv_re_ge
