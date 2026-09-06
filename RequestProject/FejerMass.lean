import Mathlib

/-!
# The total Fejér mass: `∫_ℝ (1 − cos Lu)/(L u²) du = π` (ledger 610)

The Fejér kernel on the line (609, `rieszKernel_re_line_eq`) is `F_L(u) = (1 − cos Lu)/(L u²)`. Its
total mass is what makes an on-line zero deep inside a gap carry weight one. Mathlib has neither the
Dirichlet integral nor `∫ sinc²`, so the mass is obtained from Fourier inversion for the triangle
`tri L x = (1 − |x|/L)₊`: its transform is `𝓕 tri w = (1 − cos 2πLw)/(2π²Lw²) = 2 F_L(2πw)` (one
fundamental-theorem step on `[0, L]` and the symmetry `v ↦ −v`), it is integrable, and inversion at
`0` gives `∫ 𝓕 tri = tri 0 = 1`, hence `∫ F_L = π` after the scaling `u = 2πw`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform Real

namespace CriticalLinePhasor.ContourArgument

/-- The Fejér kernel on the line, `(1 − cos Lu)/(L u²)` (value `0` at `u = 0` by convention; a null set). -/
noncomputable def fejer (L u : ℝ) : ℝ := (1 - Real.cos (L * u)) / (L * u ^ 2)

/-- The triangle of half-width `L`. -/
noncomputable def tri (L : ℝ) (x : ℝ) : ℂ := ((max (1 - |x| / L) 0 : ℝ) : ℂ)

theorem tri_continuous (L : ℝ) : Continuous (tri L) := by
  unfold tri; fun_prop

theorem tri_zero (L : ℝ) : tri L 0 = 1 := by
  simp [tri]

theorem tri_eq_zero_of_le_abs {L : ℝ} (hL : 0 < L) {x : ℝ} (hx : L ≤ |x|) : tri L x = 0 := by
  unfold tri
  rw [max_eq_right]
  · simp
  · rw [sub_nonpos, one_le_div hL]; exact hx

theorem tri_eq_of_abs_le {L : ℝ} (hL : 0 < L) {x : ℝ} (hx : |x| ≤ L) :
    tri L x = ((1 - |x| / L : ℝ) : ℂ) := by
  unfold tri
  rw [max_eq_left]
  rw [sub_nonneg, div_le_one hL]; exact hx

theorem tri_integrable {L : ℝ} (hL : 0 < L) : Integrable (tri L) := by
  have hc : HasCompactSupport (tri L) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -L) (b := L))
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hnot
    apply hx
    apply tri_eq_zero_of_le_abs hL
    rw [Set.mem_Icc] at hnot
    rcases not_and_or.mp hnot with h | h
    · rw [not_le] at h; rw [abs_of_neg (by linarith)]; linarith
    · rw [not_le] at h; rw [abs_of_pos (by linarith)]; linarith
  exact (tri_continuous L).integrable_of_hasCompactSupport hc

/-! ## The transform of the triangle -/

/-- `∫_0^L (1 − v/L) cos(αv) dv = (1 − cos αL)/(α² L)` for `α ≠ 0`. -/
theorem integral_tri_cos {L α : ℝ} (hL : 0 < L) (hα : α ≠ 0) :
    ∫ v in (0:ℝ)..L, (1 - v / L) * Real.cos (α * v) = (1 - Real.cos (α * L)) / (α ^ 2 * L) := by
  have hderiv : ∀ v ∈ Set.uIcc (0:ℝ) L, HasDerivAt
      (fun v : ℝ => (1 - v / L) * Real.sin (α * v) / α - Real.cos (α * v) / (α ^ 2 * L))
      ((1 - v / L) * Real.cos (α * v)) v := by
    intro v _
    have h1 : HasDerivAt (fun v : ℝ => 1 - v / L) (-(1 / L)) v := by
      simpa using ((hasDerivAt_id v).div_const L).const_sub 1
    have h2 : HasDerivAt (fun v : ℝ => α * v) α v := by
      simpa using (hasDerivAt_id v).const_mul α
    have hs : HasDerivAt (fun v : ℝ => Real.sin (α * v)) (Real.cos (α * v) * α) v :=
      (Real.hasDerivAt_sin _).comp v h2
    have hc : HasDerivAt (fun v : ℝ => Real.cos (α * v)) (-Real.sin (α * v) * α) v :=
      (Real.hasDerivAt_cos _).comp v h2
    have := ((h1.mul hs).div_const α).sub (hc.div_const (α ^ 2 * L))
    refine this.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun v : ℝ => (1 - v / L) * Real.cos (α * v)) volume 0 L :=
    (by fun_prop : Continuous (fun v : ℝ => (1 - v / L) * Real.cos (α * v))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, sub_zero, div_self hL.ne', sub_self, zero_mul,
    zero_div]
  field_simp
  ring

/-- The transform of the triangle at `w ≠ 0`: `(1 − cos 2πLw)/(2π²Lw²)`. -/
theorem fourier_tri {L : ℝ} (hL : 0 < L) {w : ℝ} (hw : w ≠ 0) :
    𝓕 (tri L) w = (((1 - Real.cos (2 * π * L * w)) / (2 * π ^ 2 * L * w ^ 2) : ℝ) : ℂ) := by
  set α : ℝ := 2 * π * w with hα
  have hα0 : α ≠ 0 := by positivity
  rw [Real.fourier_real_eq_integral_exp_smul]
  -- restrict to `[−L, L]`
  have hsupp : ∀ v : ℝ, v ∉ Icc (-L) L →
      Complex.exp (↑(-2 * π * v * w) * Complex.I) • tri L v = 0 := by
    intro v hv
    have : L ≤ |v| := by
      rw [Set.mem_Icc] at hv
      rcases not_and_or.mp hv with h | h
      · rw [not_le] at h; rw [abs_of_neg (by linarith)]; linarith
      · rw [not_le] at h; rw [abs_of_pos (by linarith)]; linarith
    rw [tri_eq_zero_of_le_abs hL this, smul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : (-L) ≤ L)]
  -- split at 0
  have hcont : Continuous (fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) • tri L v) := by
    have := tri_continuous L
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)]
  -- the left half by `v ↦ −v`
  have hleft : ∫ v in (-L)..(0:ℝ), Complex.exp (↑(-2 * π * v * w) * Complex.I) • tri L v
      = ∫ v in (0:ℝ)..L, Complex.exp (↑(2 * π * v * w) * Complex.I) • tri L v := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := L)
      (fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) • tri L v)
    simp only [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    have htri : tri L (-v) = tri L v := by unfold tri; simp
    rw [htri]
    congr 2
    push_cast
    ring
  have hcont' : Continuous (fun v : ℝ => Complex.exp (↑(2 * π * v * w) * Complex.I) • tri L v) := by
    have := tri_continuous L
    fun_prop
  rw [hleft, ← intervalIntegral.integral_add (hcont'.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)]
  -- on `[0, L]` the integrand is `2 cos(αv) (1 − v/L)`
  have hpt : ∀ v ∈ Set.uIcc (0:ℝ) L,
      Complex.exp (↑(2 * π * v * w) * Complex.I) • tri L v
        + Complex.exp (↑(-2 * π * v * w) * Complex.I) • tri L v
        = (((2 * Real.cos (α * v)) * (1 - v / L) : ℝ) : ℂ) := by
    intro v hv
    rw [Set.uIcc_of_le hL.le] at hv
    have hv0 : 0 ≤ v := hv.1
    rw [tri_eq_of_abs_le hL (by rw [abs_of_nonneg hv0]; exact hv.2), abs_of_nonneg hv0]
    have h2c : Complex.exp (↑(2 * π * v * w) * Complex.I)
        + Complex.exp (↑(-2 * π * v * w) * Complex.I)
        = 2 * Complex.cos (↑(α * v)) := by
      have e1 : (↑(-2 * π * v * w) : ℂ) * Complex.I = (-(↑(α * v) : ℂ)) * Complex.I := by
        rw [hα]; push_cast; ring
      have e2 : (↑(2 * π * v * w) : ℂ) * Complex.I = (↑(α * v) : ℂ) * Complex.I := by
        rw [hα]; push_cast; ring
      rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      ring
    simp only [smul_eq_mul]
    rw [← add_mul, h2c, ← Complex.ofReal_cos]
    push_cast
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_ofReal]
  have hI : ∫ v in (0:ℝ)..L, 2 * Real.cos (α * v) * (1 - v / L)
      = 2 * ((1 - Real.cos (α * L)) / (α ^ 2 * L)) := by
    rw [← integral_tri_cos hL hα0, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    ring
  rw [hI]
  congr 1
  rw [hα]
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [show 2 * π * L * w = 2 * π * w * L by ring]
  field_simp

/-! ## Integrability of the transform and inversion at `0` -/

/-- The explicit transform, as a measurable function of `w` (agrees with `𝓕 tri` off `w = 0`). -/
noncomputable def triHat (L : ℝ) (w : ℝ) : ℂ :=
  (((1 - Real.cos (2 * π * L * w)) / (2 * π ^ 2 * L * w ^ 2) : ℝ) : ℂ)

theorem fourier_tri_ae {L : ℝ} (hL : 0 < L) : 𝓕 (tri L) =ᵐ[volume] triHat L := by
  have h0 : ∀ᵐ w : ℝ ∂volume, w ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, Real.volume_singleton]
  filter_upwards [h0] with w hw
  exact fourier_tri hL hw

/-- `|triHat L w| ≤ 2 max(L, 1/(π²L)) / (1 + w²)`. -/
theorem triHat_bound {L : ℝ} (hL : 0 < L) (w : ℝ) :
    ‖triHat L w‖ ≤ (2 * max L (1 / (π ^ 2 * L))) / (1 + w ^ 2) := by
  unfold triHat
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hπ := Real.pi_pos
  have hcos1 : 1 - Real.cos (2 * π * L * w) ≤ 2 := by linarith [Real.neg_one_le_cos (2 * π * L * w)]
  have hcos0 : 0 ≤ 1 - Real.cos (2 * π * L * w) := by linarith [Real.cos_le_one (2 * π * L * w)]
  have hcos2 : 1 - Real.cos (2 * π * L * w) ≤ (2 * π * L * w) ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := 2 * π * L * w)]
  by_cases hw : w = 0
  · subst hw
    simp only [mul_zero, Real.cos_zero, sub_self, zero_div, abs_zero]
    positivity
  have hw2 : 0 < w ^ 2 := by positivity
  have hden : 0 < 2 * π ^ 2 * L * w ^ 2 := by positivity
  rw [abs_of_nonneg (div_nonneg hcos0 hden.le), div_le_div_iff₀ hden (by positivity)]
  have hmaxL : L ≤ max L (1 / (π ^ 2 * L)) := le_max_left _ _
  have hmaxR : 1 / (π ^ 2 * L) ≤ max L (1 / (π ^ 2 * L)) := le_max_right _ _
  by_cases hw1 : w ^ 2 ≤ 1
  · -- use `1 − cos x ≤ x²/2`: value ≤ L ≤ 2L/(1 + w²)
    calc (1 - Real.cos (2 * π * L * w)) * (1 + w ^ 2)
        ≤ ((2 * π * L * w) ^ 2 / 2) * 2 := by
          apply mul_le_mul hcos2 (by linarith) (by positivity) (by positivity)
      _ = 2 * L * (2 * π ^ 2 * L * w ^ 2) := by ring
      _ ≤ 2 * max L (1 / (π ^ 2 * L)) * (2 * π ^ 2 * L * w ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hden.le
          linarith
  · -- use `1 − cos x ≤ 2`: value ≤ 1/(π²Lw²) ≤ 2/(π²L(1 + w²))
    rw [not_le] at hw1
    have hkey : 2 * (1 + w ^ 2) ≤ 2 * max L (1 / (π ^ 2 * L)) * (2 * π ^ 2 * L * w ^ 2) := by
      have h1 : (1 / (π ^ 2 * L)) * (π ^ 2 * L) = 1 := by field_simp
      have h2 : 2 * (1 / (π ^ 2 * L)) * (2 * π ^ 2 * L * w ^ 2) = 4 * w ^ 2 := by
        field_simp
        ring
      have h3 : 2 * (1 + w ^ 2) ≤ 4 * w ^ 2 := by linarith
      calc 2 * (1 + w ^ 2) ≤ 4 * w ^ 2 := h3
        _ = 2 * (1 / (π ^ 2 * L)) * (2 * π ^ 2 * L * w ^ 2) := h2.symm
        _ ≤ 2 * max L (1 / (π ^ 2 * L)) * (2 * π ^ 2 * L * w ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ hden.le
            linarith
    calc (1 - Real.cos (2 * π * L * w)) * (1 + w ^ 2) ≤ 2 * (1 + w ^ 2) := by
          apply mul_le_mul_of_nonneg_right hcos1 (by positivity)
      _ ≤ _ := hkey

theorem triHat_integrable {L : ℝ} (hL : 0 < L) : Integrable (triHat L) := by
  have hmeas : Measurable (triHat L) := by
    unfold triHat
    fun_prop
  refine (integrable_inv_one_add_sq.const_mul (2 * max L (1 / (π ^ 2 * L)))).mono'
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun w => ?_))
  rw [← div_eq_mul_inv]
  exact triHat_bound hL w

theorem fourier_tri_integrable {L : ℝ} (hL : 0 < L) : Integrable (𝓕 (tri L)) :=
  (triHat_integrable hL).congr (fourier_tri_ae hL).symm

/-- Inversion at `0`: `∫ 𝓕 tri = tri 0 = 1`. -/
theorem integral_fourier_tri {L : ℝ} (hL : 0 < L) : ∫ w, 𝓕 (tri L) w = 1 := by
  have h := (tri_integrable hL).fourierInv_fourier_eq (fourier_tri_integrable hL)
    ((tri_continuous L).continuousAt (x := 0))
  rw [tri_zero L, Real.fourierInv_eq] at h
  simpa using h

/-! ## The Fejér mass -/

/-- **`∫_ℝ (1 − cos Lu)/(L u²) du = π`.** -/
theorem integral_fejer {L : ℝ} (hL : 0 < L) : ∫ u, fejer L u = π := by
  have hπ := Real.pi_pos
  -- `∫ 𝓕 tri = ∫ triHat = ∫ 2 fejer L (2πw) dw` as real numbers
  have h1 : ∫ w, 𝓕 (tri L) w = ((∫ w, 2 * fejer L (2 * π * w) : ℝ) : ℂ) := by
    rw [integral_congr_ae (fourier_tri_ae hL), ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    unfold triHat fejer
    congr 1
    by_cases hw : w = 0
    · subst hw; simp
    · have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
      have hπ0 : π ≠ 0 := Real.pi_ne_zero
      rw [show L * (2 * π * w) = 2 * π * L * w by ring]
      field_simp
  rw [integral_fourier_tri hL] at h1
  have h2 : (∫ w, 2 * fejer L (2 * π * w)) = 1 := by
    have := h1
    exact_mod_cast this.symm
  rw [integral_const_mul, MeasureTheory.Measure.integral_comp_mul_left (fejer L) (2 * π)] at h2
  rw [abs_of_pos (by positivity : (0:ℝ) < (2 * π)⁻¹), smul_eq_mul] at h2
  have hπ0 : π ≠ 0 := Real.pi_ne_zero
  field_simp at h2
  linarith

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.fourier_tri
#print axioms CriticalLinePhasor.ContourArgument.integral_fourier_tri
#print axioms CriticalLinePhasor.ContourArgument.integral_fejer
