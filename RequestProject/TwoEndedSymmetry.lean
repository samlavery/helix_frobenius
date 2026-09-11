import RequestProject.TwoEndedFiber

/-!
# The two-ended grown fiber: functional-equation symmetry and axis reality (ledger 704)

* `feFactor_mul_feFactor_one_sub` — `A(s) A(1 − s) = 1` on the strip (reflection formula for `Γ`, double angle);
* `chiEta_mul_chiEta_one_sub`, **`twoEnded_one_sub`** — the stages satisfy η's functional equation exactly:
  `G_Z(1 − s) = χ_η(1 − s) G_Z(s)`;
* `chiEta_conj`, `chiEta_norm_one` — conjugation symmetry, hence `|χ_η| = 1` on the axis (there `1 − s = s̄`);
* **`twoEnded_conj_axis`, `twoEnded_sq_axis`, `twoEnded_axis_real`** — axis reality: on the axis
  `conj G_Z = G_Z / χ_η`, `G_Z² = χ_η ‖G_Z‖²`, and a unimodular rotation makes `G_Z` real.
-/

open Complex Filter Topology Set
open CriticalLinePhasor.CarrierHeadFiniteFiber

namespace CriticalLinePhasor.GrownFiber

/-! ### The functional-equation symmetry of the stages -/

theorem sin_pi_mul_ne_zero {s : ℂ} (hs : s ∈ strip) : Complex.sin (Real.pi * s) ≠ 0 := by
  intro h
  rw [Complex.sin_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs' : s = (k : ℂ) := by
    have : (Real.pi : ℂ) * s = (Real.pi : ℂ) * (k : ℂ) := by rw [hk]; ring
    exact mul_left_cancel₀ hπ this
  have hre := congrArg Complex.re hs'
  simp at hre
  have h0 := hs.1; have h1 := hs.2
  have hk1 : (0 : ℝ) < k := by linarith
  have hk2 : (k : ℝ) < 1 := by linarith
  have hk3 : 0 < k := by exact_mod_cast hk1
  have hk4 : k < 1 := by exact_mod_cast hk2
  omega

/-- `A(s) A(1 − s) = 1` on the strip. -/
theorem feFactor_mul_feFactor_one_sub {s : ℂ} (hs : s ∈ strip) : feFactor s * feFactor (1 - s) = 1 := by
  unfold feFactor
  have hbase : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpow : (2 * (Real.pi : ℂ)) ^ (-s) * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) = (2 * (Real.pi : ℂ))⁻¹ := by
    rw [← Complex.cpow_add _ _ hbase, show -s + -(1 - s) = (-1 : ℂ) by ring, Complex.cpow_neg_one]
  have hΓ := Complex.Gamma_mul_Gamma_one_sub s
  have hcos : Complex.cos (Real.pi * (1 - s) / 2) = Complex.sin (Real.pi * s / 2) := by
    rw [show (Real.pi : ℂ) * (1 - s) / 2 = Real.pi / 2 - Real.pi * s / 2 by ring, Complex.cos_pi_div_two_sub]
  have hsin2 : Complex.sin (Real.pi * s) = 2 * Complex.sin (Real.pi * s / 2) * Complex.cos (Real.pi * s / 2) := by
    rw [← Complex.sin_two_mul]; congr 1; ring
  have hsin : Complex.sin (Real.pi * s) ≠ 0 := sin_pi_mul_ne_zero hs
  have hs2 : Complex.sin (Real.pi * s / 2) ≠ 0 := by
    intro h; apply hsin; rw [hsin2, h]; ring
  have hc2 : Complex.cos (Real.pi * s / 2) ≠ 0 := by
    intro h; apply hsin; rw [hsin2, h]; ring
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  calc 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos (Real.pi * s / 2) *
        (2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Complex.Gamma (1 - s) * Complex.cos (Real.pi * (1 - s) / 2))
      = 4 * ((2 * (Real.pi : ℂ)) ^ (-s) * (2 * (Real.pi : ℂ)) ^ (-(1 - s))) *
          (Complex.Gamma s * Complex.Gamma (1 - s)) *
          (Complex.cos (Real.pi * s / 2) * Complex.cos (Real.pi * (1 - s) / 2)) := by ring
    _ = 4 * (2 * (Real.pi : ℂ))⁻¹ * (Real.pi / Complex.sin (Real.pi * s)) *
          (Complex.cos (Real.pi * s / 2) * Complex.sin (Real.pi * s / 2)) := by rw [hpow, hΓ, hcos]
    _ = 1 := by
        rw [hsin2]
        field_simp
        ring

theorem chiEta_mul_chiEta_one_sub {s : ℂ} (hs : s ∈ strip) : chiEta s * chiEta (1 - s) = 1 := by
  have h1s := one_sub_mem_strip hs
  have hA := feFactor_mul_feFactor_one_sub hs
  have hA1 := feFactor_ne_zero hs
  have hA2 := feFactor_ne_zero h1s
  have hc1 : (1 - (2 : ℂ) ^ s) ≠ 0 := sub_ne_zero.mpr (two_cpow_ne_one hs.1.ne').symm
  have hc2 : (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) ≠ 0 := sub_ne_zero.mpr (two_cpow_ne_one h1s.1.ne').symm
  calc chiEta s * chiEta (1 - s)
      = ((1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * (1 - (2 : ℂ) ^ s)) /
          (((1 - (2 : ℂ) ^ s) * feFactor s) * ((1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * feFactor (1 - s))) := by
        unfold chiEta
        rw [show (1 : ℂ) - (1 - s) = s by ring, div_mul_div_comm]
    _ = 1 / (feFactor s * feFactor (1 - s)) := by
        field_simp
    _ = 1 := by rw [hA]; simp

/-- **The stages satisfy η's functional equation exactly.** -/
theorem twoEnded_one_sub (Z : ℝ) {s : ℂ} (hs : s ∈ strip) :
    twoEnded Z (1 - s) = chiEta (1 - s) * twoEnded Z s := by
  unfold twoEnded
  rw [show (1 : ℂ) - (1 - s) = s by ring]
  have h := chiEta_mul_chiEta_one_sub hs
  linear_combination (-(finiteFiber Z (1 - s))) * h

/-! ### Conjugation symmetry and unimodularity on the axis -/

theorem cpow_real_conj {x : ℝ} (hx : 0 < x) (n : ℂ) :
    (x : ℂ) ^ (starRingEnd ℂ n) = starRingEnd ℂ ((x : ℂ) ^ n) := by
  rw [Complex.cpow_conj _ _ (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm),
    Complex.conj_ofReal]

theorem conj_two : (starRingEnd ℂ) (2 : ℂ) = 2 := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]

theorem feFactor_conj (s : ℂ) : feFactor (starRingEnd ℂ s) = starRingEnd ℂ (feFactor s) := by
  unfold feFactor
  have h2π : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have e1 : (2 * (Real.pi : ℂ)) ^ (-(starRingEnd ℂ s)) = starRingEnd ℂ ((2 * (Real.pi : ℂ)) ^ (-s)) := by
    rw [h2π, ← map_neg, cpow_real_conj (by positivity)]
  have e2 : Complex.cos (Real.pi * (starRingEnd ℂ s) / 2) = starRingEnd ℂ (Complex.cos (Real.pi * s / 2)) := by
    rw [← Complex.cos_conj]
    congr 1
    rw [map_div₀, map_mul, Complex.conj_ofReal, conj_two]
  rw [e1, Complex.Gamma_conj, e2, map_mul, map_mul, map_mul, conj_two]

theorem chiEta_conj (s : ℂ) : chiEta (starRingEnd ℂ s) = starRingEnd ℂ (chiEta s) := by
  unfold chiEta
  have e1 : (2 : ℂ) ^ ((1 : ℂ) - starRingEnd ℂ s) = starRingEnd ℂ ((2 : ℂ) ^ ((1 : ℂ) - s)) := by
    rw [show (1 : ℂ) - starRingEnd ℂ s = starRingEnd ℂ (1 - s) by simp,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, cpow_real_conj (by norm_num)]
  have e2 : (2 : ℂ) ^ (starRingEnd ℂ s) = starRingEnd ℂ ((2 : ℂ) ^ s) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, cpow_real_conj (by norm_num)]
  rw [e1, e2, feFactor_conj]
  simp [map_div₀, map_mul, map_sub]

theorem conj_eq_one_sub_of_re_half {s : ℂ} (h : s.re = 1 / 2) : starRingEnd ℂ s = 1 - s := by
  apply Complex.ext
  · simp [h]; norm_num
  · simp

/-- `|χ_η| = 1` on the axis. -/
theorem chiEta_norm_one {s : ℂ} (hs : s ∈ strip) (h : s.re = 1 / 2) : ‖chiEta s‖ = 1 := by
  have h1 := chiEta_mul_chiEta_one_sub hs
  rw [← conj_eq_one_sub_of_re_half h, chiEta_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h1
  have h2 : ‖chiEta s‖ ^ 2 = 1 := by exact_mod_cast h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

theorem chiEta_mul_conj_axis {s : ℂ} (hs : s ∈ strip) (h : s.re = 1 / 2) :
    chiEta s * starRingEnd ℂ (chiEta s) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, chiEta_norm_one hs h]
  norm_num

/-! ### Axis reality -/

/-- On the axis the two ends are conjugates: `F_Z(1 − s) = conj F_Z(s)`. -/
theorem finiteFiber_one_sub_axis (Z : ℝ) {s : ℂ} (h : s.re = 1 / 2) :
    finiteFiber Z (1 - s) = starRingEnd ℂ (finiteFiber Z s) := by
  rw [← conj_eq_one_sub_of_re_half h, finiteFiber_conj]

/-- **Axis reality, conjugation form:** `conj G_Z(s) = G_Z(s) / χ_η(s)` on the axis. -/
theorem twoEnded_conj_axis (Z : ℝ) {s : ℂ} (hs : s ∈ strip) (h : s.re = 1 / 2) :
    starRingEnd ℂ (twoEnded Z s) = twoEnded Z s / chiEta s := by
  have hc := chiEta_norm_one hs h
  have hc0 : chiEta s ≠ 0 := by intro h0; rw [h0, norm_zero] at hc; norm_num at hc
  have hcc : starRingEnd ℂ (chiEta s) = (chiEta s)⁻¹ := eq_inv_of_mul_eq_one_right (chiEta_mul_conj_axis hs h)
  unfold twoEnded
  rw [map_add, map_mul, hcc, finiteFiber_one_sub_axis Z h, Complex.conj_conj]
  field_simp
  ring

/-- **Axis reality, square form:** `G_Z(s)² = χ_η(s) ‖G_Z(s)‖²` on the axis — the stage's phase on the axis is half
that of `χ_η`, fixed by the two ends. -/
theorem twoEnded_sq_axis (Z : ℝ) {s : ℂ} (hs : s ∈ strip) (h : s.re = 1 / 2) :
    twoEnded Z s ^ 2 = chiEta s * ((‖twoEnded Z s‖ ^ 2 : ℝ) : ℂ) := by
  have hc := chiEta_norm_one hs h
  have hc0 : chiEta s ≠ 0 := by intro h0; rw [h0, norm_zero] at hc; norm_num at hc
  have h1 := twoEnded_conj_axis Z hs h
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, h1]
  field_simp

/-- **Axis reality, rotation form:** a unimodular rotation makes the stage real on the axis. -/
theorem twoEnded_axis_real (Z : ℝ) {s : ℂ} (hs : s ∈ strip) (h : s.re = 1 / 2) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ (ω * twoEnded Z s).im = 0 := by
  have hc := chiEta_norm_one hs h
  have hc0 : chiEta s ≠ 0 := by intro h0; rw [h0, norm_zero] at hc; norm_num at hc
  set ω : ℂ := Complex.exp (-(Complex.log (chiEta s)) / 2) with hω
  have hω2 : ω ^ 2 = (chiEta s)⁻¹ := by
    rw [hω, ← Complex.exp_nat_mul,
      show ((2 : ℕ) : ℂ) * (-(Complex.log (chiEta s)) / 2) = -(Complex.log (chiEta s)) by push_cast; ring,
      Complex.exp_neg, Complex.exp_log hc0]
  have hωn : ‖ω‖ = 1 := by
    rw [hω, Complex.norm_exp]
    simp [Complex.log_re, hc]
  refine ⟨ω, hωn, ?_⟩
  have hsq : (ω * twoEnded Z s) ^ 2 = ((‖twoEnded Z s‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, hω2, twoEnded_sq_axis Z hs h, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  set z := ω * twoEnded Z s with hz
  have him : (z ^ 2).im = 0 := by rw [hsq, Complex.ofReal_im]
  have hre : 0 ≤ (z ^ 2).re := by rw [hsq, Complex.ofReal_re]; positivity
  rw [pow_two, Complex.mul_im] at him
  rw [pow_two, Complex.mul_re] at hre
  by_contra hne
  have h2 : z.re * z.im = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · rw [h3] at hre
    have := mul_self_pos.mpr hne
    linarith
  · exact hne h3

end CriticalLinePhasor.GrownFiber

#print axioms CriticalLinePhasor.GrownFiber.twoEnded_one_sub
#print axioms CriticalLinePhasor.GrownFiber.chiEta_norm_one
#print axioms CriticalLinePhasor.GrownFiber.twoEnded_sq_axis
#print axioms CriticalLinePhasor.GrownFiber.twoEnded_axis_real
