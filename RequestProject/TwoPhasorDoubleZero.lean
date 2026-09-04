import Mathlib

/-!
# Two-phasor banks: when the real part has a double zero (ledger 576 → theorem)

A bank of two phasors with FIXED unit amplitudes and FIXED distinct positive rates `ω₁ > ω₂ > 0`,
read on the real line: `twoPhasor ω₁ ω₂ x = Re(e^{iω₁x} + e^{iω₂x}) = cos(ω₁x) + cos(ω₂x)`.

With the half-sum `σ = (ω₁+ω₂)/2` and half-difference `δ = (ω₁−ω₂)/2` clocks,

* `twoPhasor_double_zero_iff`: value and derivative vanish at `x` **iff** both clocks are at a
  quarter turn, `cos(σx) = 0 ∧ cos(δx) = 0`;
* `twoPhasor_exists_double_zero_iff`: a double zero exists somewhere **iff** the rate ratio is a
  ratio of odd integers, `∃ k m : ℤ, (2k+1)·δ = (2m+1)·σ`;
* `twoPhasor_two_one_double_zero`: rates `2, 1` (ratio `σ/δ = 3`) — a double zero at `x = π`.

So "positive fixed amplitudes, distinct rates, one phasor introduced at a time" does not forbid a
double zero; the ARITHMETIC OF THE RATES decides. The lanes cancel exactly at `x = π` and so does the
derivative. This is the compiled form of the block encountered in ledger 576.
-/

namespace CriticalLinePhasor.TwoPhasor

open Real

/-- The two-phasor bank on the line: `Re(e^{iω₁x} + e^{iω₂x})`. -/
noncomputable def twoPhasor (ω₁ ω₂ x : ℝ) : ℝ := Real.cos (ω₁ * x) + Real.cos (ω₂ * x)

theorem twoPhasor_eq_re (ω₁ ω₂ x : ℝ) :
    twoPhasor ω₁ ω₂ x = (Complex.exp ((ω₁ * x : ℝ) * Complex.I) + Complex.exp ((ω₂ * x : ℝ) * Complex.I)).re := by
  simp only [twoPhasor, Complex.add_re, Complex.exp_ofReal_mul_I_re]

/-- The derivative of the bank. -/
theorem hasDerivAt_twoPhasor (ω₁ ω₂ x : ℝ) :
    HasDerivAt (twoPhasor ω₁ ω₂) (-(ω₁ * Real.sin (ω₁ * x)) - ω₂ * Real.sin (ω₂ * x)) x := by
  have h1 : HasDerivAt (fun x => Real.cos (ω₁ * x)) (-Real.sin (ω₁ * x) * ω₁) x :=
    ((hasDerivAt_id x).const_mul ω₁).cos |>.congr_deriv (by simp)
  have h2 : HasDerivAt (fun x => Real.cos (ω₂ * x)) (-Real.sin (ω₂ * x) * ω₂) x :=
    ((hasDerivAt_id x).const_mul ω₂).cos |>.congr_deriv (by simp)
  exact (h1.add h2).congr_deriv (by ring)

theorem deriv_twoPhasor (ω₁ ω₂ x : ℝ) :
    deriv (twoPhasor ω₁ ω₂) x = -(ω₁ * Real.sin (ω₁ * x)) - ω₂ * Real.sin (ω₂ * x) :=
  (hasDerivAt_twoPhasor ω₁ ω₂ x).deriv

/-- Product form: `cos(ω₁x) + cos(ω₂x) = 2 cos(σx) cos(δx)`. -/
theorem twoPhasor_eq_prod (ω₁ ω₂ x : ℝ) :
    twoPhasor ω₁ ω₂ x
      = 2 * Real.cos ((ω₁ + ω₂) / 2 * x) * Real.cos ((ω₁ - ω₂) / 2 * x) := by
  rw [twoPhasor, Real.cos_add_cos]
  congr 2 <;> ring

/-- Derivative in the two clocks: `f′ = −2σ sin(σx) cos(δx) − 2δ cos(σx) sin(δx)`. -/
theorem deriv_twoPhasor_prod (ω₁ ω₂ x : ℝ) :
    deriv (twoPhasor ω₁ ω₂) x
      = -(2 * ((ω₁ + ω₂) / 2) * Real.sin ((ω₁ + ω₂) / 2 * x) * Real.cos ((ω₁ - ω₂) / 2 * x))
        - 2 * ((ω₁ - ω₂) / 2) * Real.cos ((ω₁ + ω₂) / 2 * x) * Real.sin ((ω₁ - ω₂) / 2 * x) := by
  rw [deriv_twoPhasor]
  have hA : ω₁ * x = (ω₁ + ω₂) / 2 * x + (ω₁ - ω₂) / 2 * x := by ring
  have hB : ω₂ * x = (ω₁ + ω₂) / 2 * x - (ω₁ - ω₂) / 2 * x := by ring
  rw [hA, hB, Real.sin_add, Real.sin_sub]
  ring

/-- **Double zero ⟺ both clocks at a quarter turn** (rates distinct and positive). -/
theorem twoPhasor_double_zero_iff {ω₁ ω₂ : ℝ} (h : ω₂ < ω₁) (h2 : 0 < ω₂) (x : ℝ) :
    (twoPhasor ω₁ ω₂ x = 0 ∧ deriv (twoPhasor ω₁ ω₂) x = 0)
      ↔ (Real.cos ((ω₁ + ω₂) / 2 * x) = 0 ∧ Real.cos ((ω₁ - ω₂) / 2 * x) = 0) := by
  rw [twoPhasor_eq_prod, deriv_twoPhasor_prod]
  set σ := (ω₁ + ω₂) / 2 with hσ
  set δ := (ω₁ - ω₂) / 2 with hδ
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  constructor
  · rintro ⟨hf, hf'⟩
    have hprod : Real.cos (σ * x) = 0 ∨ Real.cos (δ * x) = 0 := by
      rcases mul_eq_zero.mp hf with h0 | h0
      · rcases mul_eq_zero.mp h0 with h00 | h00
        · norm_num at h00
        · exact Or.inl h00
      · exact Or.inr h0
    rcases hprod with hc | hc
    · refine ⟨hc, ?_⟩
      rw [hc] at hf'
      have hs : Real.sin (σ * x) ≠ 0 := by
        intro hs
        have := Real.sin_sq_add_cos_sq (σ * x)
        rw [hs, hc] at this
        norm_num at this
      have : -(2 * σ * Real.sin (σ * x) * Real.cos (δ * x)) = 0 := by linarith [hf']
      rcases mul_eq_zero.mp (neg_eq_zero.mp this) with h0 | h0
      · rcases mul_eq_zero.mp h0 with h00 | h00
        · rcases mul_eq_zero.mp h00 with h000 | h000
          · norm_num at h000
          · exact absurd h000 hσ0.ne'
        · exact absurd h00 hs
      · exact h0
    · refine ⟨?_, hc⟩
      rw [hc] at hf'
      have hs : Real.sin (δ * x) ≠ 0 := by
        intro hs
        have := Real.sin_sq_add_cos_sq (δ * x)
        rw [hs, hc] at this
        norm_num at this
      have : 2 * δ * Real.cos (σ * x) * Real.sin (δ * x) = 0 := by linarith [hf']
      rcases mul_eq_zero.mp this with h0 | h0
      · rcases mul_eq_zero.mp h0 with h00 | h00
        · rcases mul_eq_zero.mp h00 with h000 | h000
          · norm_num at h000
          · exact absurd h000 hδ0.ne'
        · exact h00
      · exact absurd h0 hs
  · rintro ⟨hc1, hc2⟩
    rw [hc1, hc2]
    constructor <;> ring

/-- **A double zero exists ⟺ the rate ratio is a ratio of odd integers**:
`∃ k m : ℤ, (2k+1)·δ = (2m+1)·σ` with `σ = (ω₁+ω₂)/2`, `δ = (ω₁−ω₂)/2`. -/
theorem twoPhasor_exists_double_zero_iff {ω₁ ω₂ : ℝ} (h : ω₂ < ω₁) (h2 : 0 < ω₂) :
    (∃ x, twoPhasor ω₁ ω₂ x = 0 ∧ deriv (twoPhasor ω₁ ω₂) x = 0)
      ↔ ∃ k m : ℤ, (2 * k + 1 : ℝ) * ((ω₁ - ω₂) / 2) = (2 * m + 1 : ℝ) * ((ω₁ + ω₂) / 2) := by
  have hσ0 : 0 < (ω₁ + ω₂) / 2 := by linarith
  have hδ0 : 0 < (ω₁ - ω₂) / 2 := by linarith
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hc1, hc2⟩ := (twoPhasor_double_zero_iff h h2 x).mp hx
    obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hc1
    obtain ⟨m, hm⟩ := Real.cos_eq_zero_iff.mp hc2
    refine ⟨k, m, ?_⟩
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    -- σx = (2k+1)π/2, δx = (2m+1)π/2 ⟹ (2k+1)δ = (2m+1)σ
    have e1 : (2 * k + 1 : ℝ) * Real.pi / 2 * ((ω₁ - ω₂) / 2)
        = (ω₁ + ω₂) / 2 * x * ((ω₁ - ω₂) / 2) := by rw [← hk]
    have e2 : (2 * m + 1 : ℝ) * Real.pi / 2 * ((ω₁ + ω₂) / 2)
        = (ω₁ - ω₂) / 2 * x * ((ω₁ + ω₂) / 2) := by rw [← hm]
    have e3 : (2 * k + 1 : ℝ) * Real.pi / 2 * ((ω₁ - ω₂) / 2)
        = (2 * m + 1 : ℝ) * Real.pi / 2 * ((ω₁ + ω₂) / 2) := by
      rw [e1, e2]; ring
    have e4 : Real.pi * ((2 * k + 1 : ℝ) * ((ω₁ - ω₂) / 2) - (2 * m + 1 : ℝ) * ((ω₁ + ω₂) / 2)) = 0 := by
      linear_combination 2 * e3
    rcases mul_eq_zero.mp e4 with h0 | h0
    · exact absurd h0 hpi.ne'
    · linarith
  · rintro ⟨k, m, hkm⟩
    have hσne : (ω₁ + ω₂) / 2 ≠ 0 := hσ0.ne'
    refine ⟨(2 * k + 1 : ℝ) * Real.pi / 2 / ((ω₁ + ω₂) / 2), ?_⟩
    rw [twoPhasor_double_zero_iff h h2]
    constructor
    · rw [Real.cos_eq_zero_iff]
      exact ⟨k, by rw [mul_div_cancel₀ _ hσne]⟩
    · rw [Real.cos_eq_zero_iff]
      refine ⟨m, ?_⟩
      calc (ω₁ - ω₂) / 2 * ((2 * k + 1 : ℝ) * Real.pi / 2 / ((ω₁ + ω₂) / 2))
          = ((2 * k + 1 : ℝ) * ((ω₁ - ω₂) / 2)) * Real.pi / 2 / ((ω₁ + ω₂) / 2) := by ring
        _ = ((2 * m + 1 : ℝ) * ((ω₁ + ω₂) / 2)) * Real.pi / 2 / ((ω₁ + ω₂) / 2) := by rw [hkm]
        _ = (2 * m + 1 : ℝ) * Real.pi / 2 := by
          rw [show ((2 * m + 1 : ℝ) * ((ω₁ + ω₂) / 2)) * Real.pi / 2 / ((ω₁ + ω₂) / 2)
              = (2 * m + 1 : ℝ) * Real.pi / 2 * (((ω₁ + ω₂) / 2) / ((ω₁ + ω₂) / 2)) by ring,
            div_self hσne, mul_one]

/-- **The instance of ledger 576:** rates `2, 1`, fixed unit amplitudes — a double zero at `x = π`. -/
theorem twoPhasor_two_one_double_zero :
    twoPhasor 2 1 Real.pi = 0 ∧ deriv (twoPhasor 2 1) Real.pi = 0 := by
  rw [twoPhasor_double_zero_iff (by norm_num) (by norm_num)]
  constructor
  · rw [Real.cos_eq_zero_iff]
    exact ⟨1, by push_cast; ring⟩
  · rw [Real.cos_eq_zero_iff]
    exact ⟨0, by push_cast; ring⟩

#print axioms twoPhasor_double_zero_iff
#print axioms twoPhasor_exists_double_zero_iff
#print axioms twoPhasor_two_one_double_zero

end CriticalLinePhasor.TwoPhasor
