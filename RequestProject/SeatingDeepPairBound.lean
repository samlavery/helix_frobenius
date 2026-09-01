import RequestProject.SeatingMassDisk

/-!
# The deep-pair influence bound: divers are mass-harmless

The missing regime of the disk-law suite.  A mirror pair of depth
`b = β − ½` with `|b| ≥ 1` may hold a channel point INSIDE its depth-disk —
there its mass contribution is negative — but never by more than
`32/(b² + Δ²)` (`Δ` = height offset): the Poisson influence of a deep zero
DECAYS quadratically in its distance.  This is the (c)-regime brick of the
three-regime escort law: divers that plunge (`b → ∞`) or recede (`Δ → ∞`)
contribute vanishing negative mass, so stage-mass positivity needs only the
shallow and middle bands — never control of the deep field.

Mechanism: `|σ−½| ≤ ½ ≤ |b|/2` pins both shifted denominators at
`(b²+Δ²)/4`, so `32·D₁D₂ ≥ 2(b²+Δ²)² ≥ 2(b²−σ²−Δ²)(b²+Δ²)`.

No `sorry`, no `axiom`.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- **Deep pairs are mass-harmless**: for a pair of depth `|β−½| ≥ 1` and a
point of channel width (`|σ−½| ≤ ½`), the pair's seat-mass contribution is
bounded below by `−32/(depth² + height-offset²)` — quadratic influence
decay, valid inside or outside the depth-disk. -/
theorem deep_pair_mass_lower_bound (β γ : ℝ) {s : ℂ}
    (hdeep : 1 ≤ |β - 1/2|) (hσ : |s.re - 1/2| ≤ 1/2)
    (h1 : s ≠ β + γ * I) (h2 : s ≠ (1 - β) + γ * I) :
    -(32 / ((β - 1/2)^2 + (s.im - γ)^2))
      ≤ ((s - (β + γ * I))⁻¹ + (s - ((1 - β) + γ * I))⁻¹).re
        / (s.re - 1/2) := by
  set b : ℝ := β - 1/2 with hb
  set Δ : ℝ := s.im - γ with hΔ
  set σh : ℝ := s.re - 1/2 with hσh
  have hb2 : 1 ≤ b^2 := by
    nlinarith [sq_abs b, hdeep, abs_nonneg b]
  have hRpos : 0 < b^2 + Δ^2 := by nlinarith [sq_nonneg Δ]
  -- quarter floors for the shifted denominators
  have hquartp : (b^2 + Δ^2)/4 ≤ (σh - b)^2 + Δ^2 := by
    rcases abs_le.mp hσ with ⟨hσlo, hσhi⟩
    rcases le_or_gt 0 b with hbpos | hbneg
    · have hb1 : 1 ≤ b := by rwa [abs_of_nonneg hbpos] at hdeep
      nlinarith [sq_nonneg (2*σh - b),
        mul_nonneg (by linarith : (0:ℝ) ≤ b)
          (by linarith : (0:ℝ) ≤ b - 2*σh), sq_nonneg Δ]
    · have habs : |b| = -b := abs_of_neg hbneg
      have hb1 : b ≤ -1 := by
        rw [habs] at hdeep
        linarith
      nlinarith [sq_nonneg (2*σh - b),
        mul_nonneg (by linarith : (0:ℝ) ≤ -b)
          (by linarith : (0:ℝ) ≤ 2*σh - b), sq_nonneg Δ]
  have hquartm : (b^2 + Δ^2)/4 ≤ (σh + b)^2 + Δ^2 := by
    rcases abs_le.mp hσ with ⟨hσlo, hσhi⟩
    rcases le_or_gt 0 b with hbpos | hbneg
    · have hb1 : 1 ≤ b := by rwa [abs_of_nonneg hbpos] at hdeep
      nlinarith [sq_nonneg (2*σh + b),
        mul_nonneg (by linarith : (0:ℝ) ≤ b)
          (by linarith : (0:ℝ) ≤ b + 2*σh), sq_nonneg Δ]
    · have habs : |b| = -b := abs_of_neg hbneg
      have hb1 : b ≤ -1 := by
        rw [habs] at hdeep
        linarith
      nlinarith [sq_nonneg (2*σh + b),
        mul_nonneg (by linarith : (0:ℝ) ≤ -b)
          (by linarith : (0:ℝ) ≤ -b - 2*σh), sq_nonneg Δ]
  have hD1pos : 0 < (σh - b)^2 + Δ^2 := lt_of_lt_of_le (by linarith) hquartp
  have hD2pos : 0 < (σh + b)^2 + Δ^2 := lt_of_lt_of_le (by linarith) hquartm
  have hDpos : 0 < ((σh - b)^2 + Δ^2) * ((σh + b)^2 + Δ^2) :=
    mul_pos hD1pos hD2pos
  -- the closed form, folded into (b, Δ, σh)
  have hD1eq : (s.re - β)^2 + (s.im - γ)^2 = (σh - b)^2 + Δ^2 := by
    rw [hb, hΔ, hσh]; ring
  have hD2eq : (s.re - (1 - β))^2 + (s.im - γ)^2 = (σh + b)^2 + Δ^2 := by
    rw [hb, hΔ, hσh]; ring
  rw [mirror_pair_floor_law β γ h1 h2, hD1eq, hD2eq, ← hσh, ← hΔ, ← hb]
  rcases eq_or_ne σh 0 with hz | hz
  · -- on the line: the mass expression collapses to 0, the bound is ≤ 0
    rw [hz]
    simp only [mul_zero, zero_mul, zero_div, div_zero]
    have h32 : 0 < 32 / (b^2 + Δ^2) :=
      div_pos (by norm_num) hRpos
    linarith
  · -- cancel the odd prefactor
    have hfold : 2 * σh * (σh^2 + Δ^2 - b^2)
          / (((σh - b)^2 + Δ^2) * ((σh + b)^2 + Δ^2)) / σh
        = 2 * (σh^2 + Δ^2 - b^2)
          / (((σh - b)^2 + Δ^2) * ((σh + b)^2 + Δ^2)) := by
      rw [div_div,
        show 2 * σh * (σh^2 + Δ^2 - b^2)
            = σh * (2 * (σh^2 + Δ^2 - b^2)) by ring,
        show (((σh - b)^2 + Δ^2) * ((σh + b)^2 + Δ^2)) * σh
            = σh * (((σh - b)^2 + Δ^2) * ((σh + b)^2 + Δ^2)) by ring]
      exact mul_div_mul_left _ _ hz
    rw [hfold]
    rcases le_or_gt 0 (σh^2 + Δ^2 - b^2) with hN | hN
    · -- outside the disk: nonneg vs nonpos bound
      have hpos : 0 ≤ 2 * (σh^2 + Δ^2 - b^2)
          / (((σh - b)^2 + Δ^2) * ((σh + b)^2 + Δ^2)) :=
        div_nonneg (by linarith) hDpos.le
      have h32 : 0 < 32 / (b^2 + Δ^2) := div_pos (by norm_num) hRpos
      linarith
    · -- inside the disk: cross-multiply against the quarter floors
      have hprod : (b^2 + Δ^2)^2 / 16
          ≤ ((σh - b)^2 + Δ^2) * ((σh + b)^2 + Δ^2) := by
        calc (b^2 + Δ^2)^2 / 16
            = ((b^2 + Δ^2)/4) * ((b^2 + Δ^2)/4) := by ring
          _ ≤ _ := mul_le_mul hquartp hquartm (by linarith) (by linarith)
      have haux : 0 ≤ (b^2 + Δ^2) * (σh^2 + 2*Δ^2) :=
        mul_nonneg hRpos.le (by positivity)
      have hid : 2 * (σh^2 + Δ^2 - b^2) * (b^2 + Δ^2)
          = 2 * ((b^2 + Δ^2) * (σh^2 + 2*Δ^2)) - 2 * (b^2 + Δ^2)^2 := by
        ring
      rw [show -(32 / (b^2 + Δ^2)) = (-32) / (b^2 + Δ^2) by ring,
        div_le_div_iff₀ hRpos hDpos]
      nlinarith [hprod, haux, hid]

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.deep_pair_mass_lower_bound
