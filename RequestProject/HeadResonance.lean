import RequestProject.WarpLedger

/-!
# The head resonance, proved; the clocks removed from the drift question (ledger 947)

Sam, 2026-09-30: "ok, prove it" (after ledger 946: the warp ledger's alternation is carried by the clock at the head,
`log p = θ′`, which gains a half-turn every gap).

* `clock_increments_alternate` — **the head clock alternates.** If two consecutive gaps each carry a clock of frequency
  `ω` through a half-turn up to `ε` (`|ω·gap − π| ≤ ε`, `ε < π/2`), its increments across the two gaps have OPPOSITE
  signs, unless the first gap's midpoint phase lies within `tan ε` of a node (`|cos| ≤ tan ε`).
* `clock_integral_abs_le`, `clockSum_integral_abs_le` — **a clock never drifts**: `|∫₀ᵀ sin(ωt)| ≤ 2/ω`, so a finite
  bank of clocks has a running integral bounded uniformly in `T`.
* `noOffline_of_residual_not_linearly_behind` — **remove the clocks first**: for ANY finite bank of clocks, door 677
  needs only that the registered ledger MINUS that bank is not linearly behind at arbitrarily large heights.
-/

open Real Filter Topology Finset
open CriticalLinePhasor.ResidueJump DoubleCoshProgram

namespace CriticalLinePhasor.HeadResonance

/-- **A clock never drifts.** -/
theorem clock_integral_abs_le {ω : ℝ} (hω : 0 < ω) (T : ℝ) :
    |∫ t in (0:ℝ)..T, Real.sin (ω * t)| ≤ 2 / ω := by
  have h : ∫ t in (0:ℝ)..T, Real.sin (ω * t) = (1 - Real.cos (ω * T)) / ω := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hω.ne', integral_sin]
    simp only [smul_eq_mul, mul_zero, Real.cos_zero]
    field_simp
  rw [h, abs_div, abs_of_pos hω]
  gcongr
  have h1 := Real.neg_one_le_cos (ω * T)
  have h2 := Real.cos_le_one (ω * T)
  rw [abs_le]; constructor <;> linarith

/-- **A finite bank of clocks never drifts**: its running integral is bounded uniformly in the height. -/
theorem clockSum_integral_abs_le {ι : Type*} (F : Finset ι) (a ω : ι → ℝ) (hω : ∀ j ∈ F, 0 < ω j) (T : ℝ) :
    |∫ t in (0:ℝ)..T, ∑ j ∈ F, a j * Real.sin (ω j * t)| ≤ ∑ j ∈ F, |a j| * (2 / ω j) := by
  rw [intervalIntegral.integral_finsetSum (fun j _ =>
    (by fun_prop : Continuous fun t => a j * Real.sin (ω j * t)).intervalIntegrable _ _)]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
  rw [intervalIntegral.integral_const_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (clock_integral_abs_le (hω j hj) T) (abs_nonneg _)

/-- **The head clock alternates.** A clock carried through a half-turn (up to `ε`) by each of two consecutive gaps has
increments of opposite sign across them, unless the first gap's midpoint phase is within `tan ε` of a node. -/
theorem clock_increments_alternate {ω t₀ t₁ t₂ ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < π / 2)
    (h₀ : |ω * (t₁ - t₀) - π| ≤ ε) (h₁ : |ω * (t₂ - t₁) - π| ≤ ε)
    (hnode : Real.tan ε < |Real.cos (ω * (t₀ + t₁) / 2)|) :
    (Real.sin (ω * t₁) - Real.sin (ω * t₀)) * (Real.sin (ω * t₂) - Real.sin (ω * t₁)) < 0 := by
  set A := ω * (t₁ - t₀) / 2 with hA
  set B := ω * (t₂ - t₁) / 2 with hB
  set φ := ω * (t₀ + t₁) / 2 with hφ
  set η := A + B - π with hη
  have hpi := Real.pi_pos
  -- the half-turn bounds on each gap
  have hA2 : |2 * A - π| ≤ ε := by
    have : 2 * A = ω * (t₁ - t₀) := by rw [hA]; ring
    rw [this]; exact h₀
  have hB2 : |2 * B - π| ≤ ε := by
    have : 2 * B = ω * (t₂ - t₁) := by rw [hB]; ring
    rw [this]; exact h₁
  obtain ⟨hA2l, hA2r⟩ := abs_le.mp hA2
  obtain ⟨hB2l, hB2r⟩ := abs_le.mp hB2
  have hsinA : 0 < Real.sin A := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsinB : 0 < Real.sin B := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hηl : -ε ≤ η := by rw [hη]; linarith
  have hηr : η ≤ ε := by rw [hη]; linarith
  -- the two increments, in product-to-sum form
  have hd0 : Real.sin (ω * t₁) - Real.sin (ω * t₀) = 2 * Real.sin A * Real.cos φ := by
    rw [Real.sin_sub_sin]
    have e1 : (ω * t₁ - ω * t₀) / 2 = A := by rw [hA]; ring
    have e2 : (ω * t₁ + ω * t₀) / 2 = φ := by rw [hφ]; ring
    rw [e1, e2]
  have hd1 : Real.sin (ω * t₂) - Real.sin (ω * t₁) = -(2 * Real.sin B * Real.cos (φ + η)) := by
    rw [Real.sin_sub_sin]
    have e1 : (ω * t₂ - ω * t₁) / 2 = B := by rw [hB]; ring
    have e2 : (ω * t₂ + ω * t₁) / 2 = (φ + η) + π := by rw [hφ, hη, hA, hB]; ring
    rw [e1, e2, Real.cos_add_pi]
    ring
  -- trigonometric bounds on the phase slip η
  have hcosε : 0 < Real.cos ε := Real.cos_pos_of_mem_Ioo ⟨by linarith, hε⟩
  have hsinε : 0 ≤ Real.sin ε := Real.sin_nonneg_of_nonneg_of_le_pi hε0 (by linarith)
  have hcosη : Real.cos ε ≤ Real.cos η := by
    rw [← Real.cos_abs η]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg η) (by linarith) (abs_le.mpr ⟨hηl, hηr⟩)
  have hsinη : |Real.sin η| ≤ Real.sin ε := by
    rw [abs_le]
    constructor
    · have := Real.sin_le_sin_of_le_of_le_pi_div_two (x := -ε) (y := η) (by linarith) (by linarith) hηl
      rw [Real.sin_neg] at this; linarith
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hηr
  have htan0 : 0 ≤ Real.tan ε := by rw [Real.tan_eq_sin_div_cos]; exact div_nonneg hsinε hcosε.le
  have hpos : 0 < |Real.cos φ| := lt_of_le_of_lt htan0 hnode
  have htan : Real.sin ε < |Real.cos φ| * Real.cos ε := by
    rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcosε] at hnode; linarith
  -- the key sign: cos φ · cos(φ + η) > 0
  have hkey : 0 < Real.cos φ * Real.cos (φ + η) := by
    rw [Real.cos_add]
    have h1 : Real.cos φ * (Real.sin φ * Real.sin η) ≤ |Real.cos φ| * Real.sin ε := by
      calc Real.cos φ * (Real.sin φ * Real.sin η)
          ≤ |Real.cos φ * (Real.sin φ * Real.sin η)| := le_abs_self _
        _ = |Real.cos φ| * (|Real.sin φ| * |Real.sin η|) := by rw [abs_mul, abs_mul]
        _ ≤ |Real.cos φ| * (1 * Real.sin ε) := by
            gcongr
            · exact Real.abs_sin_le_one φ
        _ = |Real.cos φ| * Real.sin ε := by ring
    have h2 : |Real.cos φ| * |Real.cos φ| * Real.cos ε ≤ Real.cos φ * (Real.cos φ * Real.cos η) := by
      rw [abs_mul_abs_self]
      have : 0 ≤ Real.cos φ * Real.cos φ := mul_self_nonneg _
      nlinarith
    have h3 : 0 < |Real.cos φ| * (|Real.cos φ| * Real.cos ε - Real.sin ε) :=
      mul_pos hpos (by linarith)
    nlinarith
  rw [hd0, hd1]
  have hprod := mul_pos (mul_pos hsinA hsinB) hkey
  have : 2 * Real.sin A * Real.cos φ * -(2 * Real.sin B * Real.cos (φ + η))
      = -(4 * (Real.sin A * Real.sin B * (Real.cos φ * Real.cos (φ + η)))) := by ring
  rw [this]
  linarith

/-- **Remove the clocks first.** For ANY finite bank of clocks, door 677 needs only that the registered ledger minus
that bank is not linearly behind at arbitrarily large heights. -/
theorem noOffline_of_residual_not_linearly_behind {ι : Type*} (F : Finset ι) (a ω : ι → ℝ)
    (hω : ∀ j ∈ F, 0 < ω j)
    (h : ∃ c : ℝ, c < 1 ∧ ∃ᶠ T in atTop,
      -(c * T) ≤ ∫ t in (0:ℝ)..T, (Smult t - ∑ j ∈ F, a j * Real.sin (ω j * t))) :
    NoOfflineZeros := by
  obtain ⟨c, hc, hfreq⟩ := h
  set K := ∑ j ∈ F, |a j| * (2 / ω j) with hK
  apply CriticalLinePhasor.WarpLedger.noOffline_of_frequently_not_linearly_behind
  refine ⟨(c + 1) / 2, by linarith, ?_⟩
  refine (hfreq.and_eventually (eventually_ge_atTop (2 * K / (1 - c)))).mono fun T hT => ?_
  obtain ⟨hTc, hTbig⟩ := hT
  have hcont : Continuous fun t => ∑ j ∈ F, a j * Real.sin (ω j * t) := by fun_prop
  have hint : ∫ t in (0:ℝ)..T, (Smult t - ∑ j ∈ F, a j * Real.sin (ω j * t))
      = (∫ t in (0:ℝ)..T, Smult t) - ∫ t in (0:ℝ)..T, ∑ j ∈ F, a j * Real.sin (ω j * t) :=
    intervalIntegral.integral_sub (CriticalLinePhasor.DVP.smult_intervalIntegrable 0 T)
      (hcont.intervalIntegrable 0 T)
  have hclock := clockSum_integral_abs_le F a ω hω T
  have hclock' : -K ≤ ∫ t in (0:ℝ)..T, ∑ j ∈ F, a j * Real.sin (ω j * t) :=
    le_trans (neg_le_neg hclock) (neg_abs_le _)
  have h1c : 0 < 1 - c := by linarith
  have hTK : 2 * K ≤ (1 - c) * T := by
    rw [div_le_iff₀ h1c] at hTbig; linarith
  rw [hint] at hTc
  nlinarith

end CriticalLinePhasor.HeadResonance

#print axioms CriticalLinePhasor.HeadResonance.clock_increments_alternate
#print axioms CriticalLinePhasor.HeadResonance.clockSum_integral_abs_le
#print axioms CriticalLinePhasor.HeadResonance.noOffline_of_residual_not_linearly_behind
