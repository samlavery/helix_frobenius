import RequestProject.DVPLog58Table
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The `cos(58·log n)` evaluator

One packaged lemma: from a seven-decimal log bracket, a quarter-angle
witness `r` with its exact `sinTaylor` order-5 value, and the d20 π
decimals, the kernel certifies `|cos(58·L) − v| ≤ ε`.  All 99 cosine
instances of the `t = 58` segment certificate go through this single slot;
the two big rationals are the d20 brackets of `2π`.
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The packaged cosine certificate at `t = 58`.** -/
theorem cos58_eval {L : ℝ} {lo hi r δ v ε : ℚ} (k : ℕ)
    (hlo : ((lo : ℚ) : ℝ) ≤ L) (hhi : L ≤ ((hi : ℚ) : ℝ))
    (hr : |r| ≤ 1)
    (ha1 : 58 * hi - k * (628318530717958647692/10^20 : ℚ) - 4 * r ≤ δ)
    (ha2 : -δ ≤ 58 * lo - k * (628318530717958647694/10^20 : ℚ) - 4 * r)
    (hs2 : |sinTaylor r 5| ≤ 2)
    (hε : δ + 96 * (|r| ^ 10 * (11/36288000))
        + |v - (2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1)| ≤ ε) :
    |Real.cos (58 * L) - ((v : ℚ) : ℝ)| ≤ ((ε : ℚ) : ℝ) := by
  have hδ0 : (0:ℚ) ≤ δ := by
    have h12 : (58:ℚ) * lo ≤ 58 * hi := by
      have : (lo : ℝ) ≤ (hi : ℝ) := le_trans hlo hhi
      have hlohi : lo ≤ hi := by exact_mod_cast this
      linarith
    have hA : (628318530717958647692/10^20 : ℚ)
        ≤ (628318530717958647694/10^20 : ℚ) := by norm_num
    have hkA : (k:ℚ) * (628318530717958647692/10^20 : ℚ)
        ≤ (k:ℚ) * (628318530717958647694/10^20 : ℚ) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    nlinarith [ha1, ha2]
  -- the 2π decimals
  have h2π_lo : ((628318530717958647692/10^20 : ℚ) : ℝ) ≤ 2 * Real.pi := by
    have := Real.pi_gt_d20
    push_cast
    linarith
  have h2π_hi : 2 * Real.pi ≤ ((628318530717958647694/10^20 : ℚ) : ℝ) := by
    have := Real.pi_lt_d20
    push_cast
    linarith
  -- the angle certificate
  have hθ : |58 * L - ((k : ℤ) : ℝ) * (2 * Real.pi) - 4 * ((r : ℚ) : ℝ)|
      ≤ ((δ : ℚ) : ℝ) := by
    have hk0 : (0:ℝ) ≤ ((k : ℤ) : ℝ) := by positivity
    have hcast : ((k : ℤ) : ℝ) = ((k : ℕ) : ℝ) := by push_cast; rfl
    rw [abs_le]
    constructor
    · have h1 : ((k : ℕ) : ℝ) * (2 * Real.pi)
          ≤ ((k : ℕ) : ℝ) * ((628318530717958647694/10^20 : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left h2π_hi (by positivity)
      have h2 : ((58 * lo - k * (628318530717958647694/10^20) - 4 * r
          : ℚ) : ℝ) ≤ 58 * L - ((k : ℕ) : ℝ)
            * ((628318530717958647694/10^20 : ℚ) : ℝ)
            - 4 * ((r : ℚ) : ℝ) := by
        push_cast
        have : ((lo : ℚ) : ℝ) * 58 ≤ L * 58 := by nlinarith [hlo]
        nlinarith [hlo]
      have h3 : (((-δ) : ℚ) : ℝ)
          ≤ ((58 * lo - k * (628318530717958647694/10^20) - 4 * r
            : ℚ) : ℝ) := by exact_mod_cast ha2
      rw [hcast]
      push_cast at h3 h2 ⊢
      nlinarith [h1, h2, h3]
    · have h1 : ((k : ℕ) : ℝ) * ((628318530717958647692/10^20 : ℚ) : ℝ)
          ≤ ((k : ℕ) : ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_left h2π_lo (by positivity)
      have h2 : 58 * L - ((k : ℕ) : ℝ)
            * ((628318530717958647692/10^20 : ℚ) : ℝ)
            - 4 * ((r : ℚ) : ℝ)
          ≤ ((58 * hi - k * (628318530717958647692/10^20) - 4 * r
            : ℚ) : ℝ) := by
        push_cast
        nlinarith [hhi]
      have h3 : ((58 * hi - k * (628318530717958647692/10^20) - 4 * r
          : ℚ) : ℝ) ≤ ((δ : ℚ) : ℝ) := by exact_mod_cast ha1
      rw [hcast]
      push_cast at h3 h2 ⊢
      nlinarith [h1, h2, h3]
  -- the sin certificate at the quarter angle
  have hsin := sin_enclosure (x := r) hr (n := 5) (by norm_num)
  have hbr : |((r : ℚ) : ℝ)| ^ (2 * 5)
      * (((2 * 5).succ : ℝ) * (((2 * 5).factorial : ℝ) * ((2 * 5 : ℕ) : ℝ))⁻¹)
      ≤ ((|r| ^ 10 * (11/36288000) : ℚ) : ℝ) := by
    rw [← Rat.cast_abs]
    push_cast
    norm_num [Nat.factorial]
  have hŝ := le_trans hsin hbr
  have hs2' : |((sinTaylor r 5 : ℚ) : ℝ)| ≤ 2 := by
    rw [← Rat.cast_abs]
    exact_mod_cast hs2
  -- the packaged evaluation
  have hmain := cos_angle_eval (θ := 58 * L) (r := r) (ŝ := sinTaylor r 5)
    (δ := δ) (τ := |r| ^ 10 * (11/36288000)) ((k : ℕ) : ℤ) hθ hŝ hs2'
  -- transfer to the rounded value v
  have hvF : |((v : ℚ) : ℝ)
      - ((2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1 : ℚ) : ℝ)|
      = ((|v - (2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1)| : ℚ) : ℝ) := by
    rw [← Rat.cast_sub, ← Rat.cast_abs]
  calc |Real.cos (58 * L) - ((v : ℚ) : ℝ)|
      = |(Real.cos (58 * L)
          - ((2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1 : ℚ) : ℝ))
        + (((2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1 : ℚ) : ℝ)
          - ((v : ℚ) : ℝ))| := by ring_nf
    _ ≤ |Real.cos (58 * L)
          - ((2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1 : ℚ) : ℝ)|
        + |((2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1 : ℚ) : ℝ)
          - ((v : ℚ) : ℝ)| := abs_add_le _ _
    _ ≤ (((δ : ℚ) : ℝ) + 96 * ((|r| ^ 10 * (11/36288000) : ℚ) : ℝ))
        + ((|v - (2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1)| : ℚ) : ℝ) := by
        refine add_le_add hmain ?_
        rw [abs_sub_comm, hvF]
    _ ≤ ((ε : ℚ) : ℝ) := by
        rw [show (((δ : ℚ) : ℝ) + 96 * ((|r| ^ 10 * (11/36288000) : ℚ) : ℝ))
            + ((|v - (2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1)| : ℚ) : ℝ)
            = ((δ + 96 * (|r| ^ 10 * (11/36288000))
              + |v - (2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1)| : ℚ) : ℝ) by
          push_cast; ring]
        exact_mod_cast hε

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cos58_eval
end AxiomAudit
