import RequestProject.DVPLog58Table
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The parametric `cos/sin (M·log n)` evaluators

Generalizations of the `t = 58` cosine evaluator to an arbitrary natural
multiplier `M` (the station height): from a seven-decimal log bracket and
a quarter-angle witness, the kernel certifies BOTH
`|cos(M·L) − v| ≤ ε` and `|sin(M·L) − u| ≤ ε` — the entire transcendental
input of a Hardy-ladder station.
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The angle window from a log bracket and the d20 `2π` decimals. -/
theorem angle_window {L : ℝ} {lo hi r δ : ℚ} (M k : ℕ)
    (hlo : ((lo : ℚ) : ℝ) ≤ L) (hhi : L ≤ ((hi : ℚ) : ℝ))
    (ha1 : M * hi - k * (628318530717958647692/10^20 : ℚ) - 4 * r ≤ δ)
    (ha2 : -δ ≤ M * lo - k * (628318530717958647694/10^20 : ℚ) - 4 * r) :
    |(M:ℝ) * L - ((k : ℤ) : ℝ) * (2 * Real.pi) - 4 * ((r : ℚ) : ℝ)|
      ≤ ((δ : ℚ) : ℝ) := by
  have h2π_lo : ((628318530717958647692/10^20 : ℚ) : ℝ) ≤ 2 * Real.pi := by
    have := Real.pi_gt_d20
    push_cast
    linarith
  have h2π_hi : 2 * Real.pi ≤ ((628318530717958647694/10^20 : ℚ) : ℝ) := by
    have := Real.pi_lt_d20
    push_cast
    linarith
  have hcast : ((k : ℤ) : ℝ) = ((k : ℕ) : ℝ) := by push_cast; rfl
  rw [abs_le, hcast]
  constructor
  · have h1 : ((k : ℕ) : ℝ) * (2 * Real.pi)
        ≤ ((k : ℕ) : ℝ) * ((628318530717958647694/10^20 : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_left h2π_hi (by positivity)
    have h2 : ((M * lo - k * (628318530717958647694/10^20) - 4 * r
        : ℚ) : ℝ) ≤ (M:ℝ) * L - ((k : ℕ) : ℝ)
          * ((628318530717958647694/10^20 : ℚ) : ℝ)
          - 4 * ((r : ℚ) : ℝ) := by
      push_cast
      have hM0 : (0:ℝ) ≤ (M:ℝ) := by positivity
      nlinarith [hlo]
    have h3 : (((-δ) : ℚ) : ℝ)
        ≤ ((M * lo - k * (628318530717958647694/10^20) - 4 * r
          : ℚ) : ℝ) := by exact_mod_cast ha2
    push_cast at h3 h2 ⊢
    nlinarith [h1, h2, h3]
  · have h1 : ((k : ℕ) : ℝ) * ((628318530717958647692/10^20 : ℚ) : ℝ)
        ≤ ((k : ℕ) : ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_left h2π_lo (by positivity)
    have h2 : (M:ℝ) * L - ((k : ℕ) : ℝ)
          * ((628318530717958647692/10^20 : ℚ) : ℝ)
          - 4 * ((r : ℚ) : ℝ)
        ≤ ((M * hi - k * (628318530717958647692/10^20) - 4 * r
          : ℚ) : ℝ) := by
      push_cast
      have hM0 : (0:ℝ) ≤ (M:ℝ) := by positivity
      nlinarith [hhi]
    have h3 : ((M * hi - k * (628318530717958647692/10^20) - 4 * r
        : ℚ) : ℝ) ≤ ((δ : ℚ) : ℝ) := by exact_mod_cast ha1
    push_cast at h3 h2 ⊢
    nlinarith [h1, h2, h3]

/-- **The parametric cosine evaluator.** -/
theorem cosMul_eval {L : ℝ} {lo hi r δ v ε : ℚ} (M k : ℕ)
    (hlo : ((lo : ℚ) : ℝ) ≤ L) (hhi : L ≤ ((hi : ℚ) : ℝ))
    (hr : |r| ≤ 1)
    (ha1 : M * hi - k * (628318530717958647692/10^20 : ℚ) - 4 * r ≤ δ)
    (ha2 : -δ ≤ M * lo - k * (628318530717958647694/10^20 : ℚ) - 4 * r)
    (hs2 : |sinTaylor r 5| ≤ 2)
    (hε : δ + 96 * (|r| ^ 10 * (11/36288000))
        + |v - (2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1)| ≤ ε) :
    |Real.cos ((M:ℝ) * L) - ((v : ℚ) : ℝ)| ≤ ((ε : ℚ) : ℝ) := by
  have hθ := angle_window M k hlo hhi ha1 ha2
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
  have hmain := cos_angle_eval (θ := (M:ℝ) * L) (r := r)
    (ŝ := sinTaylor r 5) (δ := δ) (τ := |r| ^ 10 * (11/36288000))
    ((k : ℕ) : ℤ) hθ hŝ hs2'
  have hvF : |((v : ℚ) : ℝ)
      - ((2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1 : ℚ) : ℝ)|
      = ((|v - (2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1)| : ℚ) : ℝ) := by
    rw [← Rat.cast_sub, ← Rat.cast_abs]
  calc |Real.cos ((M:ℝ) * L) - ((v : ℚ) : ℝ)|
      ≤ |Real.cos ((M:ℝ) * L)
          - ((2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1 : ℚ) : ℝ)|
        + |((2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1 : ℚ) : ℝ)
          - ((v : ℚ) : ℝ)| := by
        have := abs_sub_abs_le_abs_sub (Real.cos ((M:ℝ) * L)) ((v : ℚ) : ℝ)
        calc |Real.cos ((M:ℝ) * L) - ((v : ℚ) : ℝ)|
            = |(Real.cos ((M:ℝ) * L)
                - ((2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1 : ℚ) : ℝ))
              + (((2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1 : ℚ) : ℝ)
                - ((v : ℚ) : ℝ))| := by ring_nf
          _ ≤ _ := abs_add_le _ _
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

/-- **The parametric sine evaluator.** -/
theorem sinMul_eval {L : ℝ} {lo hi r δ u ε : ℚ} (M k : ℕ)
    (hlo : ((lo : ℚ) : ℝ) ≤ L) (hhi : L ≤ ((hi : ℚ) : ℝ))
    (hr : |r| ≤ 1)
    (ha1 : M * hi - k * (628318530717958647692/10^20 : ℚ) - 4 * r ≤ δ)
    (ha2 : -δ ≤ M * lo - k * (628318530717958647694/10^20 : ℚ) - 4 * r)
    (hs2 : |sinTaylor r 5| ≤ 2)
    (hε : δ + 72 * (|r| ^ 10 * (11/36288000) + |r| ^ 10 * (11/36288000))
        + |u - (4 * sinTaylor r 5 * cosTaylor r 5
            * (1 - 2 * (sinTaylor r 5) ^ 2))| ≤ ε) :
    |Real.sin ((M:ℝ) * L) - ((u : ℚ) : ℝ)| ≤ ((ε : ℚ) : ℝ) := by
  have hθ := angle_window M k hlo hhi ha1 ha2
  have hsin := sin_enclosure (x := r) hr (n := 5) (by norm_num)
  have hbrs : |((r : ℚ) : ℝ)| ^ (2 * 5)
      * (((2 * 5).succ : ℝ) * (((2 * 5).factorial : ℝ) * ((2 * 5 : ℕ) : ℝ))⁻¹)
      ≤ ((|r| ^ 10 * (11/36288000) : ℚ) : ℝ) := by
    rw [← Rat.cast_abs]
    push_cast
    norm_num [Nat.factorial]
  have hŝ := le_trans hsin hbrs
  have hcos := cos_enclosure (x := r) hr (n := 5) (by norm_num)
  have hbrc : |((r : ℚ) : ℝ)| ^ (2 * 5)
      * (((2 * 5).succ : ℝ) * (((2 * 5).factorial : ℝ) * ((2 * 5 : ℕ) : ℝ))⁻¹)
      ≤ ((|r| ^ 10 * (11/36288000) : ℚ) : ℝ) := by
    rw [← Rat.cast_abs]
    push_cast
    norm_num [Nat.factorial]
  have hĉ := le_trans hcos hbrc
  have hs2' : |((sinTaylor r 5 : ℚ) : ℝ)| ≤ 2 := by
    rw [← Rat.cast_abs]
    exact_mod_cast hs2
  have hmain := sin_angle_eval (θ := (M:ℝ) * L) (r := r)
    (ŝ := sinTaylor r 5) (ĉ := cosTaylor r 5) (δ := δ)
    (τs := |r| ^ 10 * (11/36288000)) (τc := |r| ^ 10 * (11/36288000))
    ((k : ℕ) : ℤ) hθ hŝ hĉ hs2'
  have hvF : |((u : ℚ) : ℝ)
      - ((4 * sinTaylor r 5 * cosTaylor r 5
          * (1 - 2 * (sinTaylor r 5) ^ 2) : ℚ) : ℝ)|
      = ((|u - (4 * sinTaylor r 5 * cosTaylor r 5
          * (1 - 2 * (sinTaylor r 5) ^ 2))| : ℚ) : ℝ) := by
    rw [← Rat.cast_sub, ← Rat.cast_abs]
  calc |Real.sin ((M:ℝ) * L) - ((u : ℚ) : ℝ)|
      ≤ |Real.sin ((M:ℝ) * L)
          - ((4 * sinTaylor r 5 * cosTaylor r 5
            * (1 - 2 * (sinTaylor r 5) ^ 2) : ℚ) : ℝ)|
        + |((4 * sinTaylor r 5 * cosTaylor r 5
            * (1 - 2 * (sinTaylor r 5) ^ 2) : ℚ) : ℝ)
          - ((u : ℚ) : ℝ)| := by
        calc |Real.sin ((M:ℝ) * L) - ((u : ℚ) : ℝ)|
            = |(Real.sin ((M:ℝ) * L)
                - ((4 * sinTaylor r 5 * cosTaylor r 5
                  * (1 - 2 * (sinTaylor r 5) ^ 2) : ℚ) : ℝ))
              + (((4 * sinTaylor r 5 * cosTaylor r 5
                  * (1 - 2 * (sinTaylor r 5) ^ 2) : ℚ) : ℝ)
                - ((u : ℚ) : ℝ))| := by ring_nf
          _ ≤ _ := abs_add_le _ _
    _ ≤ (((δ : ℚ) : ℝ)
          + 72 * (((|r| ^ 10 * (11/36288000) : ℚ) : ℝ)
            + ((|r| ^ 10 * (11/36288000) : ℚ) : ℝ)))
        + ((|u - (4 * sinTaylor r 5 * cosTaylor r 5
            * (1 - 2 * (sinTaylor r 5) ^ 2))| : ℚ) : ℝ) := by
        refine add_le_add ?_ ?_
        · first
          | exact hmain
          | (convert hmain using 2)
        · rw [abs_sub_comm, hvF]
    _ ≤ ((ε : ℚ) : ℝ) := by
        rw [show (((δ : ℚ) : ℝ)
              + 72 * (((|r| ^ 10 * (11/36288000) : ℚ) : ℝ)
                + ((|r| ^ 10 * (11/36288000) : ℚ) : ℝ)))
            + ((|u - (4 * sinTaylor r 5 * cosTaylor r 5
                * (1 - 2 * (sinTaylor r 5) ^ 2))| : ℚ) : ℝ)
            = ((δ + 72 * (|r| ^ 10 * (11/36288000) + |r| ^ 10 * (11/36288000))
              + |u - (4 * sinTaylor r 5 * cosTaylor r 5
                * (1 - 2 * (sinTaylor r 5) ^ 2))| : ℚ) : ℝ) by
          push_cast; ring]
        exact_mod_cast hε

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cosMul_eval
#print axioms CriticalLinePhasor.DVP.sinMul_eval
end AxiomAudit
