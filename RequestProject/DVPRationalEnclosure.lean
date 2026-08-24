import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Rat.BigOperators

/-!
# Kernel-rational Taylor enclosures for exp, cos, sin

Foundation of the finite-conjunct campaign (`seat_criterion_split_iff`
item (1), RH_LEDGER 342): a rigorous evaluation of ζ at low height reduces
to rational arithmetic the kernel checks, plus ONE generic enclosure lemma
per special function.  `Complex.exp_bound` supplies arbitrary-order error
control; the partial sums here are ℚ-valued by construction.
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- Rational Taylor partial sum for `exp`. -/
def expTaylor (x : ℚ) (n : ℕ) : ℚ :=
  ∑ m ∈ range n, x ^ m / m.factorial

/-- Rational Taylor partial sum for `cos`: the even block of order `2n`. -/
def cosTaylor (x : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ range n, (-1) ^ k * x ^ (2 * k) / (2 * k).factorial

/-- Rational Taylor partial sum for `sin`: the odd block of order `2n+1`. -/
def sinTaylor (x : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ range n, (-1) ^ k * x ^ (2 * k + 1) / (2 * k + 1).factorial

/-- **E1: the exp enclosure.**  For rational `|x| ≤ 1` the `n`-term partial
sum encloses `exp x` with the factorial tail error. -/
theorem exp_enclosure {x : ℚ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    |Real.exp x - (expTaylor x n : ℝ)|
      ≤ |(x : ℝ)| ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * n)) := by
  have hx' : |(x : ℝ)| ≤ 1 := by exact_mod_cast hx
  have h := Real.exp_bound hx' hn
  have hsum : ((expTaylor x n : ℚ) : ℝ)
      = ∑ m ∈ range n, (x : ℝ) ^ m / m.factorial := by
    unfold expTaylor
    rw [Rat.cast_sum]
    push_cast
    rfl
  rw [hsum]
  exact h

/-- `(x·I)^(2k)` is the real number `(−1)^k x^(2k)`. -/
lemma mul_I_pow_even (x : ℝ) (k : ℕ) :
    ((x : ℂ) * I) ^ (2 * k) = (((-1) ^ k * x ^ (2 * k) : ℝ) : ℂ) := by
  rw [mul_pow, pow_mul, pow_mul, I_sq]
  push_cast
  ring

/-- `(x·I)^(2k+1)` is `(−1)^k x^(2k+1)` times `I`. -/
lemma mul_I_pow_odd (x : ℝ) (k : ℕ) :
    ((x : ℂ) * I) ^ (2 * k + 1)
      = (((-1) ^ k * x ^ (2 * k + 1) : ℝ) : ℂ) * I := by
  rw [pow_succ, mul_I_pow_even]
  push_cast
  ring

/-- The order-`2n` exp partial sum at `x·I`: real part is the cos block,
imaginary part is the sin block. -/
lemma exp_partial_eq (x : ℚ) (n : ℕ) :
    ∑ m ∈ range (2 * n), (((x : ℝ) : ℂ) * I) ^ m / m.factorial
      = ((cosTaylor x n : ℝ) : ℂ) + ((sinTaylor x n : ℝ) : ℂ) * I := by
  induction n with
  | zero => simp [cosTaylor, sinTaylor]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n) + 1 + 1 by ring, sum_range_succ,
      sum_range_succ, ih, mul_I_pow_even, mul_I_pow_odd]
    have hc : (cosTaylor x (n + 1) : ℝ)
        = (cosTaylor x n : ℝ) + (-1) ^ n * (x : ℝ) ^ (2 * n)
            / (2 * n).factorial := by
      unfold cosTaylor
      rw [sum_range_succ]
      push_cast
      ring
    have hs : (sinTaylor x (n + 1) : ℝ)
        = (sinTaylor x n : ℝ) + (-1) ^ n * (x : ℝ) ^ (2 * n + 1)
            / (2 * n + 1).factorial := by
      unfold sinTaylor
      rw [sum_range_succ]
      push_cast
      ring
    rw [hc, hs]
    push_cast
    ring

/-- `‖x·I‖ = |x|` for real `x`. -/
lemma norm_ofReal_mul_I (x : ℝ) : ‖(x : ℂ) * I‖ = |x| := by
  simp [Real.norm_eq_abs]

/-- **E2: the cos enclosure.**  For rational `|x| ≤ 1` the `n`-block even
partial sum encloses `cos x` with the order-`2n` factorial tail error. -/
theorem cos_enclosure {x : ℚ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    |Real.cos x - (cosTaylor x n : ℝ)|
      ≤ |(x : ℝ)| ^ (2 * n)
        * (((2 * n).succ : ℝ) * (((2 * n).factorial : ℝ) * ((2 * n : ℕ) : ℝ))⁻¹) := by
  have hx' : ‖((x : ℝ) : ℂ) * I‖ ≤ 1 := by
    rw [norm_ofReal_mul_I]
    exact_mod_cast hx
  have h2n : 0 < 2 * n := by omega
  have h := Complex.exp_bound hx' h2n
  rw [exp_partial_eq] at h
  have hre : (Complex.exp (((x : ℝ) : ℂ) * I)
      - (((cosTaylor x n : ℝ) : ℂ) + ((sinTaylor x n : ℝ) : ℂ) * I)).re
      = Real.cos x - (cosTaylor x n : ℝ) := by
    rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re]
    simp
  calc |Real.cos x - (cosTaylor x n : ℝ)|
      = |(Complex.exp (((x : ℝ) : ℂ) * I)
          - (((cosTaylor x n : ℝ) : ℂ) + ((sinTaylor x n : ℝ) : ℂ) * I)).re| := by
        rw [hre]
    _ ≤ ‖Complex.exp (((x : ℝ) : ℂ) * I)
          - (((cosTaylor x n : ℝ) : ℂ) + ((sinTaylor x n : ℝ) : ℂ) * I)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ‖((x : ℝ) : ℂ) * I‖ ^ (2 * n)
          * (((2 * n).succ : ℝ) * (((2 * n).factorial : ℝ) * ((2 * n : ℕ) : ℝ))⁻¹) := h
    _ = |(x : ℝ)| ^ (2 * n)
          * (((2 * n).succ : ℝ) * (((2 * n).factorial : ℝ) * ((2 * n : ℕ) : ℝ))⁻¹) := by
        rw [norm_ofReal_mul_I]

/-- **E3: the sin enclosure.**  Same tail error as E2 (the sin block is
the imaginary part of the same order-`2n` partial sum). -/
theorem sin_enclosure {x : ℚ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    |Real.sin x - (sinTaylor x n : ℝ)|
      ≤ |(x : ℝ)| ^ (2 * n)
        * (((2 * n).succ : ℝ) * (((2 * n).factorial : ℝ) * ((2 * n : ℕ) : ℝ))⁻¹) := by
  have hx' : ‖((x : ℝ) : ℂ) * I‖ ≤ 1 := by
    rw [norm_ofReal_mul_I]
    exact_mod_cast hx
  have h2n : 0 < 2 * n := by omega
  have h := Complex.exp_bound hx' h2n
  rw [exp_partial_eq] at h
  have him : (Complex.exp (((x : ℝ) : ℂ) * I)
      - (((cosTaylor x n : ℝ) : ℂ) + ((sinTaylor x n : ℝ) : ℂ) * I)).im
      = Real.sin x - (sinTaylor x n : ℝ) := by
    rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im]
    simp
  calc |Real.sin x - (sinTaylor x n : ℝ)|
      = |(Complex.exp (((x : ℝ) : ℂ) * I)
          - (((cosTaylor x n : ℝ) : ℂ) + ((sinTaylor x n : ℝ) : ℂ) * I)).im| := by
        rw [him]
    _ ≤ ‖Complex.exp (((x : ℝ) : ℂ) * I)
          - (((cosTaylor x n : ℝ) : ℂ) + ((sinTaylor x n : ℝ) : ℂ) * I)‖ :=
        Complex.abs_im_le_norm _
    _ ≤ ‖((x : ℝ) : ℂ) * I‖ ^ (2 * n)
          * (((2 * n).succ : ℝ) * (((2 * n).factorial : ℝ) * ((2 * n : ℕ) : ℝ))⁻¹) := h
    _ = |(x : ℝ)| ^ (2 * n)
          * (((2 * n).succ : ℝ) * (((2 * n).factorial : ℝ) * ((2 * n : ℕ) : ℝ))⁻¹) := by
        rw [norm_ofReal_mul_I]

/-! ## E4: angle propagation — cos/sin at ANY real angle from a rational
quarter-angle certificate.  `θ = 2πk + 4r + O(δ)` with `|r| ≤ 1`; two
double-angle steps turn Taylor data at `r` into values at `θ`.  The angle
hypothesis is stated against the REAL angle, so π-decimal and log
enclosures discharge it through the same slot. -/

/-- **E4c: cos at an arbitrary angle.**  From `|θ − 2πk − 4r| ≤ δ` and a
sin-enclosure `|sin r − ŝ| ≤ τ`, the rational value `2(1−2ŝ²)²−1`
approximates `cos θ` to `δ + 96τ`. -/
theorem cos_angle_eval {θ : ℝ} {r ŝ δ τ : ℚ} (k : ℤ)
    (hθ : |θ - k * (2 * Real.pi) - 4 * (r : ℝ)| ≤ (δ : ℝ))
    (hŝ : |Real.sin r - (ŝ : ℝ)| ≤ (τ : ℝ))
    (hŝ2 : |(ŝ : ℝ)| ≤ 2) :
    |Real.cos θ - ((2 * (1 - 2 * ŝ ^ 2) ^ 2 - 1 : ℚ) : ℝ)|
      ≤ (δ : ℝ) + 96 * τ := by
  set s : ℝ := Real.sin r with hsdef
  have hs1 : |s| ≤ 1 := Real.abs_sin_le_one r
  have hτ0 : (0:ℝ) ≤ τ := le_trans (abs_nonneg _) hŝ
  -- periodicity + Lipschitz
  have hper : Real.cos θ = Real.cos (θ - k * (2 * Real.pi)) :=
    (Real.cos_sub_int_mul_two_pi θ k).symm
  have hlip : |Real.cos (θ - k * (2 * Real.pi)) - Real.cos (4 * (r : ℝ))|
      ≤ (δ : ℝ) := le_trans (Real.abs_cos_sub_cos_le _ _) hθ
  -- exact quarter-angle identity
  have hid : Real.cos (4 * (r : ℝ)) = 2 * (1 - 2 * s ^ 2) ^ 2 - 1 := by
    have h4 : (4 : ℝ) * r = 2 * (2 * r) := by ring
    rw [h4, Real.cos_two_mul]
    have h2r : Real.cos (2 * (r : ℝ)) = 1 - 2 * s ^ 2 := by
      rw [Real.cos_two_mul]
      have hpyth := Real.sin_sq_add_cos_sq (r : ℝ)
      rw [hsdef]
      linarith
    rw [h2r]
  -- propagation through the polynomial
  have hkey : (2 * (1 - 2 * s ^ 2) ^ 2 - 1)
      - ((2 * (1 - 2 * ŝ ^ 2) ^ 2 - 1 : ℚ) : ℝ)
      = 8 * ((ŝ : ℝ) - s) * ((ŝ : ℝ) + s) * (1 - s ^ 2 - (ŝ : ℝ) ^ 2) := by
    push_cast
    ring
  have hA : |(ŝ : ℝ) - s| ≤ (τ : ℝ) := by
    rw [abs_sub_comm]
    exact hŝ
  have hB : |(ŝ : ℝ) + s| ≤ 3 := by
    calc |(ŝ : ℝ) + s| ≤ |(ŝ : ℝ)| + |s| := abs_add_le _ _
      _ ≤ 3 := by linarith
  have hs2 : s ^ 2 ≤ 1 := by
    nlinarith [sq_abs s, hs1, abs_nonneg s]
  have hŝ4 : (ŝ : ℝ) ^ 2 ≤ 4 := by
    nlinarith [sq_abs ((ŝ : ℝ)), hŝ2, abs_nonneg ((ŝ : ℝ))]
  have hC : |1 - s ^ 2 - (ŝ : ℝ) ^ 2| ≤ 4 := by
    rw [abs_le]
    constructor
    · linarith
    · nlinarith [sq_nonneg s, sq_nonneg ((ŝ : ℝ))]
  have hpoly : |(2 * (1 - 2 * s ^ 2) ^ 2 - 1)
      - ((2 * (1 - 2 * ŝ ^ 2) ^ 2 - 1 : ℚ) : ℝ)| ≤ 96 * (τ : ℝ) := by
    rw [hkey, abs_mul, abs_mul, abs_mul]
    have h8 : |(8 : ℝ)| = 8 := by norm_num
    rw [h8]
    calc 8 * |(ŝ : ℝ) - s| * |(ŝ : ℝ) + s| * |1 - s ^ 2 - (ŝ : ℝ) ^ 2|
        ≤ 8 * (τ : ℝ) * 3 * 4 := by
          gcongr
      _ = 96 * (τ : ℝ) := by ring
  calc |Real.cos θ - ((2 * (1 - 2 * ŝ ^ 2) ^ 2 - 1 : ℚ) : ℝ)|
      = |(Real.cos (θ - k * (2 * Real.pi)) - Real.cos (4 * (r : ℝ)))
          + (Real.cos (4 * (r : ℝ))
            - ((2 * (1 - 2 * ŝ ^ 2) ^ 2 - 1 : ℚ) : ℝ))| := by
        rw [hper]
        ring_nf
    _ ≤ |Real.cos (θ - k * (2 * Real.pi)) - Real.cos (4 * (r : ℝ))|
          + |Real.cos (4 * (r : ℝ))
            - ((2 * (1 - 2 * ŝ ^ 2) ^ 2 - 1 : ℚ) : ℝ)| := abs_add_le _ _
    _ ≤ (δ : ℝ) + 96 * (τ : ℝ) :=
        add_le_add hlip (hid.symm ▸ hpoly)

/-- **E4s: sin at an arbitrary angle.**  From the same angle certificate
and BOTH enclosures at `r`, the rational value `4ŝĉ(1−2ŝ²)` approximates
`sin θ` to `δ + 72(τs + τc)`. -/
theorem sin_angle_eval {θ : ℝ} {r ŝ ĉ δ τs τc : ℚ} (k : ℤ)
    (hθ : |θ - k * (2 * Real.pi) - 4 * (r : ℝ)| ≤ (δ : ℝ))
    (hŝ : |Real.sin r - (ŝ : ℝ)| ≤ (τs : ℝ))
    (hĉ : |Real.cos r - (ĉ : ℝ)| ≤ (τc : ℝ))
    (hŝ2 : |(ŝ : ℝ)| ≤ 2) :
    |Real.sin θ - ((4 * ŝ * ĉ * (1 - 2 * ŝ ^ 2) : ℚ) : ℝ)|
      ≤ (δ : ℝ) + 72 * (τs + τc) := by
  set s : ℝ := Real.sin r with hsdef
  set c : ℝ := Real.cos r with hcdef
  have hs1 : |s| ≤ 1 := Real.abs_sin_le_one r
  have hc1 : |c| ≤ 1 := Real.abs_cos_le_one r
  have hτs0 : (0:ℝ) ≤ τs := le_trans (abs_nonneg _) hŝ
  have hτc0 : (0:ℝ) ≤ τc := le_trans (abs_nonneg _) hĉ
  have hper : Real.sin θ = Real.sin (θ - k * (2 * Real.pi)) :=
    (Real.sin_sub_int_mul_two_pi θ k).symm
  have hlip : |Real.sin (θ - k * (2 * Real.pi)) - Real.sin (4 * (r : ℝ))|
      ≤ (δ : ℝ) := le_trans (Real.abs_sin_sub_sin_le _ _) hθ
  have hid : Real.sin (4 * (r : ℝ)) = 4 * s * c * (1 - 2 * s ^ 2) := by
    have h4 : (4 : ℝ) * r = 2 * (2 * r) := by ring
    rw [h4, Real.sin_two_mul, Real.sin_two_mul, Real.cos_two_mul]
    have hpyth := Real.sin_sq_add_cos_sq (r : ℝ)
    rw [← hsdef, ← hcdef] at hpyth ⊢
    linear_combination 8 * s * c * hpyth
  have hkey : (4 * s * c * (1 - 2 * s ^ 2))
      - ((4 * ŝ * ĉ * (1 - 2 * ŝ ^ 2) : ℚ) : ℝ)
      = (s - (ŝ : ℝ)) * (4 * c - 8 * c * (s ^ 2 + s * (ŝ : ℝ) + (ŝ : ℝ) ^ 2))
        + (c - (ĉ : ℝ)) * (4 * (ŝ : ℝ) - 8 * (ŝ : ℝ) ^ 3) := by
    push_cast
    ring
  have hsabs2 : |s ^ 2| ≤ 1 := by
    rw [abs_sq]
    nlinarith [sq_abs s, hs1, abs_nonneg s]
  have hŝabs2 : |(ŝ : ℝ) ^ 2| ≤ 4 := by
    rw [abs_sq]
    nlinarith [sq_abs ((ŝ : ℝ)), hŝ2, abs_nonneg ((ŝ : ℝ))]
  have hbrA : |4 * c - 8 * c * (s ^ 2 + s * (ŝ : ℝ) + (ŝ : ℝ) ^ 2)| ≤ 60 := by
    have h1 : |s ^ 2 + s * (ŝ : ℝ) + (ŝ : ℝ) ^ 2| ≤ 7 := by
      calc |s ^ 2 + s * (ŝ : ℝ) + (ŝ : ℝ) ^ 2|
          ≤ |s ^ 2| + |s * (ŝ : ℝ)| + |(ŝ : ℝ) ^ 2| := abs_add_three _ _ _
        _ ≤ 7 := by
            rw [abs_mul]
            nlinarith [hsabs2, hŝabs2, hs1, hŝ2, abs_nonneg s,
              abs_nonneg ((ŝ : ℝ))]
    calc |4 * c - 8 * c * (s ^ 2 + s * (ŝ : ℝ) + (ŝ : ℝ) ^ 2)|
        ≤ |4 * c| + |8 * c * (s ^ 2 + s * (ŝ : ℝ) + (ŝ : ℝ) ^ 2)| :=
          abs_sub _ _
      _ ≤ 60 := by
          rw [abs_mul, abs_mul, abs_mul]
          have h4 : |(4:ℝ)| = 4 := by norm_num
          have h8 : |(8:ℝ)| = 8 := by norm_num
          rw [h4, h8]
          nlinarith [hc1, h1, abs_nonneg c,
            abs_nonneg (s ^ 2 + s * (ŝ : ℝ) + (ŝ : ℝ) ^ 2)]
  have hbrB : |4 * (ŝ : ℝ) - 8 * (ŝ : ℝ) ^ 3| ≤ 72 := by
    have h3 : |(ŝ : ℝ) ^ 3| ≤ 8 := by
      rw [show ((ŝ:ℝ))^3 = (ŝ:ℝ)^2 * (ŝ:ℝ) by ring, abs_mul]
      nlinarith [hŝabs2, hŝ2, abs_nonneg ((ŝ : ℝ)),
        abs_nonneg ((ŝ : ℝ) ^ 2)]
    calc |4 * (ŝ : ℝ) - 8 * (ŝ : ℝ) ^ 3|
        ≤ |4 * (ŝ : ℝ)| + |8 * (ŝ : ℝ) ^ 3| := abs_sub _ _
      _ ≤ 72 := by
          rw [abs_mul, abs_mul]
          have h4 : |(4:ℝ)| = 4 := by norm_num
          have h8 : |(8:ℝ)| = 8 := by norm_num
          rw [h4, h8]
          linarith
  have hpoly : |(4 * s * c * (1 - 2 * s ^ 2))
      - ((4 * ŝ * ĉ * (1 - 2 * ŝ ^ 2) : ℚ) : ℝ)| ≤ 72 * ((τs : ℝ) + τc) := by
    rw [hkey]
    calc |(s - (ŝ : ℝ)) * (4 * c - 8 * c * (s ^ 2 + s * (ŝ : ℝ) + (ŝ : ℝ) ^ 2))
          + (c - (ĉ : ℝ)) * (4 * (ŝ : ℝ) - 8 * (ŝ : ℝ) ^ 3)|
        ≤ |(s - (ŝ : ℝ)) * (4 * c - 8 * c * (s ^ 2 + s * (ŝ : ℝ) + (ŝ : ℝ) ^ 2))|
          + |(c - (ĉ : ℝ)) * (4 * (ŝ : ℝ) - 8 * (ŝ : ℝ) ^ 3)| := abs_add_le _ _
      _ = |s - (ŝ : ℝ)| * |4 * c - 8 * c * (s ^ 2 + s * (ŝ : ℝ) + (ŝ : ℝ) ^ 2)|
          + |c - (ĉ : ℝ)| * |4 * (ŝ : ℝ) - 8 * (ŝ : ℝ) ^ 3| := by
            rw [abs_mul, abs_mul]
      _ ≤ (τs : ℝ) * 60 + (τc : ℝ) * 72 := by
            gcongr <;> first
              | exact hŝ
              | exact hĉ
              | exact hbrA
              | exact hbrB
      _ ≤ 72 * ((τs : ℝ) + τc) := by linarith
  calc |Real.sin θ - ((4 * ŝ * ĉ * (1 - 2 * ŝ ^ 2) : ℚ) : ℝ)|
      = |(Real.sin (θ - k * (2 * Real.pi)) - Real.sin (4 * (r : ℝ)))
          + (Real.sin (4 * (r : ℝ))
            - ((4 * ŝ * ĉ * (1 - 2 * ŝ ^ 2) : ℚ) : ℝ))| := by
        rw [hper]
        ring_nf
    _ ≤ |Real.sin (θ - k * (2 * Real.pi)) - Real.sin (4 * (r : ℝ))|
          + |Real.sin (4 * (r : ℝ))
            - ((4 * ŝ * ĉ * (1 - 2 * ŝ ^ 2) : ℚ) : ℝ)| := abs_add_le _ _
    _ ≤ (δ : ℝ) + 72 * ((τs : ℝ) + τc) :=
        add_le_add hlip (hid.symm ▸ hpoly)

/-! ## E5: exp at any rational via shift-splitting, and log certificates.
`exp x = exp(x−n)·(exp 1)^n` puts the Taylor engine in reach of any
argument; `exp 1` comes from mathlib's d9 decimals.  Log enclosures then
follow from monotonicity — no series for log at all. -/

/-- **E5u: exp upper bound by shift.**  `exp(x−n)` data (from
`exp_enclosure`) plus the d9 upper decimal for `e` bound `exp x` above. -/
theorem exp_upper_shift {x : ℚ} (n : ℕ) {T τ : ℚ}
    (hT : |Real.exp ((x - n : ℚ)) - (T : ℝ)| ≤ (τ : ℝ)) :
    Real.exp x ≤ ((T + τ) * (2.7182818286 : ℚ) ^ n : ℚ) := by
  have hsplit : Real.exp x = Real.exp ((x - n : ℚ)) * Real.exp 1 ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hsplit]
  have h1 : Real.exp ((x - n : ℚ)) ≤ (T : ℝ) + τ := by
    have := abs_le.mp hT
    linarith [this.2]
  have h2 : Real.exp 1 ^ n ≤ ((2.7182818286 : ℚ) : ℝ) ^ n := by
    apply pow_le_pow_left₀ (Real.exp_pos 1).le
    have := Real.exp_one_lt_d9
    push_cast
    linarith
  have hTτ : (0:ℝ) ≤ (T : ℝ) + τ :=
    le_trans (Real.exp_pos _).le h1
  calc Real.exp ((x - n : ℚ)) * Real.exp 1 ^ n
      ≤ ((T : ℝ) + τ) * ((2.7182818286 : ℚ) : ℝ) ^ n := by
        apply mul_le_mul h1 h2 (pow_nonneg (Real.exp_pos 1).le n) hTτ
    _ = (((T + τ) * (2.7182818286 : ℚ) ^ n : ℚ) : ℝ) := by
        push_cast
        ring

/-- **E5l: exp lower bound by shift.** -/
theorem exp_lower_shift {x : ℚ} (n : ℕ) {T τ : ℚ}
    (hT : |Real.exp ((x - n : ℚ)) - (T : ℝ)| ≤ (τ : ℝ))
    (hTτ : 0 ≤ T - τ) :
    (((T - τ) * (2.7182818283 : ℚ) ^ n : ℚ) : ℝ) ≤ Real.exp x := by
  have hsplit : Real.exp x = Real.exp ((x - n : ℚ)) * Real.exp 1 ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hsplit]
  have h1 : (T : ℝ) - τ ≤ Real.exp ((x - n : ℚ)) := by
    have := abs_le.mp hT
    linarith [this.1]
  have h2 : ((2.7182818283 : ℚ) : ℝ) ^ n ≤ Real.exp 1 ^ n := by
    apply pow_le_pow_left₀ (by norm_num)
    have := Real.exp_one_gt_d9
    push_cast
    linarith
  have hTτ' : (0:ℝ) ≤ (T : ℝ) - τ := by exact_mod_cast hTτ
  calc (((T - τ) * (2.7182818283 : ℚ) ^ n : ℚ) : ℝ)
      = ((T : ℝ) - τ) * ((2.7182818283 : ℚ) : ℝ) ^ n := by
        push_cast
        ring
    _ ≤ Real.exp ((x - n : ℚ)) * Real.exp 1 ^ n :=
        mul_le_mul h1 h2 (pow_nonneg (by norm_num) n)
          (Real.exp_pos _).le

/-- **E5log: the log certificate.**  `lo ≤ log m ≤ hi` from two exp
comparisons — each dischargeable by E5u/E5l plus kernel arithmetic. -/
theorem log_enclosure_nat {m : ℕ} {lo hi : ℚ} (hm : 1 ≤ m)
    (h1 : Real.exp lo ≤ m) (h2 : (m : ℝ) ≤ Real.exp hi) :
    (lo : ℝ) ≤ Real.log m ∧ Real.log m ≤ (hi : ℝ) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  exact ⟨(Real.le_log_iff_exp_le hm0).mpr h1,
    (Real.log_le_iff_le_exp hm0).mpr h2⟩

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.exp_enclosure
#print axioms CriticalLinePhasor.DVP.cos_enclosure
#print axioms CriticalLinePhasor.DVP.sin_enclosure
#print axioms CriticalLinePhasor.DVP.cos_angle_eval
#print axioms CriticalLinePhasor.DVP.sin_angle_eval
#print axioms CriticalLinePhasor.DVP.exp_upper_shift
#print axioms CriticalLinePhasor.DVP.exp_lower_shift
#print axioms CriticalLinePhasor.DVP.log_enclosure_nat
end AxiomAudit
