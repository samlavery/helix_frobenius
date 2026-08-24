import RequestProject.DVPTruncatedZeta

/-!
# E7: the Euler–Maclaurin ½-correction on the lattice tail

The compiled tail of `truncatedRep` decays like `x^{−σ−1}` per cell — too
slow at `σ = ½` for kernel evaluation (N ~ 10⁶).  Splitting
`{x} = ({x}−½) + ½`, the ½-mode telescopes EXACTLY to `N^{−s}/s` (DC first),
and the oscillating part gains a full power of decay through its vanishing
periodic primitive `P₂(x) = ({x}² − {x})/2`, `|P₂| ≤ 1/8`:
per cell, `∫ ({x}−½)·x^{−s−1} = (s+1)·∫ P₂·x^{−s−2}`.
-/

open Complex intervalIntegral Filter Topology

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The quadratic periodic primitive, on one cell, in affine coordinates. -/
private def P2c (m : ℕ) (x : ℝ) : ℂ :=
  (((x : ℂ) - m) ^ 2 - ((x : ℂ) - m)) / 2

/-- **E7b: the per-cell integration by parts.**  On `[m, m+1]` the centered
integrand trades one power of decay against the vanishing primitive. -/
theorem cell_centered_ibp {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : s ≠ -1) :
    ∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1),
        (((x : ℂ) - m) - 1/2) * (x : ℂ) ^ (-s - 1)
      = (s + 1) * ∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1),
          P2c m x * (x : ℂ) ^ (-s - 2) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hne1 : (-s - 1 : ℂ) ≠ 0 := by
    intro h
    exact hs (by linear_combination -h)
  -- the two derivative fields on the closed cell
  have hu : ∀ x ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1),
      HasDerivAt (fun y : ℝ => P2c m y) ((((x : ℂ) - m) - 1/2)) x := by
    intro x _
    have h1 : HasDerivAt (fun w : ℂ => w - (m : ℂ)) 1 ((x : ℝ) : ℂ) :=
      (hasDerivAt_id _).sub_const _
    have h2 : HasDerivAt (fun w : ℂ => (w - (m : ℂ)) * (w - (m : ℂ)))
        (1 * (((x : ℝ) : ℂ) - m) + (((x : ℝ) : ℂ) - m) * 1)
        ((x : ℝ) : ℂ) := h1.mul h1
    have heq : (fun w : ℂ => (w - (m : ℂ)) * (w - (m : ℂ)))
        = fun w : ℂ => (w - (m : ℂ)) ^ 2 := by
      funext w
      ring
    rw [heq] at h2
    have h3 := (h2.sub h1).div_const 2
    have hcomp := h3.comp_ofReal
    have hval : (1 * (((x : ℝ) : ℂ) - m) + (((x : ℝ) : ℂ) - m) * 1 - 1) / 2
        = (((x : ℂ) - m) - 1/2) := by
      ring
    rw [hval] at hcomp
    exact hcomp
  have hv : ∀ x ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1),
      HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ (-s - 1))
        ((-s - 1) * ((x : ℝ) : ℂ) ^ (-s - 2)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxpos : (0 : ℝ) < x := by linarith [hx.1]
    have hbase := hasDerivAt_ofReal_cpow_const hxpos.ne' hne1
    have h2 : (-s - 1 : ℂ) - 1 = -s - 2 := by ring
    rw [h2] at hbase
    exact hbase
  -- integrability of the derivative fields
  have h0mem : (0 : ℝ) ∉ Set.uIcc (m : ℝ) ((m : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    exact absurd h.1 (by linarith)
  have hu' : IntervalIntegrable (fun x : ℝ => (((x : ℂ) - m) - 1/2))
      MeasureTheory.volume (m : ℝ) ((m : ℝ) + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    continuity
  have hv' : IntervalIntegrable
      (fun x : ℝ => (-s - 1) * ((x : ℝ) : ℂ) ^ (-s - 2))
      MeasureTheory.volume (m : ℝ) ((m : ℝ) + 1) :=
    (intervalIntegral.intervalIntegrable_cpow (Or.inr h0mem)).const_mul _
  -- integration by parts
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  -- boundary vanishing: P₂(m) = P₂(m+1) = 0
  have hPm : P2c m (m : ℝ) = 0 := by
    unfold P2c
    push_cast
    ring
  have hPm1 : P2c m ((m : ℝ) + 1) = 0 := by
    unfold P2c
    push_cast
    ring
  rw [hPm, hPm1, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  -- hibp : ∫ P2c · ((−s−1)·x^{−s−2}) = −∫ (x−m−½)·x^{−s−1}
  have hconst : ∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1),
      P2c m x * ((-s - 1) * ((x : ℝ) : ℂ) ^ (-s - 2))
      = (-s - 1) * ∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1),
          P2c m x * ((x : ℝ) : ℂ) ^ (-s - 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hconst] at hibp
  linear_combination hibp

/-- **E7c: the per-cell bound with the extra power** — `|P₂| ≤ 1/8` gives
`‖∫ P₂·x^{−s−2}‖ ≤ (1/8)·m^{−σ−2}`. -/
theorem cell_P2_norm_le {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hσ : 0 ≤ s.re) :
    ‖∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1), P2c m x * (x : ℂ) ^ (-s - 2)‖
      ≤ (1/8 : ℝ) * ((m : ℝ)) ^ (-s.re - 2) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hbound : ∀ x ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1),
      ‖P2c m x * (x : ℂ) ^ (-s - 2)‖
        ≤ (1/8 : ℝ) * ((m : ℝ)) ^ (-s.re - 2) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxpos : (0 : ℝ) < x := by linarith [hx.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    have hP : ‖P2c m x‖ ≤ (1/8 : ℝ) := by
      unfold P2c
      set y : ℝ := x - m with hydef
      have hy0 : 0 ≤ y := by
        rw [hydef]
        linarith [hx.1]
      have hy1 : y ≤ 1 := by
        rw [hydef]
        linarith [hx.2]
      have hcast : (((x : ℂ) - m) ^ 2 - ((x : ℂ) - m)) / 2
          = (((y ^ 2 - y) / 2 : ℝ) : ℂ) := by
        rw [hydef]
        push_cast
        ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_le]
      constructor
      · nlinarith [sq_nonneg (y - 1/2)]
      · nlinarith [hy0, hy1]
    have h2 : x ^ ((-s - 2).re) ≤ ((m : ℝ)) ^ (-s.re - 2) := by
      have hre : (-s - 2).re = -s.re - 2 := by simp
      rw [hre]
      exact Real.rpow_le_rpow_of_nonpos hmpos hx.1 (by linarith)
    exact mul_le_mul hP h2 (Real.rpow_nonneg (le_of_lt hxpos) _)
      (by norm_num)
  have hmain : ‖∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1),
      P2c m x * (x : ℂ) ^ (-s - 2)‖
      ≤ (1/8 : ℝ) * ((m : ℝ)) ^ (-s.re - 2) * |((m : ℝ) + 1) - (m : ℝ)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      hbound x (Set.uIoc_subset_uIcc hx)
  have habs : |((m : ℝ) + 1) - (m : ℝ)| = 1 := by
    simp
  rw [habs, mul_one] at hmain
  exact hmain

/-- The cubic primitive of the ZERO-MEAN quadratic, on one cell, in affine
coordinates: `R(t) = t³/6 − t²/4 + t/12` with `R' = P₂ + 1/12` and
`R(0) = R(1) = 0`.  The `1/12` is the cell mean of `P₂` — the common mode
that the first-order bound leaves uncomputed. -/
private def P3c (m : ℕ) (x : ℝ) : ℂ :=
  ((x : ℂ) - m) ^ 3 / 6 - ((x : ℂ) - m) ^ 2 / 4 + ((x : ℂ) - m) / 12

/-- **The second integration by parts.**  Subtracting the cell mean `−1/12`
from `P₂` leaves an integrand whose primitive vanishes at both endpoints, so
one more power of decay is traded out. -/
theorem cell_P2_second_ibp {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : s ≠ -2) :
    ∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1),
        (P2c m x + 1/12) * (x : ℂ) ^ (-s - 2)
      = (s + 2) * ∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1),
          P3c m x * (x : ℂ) ^ (-s - 3) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hne2 : (-s - 2 : ℂ) ≠ 0 := by
    intro h
    exact hs (by linear_combination -h)
  have hu : ∀ x ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1),
      HasDerivAt (fun y : ℝ => P3c m y) (P2c m x + 1/12) x := by
    intro x _
    have h1 : HasDerivAt (fun w : ℂ => w - (m : ℂ)) 1 ((x : ℝ) : ℂ) :=
      (hasDerivAt_id _).sub_const _
    have hsq : HasDerivAt (fun w : ℂ => (w - (m : ℂ)) * (w - (m : ℂ)))
        (1 * (((x : ℝ) : ℂ) - m) + (((x : ℝ) : ℂ) - m) * 1) ((x : ℝ) : ℂ) :=
      h1.mul h1
    have heq2 : (fun w : ℂ => (w - (m : ℂ)) * (w - (m : ℂ)))
        = fun w : ℂ => (w - (m : ℂ)) ^ 2 := by funext w; ring
    rw [heq2] at hsq
    have hcu : HasDerivAt (fun w : ℂ => (w - (m : ℂ)) ^ 2 * (w - (m : ℂ)))
        ((1 * (((x : ℝ) : ℂ) - m) + (((x : ℝ) : ℂ) - m) * 1) * (((x : ℝ) : ℂ) - m)
          + (((x : ℝ) : ℂ) - m) ^ 2 * 1) ((x : ℝ) : ℂ) := hsq.mul h1
    have heq3 : (fun w : ℂ => (w - (m : ℂ)) ^ 2 * (w - (m : ℂ)))
        = fun w : ℂ => (w - (m : ℂ)) ^ 3 := by funext w; ring
    rw [heq3] at hcu
    have hsum := ((hcu.div_const 6).sub (hsq.div_const 4)).add (h1.div_const 12)
    have hcomp := hsum.comp_ofReal
    have hval : ((1 * (((x : ℝ) : ℂ) - m) + (((x : ℝ) : ℂ) - m) * 1)
            * (((x : ℝ) : ℂ) - m) + (((x : ℝ) : ℂ) - m) ^ 2 * 1) / 6
          - (1 * (((x : ℝ) : ℂ) - m) + (((x : ℝ) : ℂ) - m) * 1) / 4 + 1 / 12
        = P2c m x + 1/12 := by
      unfold P2c
      push_cast
      ring
    rw [hval] at hcomp
    exact hcomp
  have hv : ∀ x ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1),
      HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ (-s - 2))
        ((-s - 2) * ((x : ℝ) : ℂ) ^ (-s - 3)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxpos : (0 : ℝ) < x := by linarith [hx.1]
    have hbase := hasDerivAt_ofReal_cpow_const hxpos.ne' hne2
    have h2 : (-s - 2 : ℂ) - 1 = -s - 3 := by ring
    rw [h2] at hbase
    exact hbase
  have h0mem : (0 : ℝ) ∉ Set.uIcc (m : ℝ) ((m : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    exact absurd h.1 (by linarith)
  have hu' : IntervalIntegrable (fun x : ℝ => P2c m x + 1/12)
      MeasureTheory.volume (m : ℝ) ((m : ℝ) + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    unfold P2c
    continuity
  have hv' : IntervalIntegrable
      (fun x : ℝ => (-s - 2) * ((x : ℝ) : ℂ) ^ (-s - 3))
      MeasureTheory.volume (m : ℝ) ((m : ℝ) + 1) :=
    (intervalIntegral.intervalIntegrable_cpow (Or.inr h0mem)).const_mul _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hPm : P3c m (m : ℝ) = 0 := by
    unfold P3c
    push_cast
    ring
  have hPm1 : P3c m ((m : ℝ) + 1) = 0 := by
    unfold P3c
    push_cast
    ring
  rw [hPm, hPm1, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  have hconst : ∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1),
      P3c m x * ((-s - 2) * ((x : ℝ) : ℂ) ^ (-s - 3))
      = (-s - 2) * ∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1),
          P3c m x * ((x : ℝ) : ℂ) ^ (-s - 3) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hconst] at hibp
  linear_combination hibp

/-- **The second-order per-cell bound** — `|R| ≤ 1/48` on the cell gives
`‖∫ P₃·x^{−s−3}‖ ≤ (1/48)·m^{−σ−3}`: one more power of `N` than the
first-order bound. -/
theorem cell_P3_norm_le {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hσ : 0 ≤ s.re) :
    ‖∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1), P3c m x * (x : ℂ) ^ (-s - 3)‖
      ≤ (1/48 : ℝ) * ((m : ℝ)) ^ (-s.re - 3) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hbound : ∀ x ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1),
      ‖P3c m x * (x : ℂ) ^ (-s - 3)‖
        ≤ (1/48 : ℝ) * ((m : ℝ)) ^ (-s.re - 3) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxpos : (0 : ℝ) < x := by linarith [hx.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    have hP : ‖P3c m x‖ ≤ (1/48 : ℝ) := by
      unfold P3c
      set y : ℝ := x - m with hydef
      have hy0 : 0 ≤ y := by
        rw [hydef]; linarith [hx.1]
      have hy1 : y ≤ 1 := by
        rw [hydef]; linarith [hx.2]
      have hcast : ((x : ℂ) - m) ^ 3 / 6 - ((x : ℂ) - m) ^ 2 / 4
            + ((x : ℂ) - m) / 12
          = (((y ^ 3 / 6 - y ^ 2 / 4 + y / 12 : ℝ)) : ℂ) := by
        rw [hydef]
        push_cast
        ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      have ha0 : 0 ≤ y * (1 - y) := mul_nonneg hy0 (by linarith)
      have ha : y * (1 - y) ≤ 1/4 := by nlinarith [sq_nonneg (y - 1/2)]
      have hb1 : -1 ≤ 2*y - 1 := by linarith
      have hb2 : 2*y - 1 ≤ 1 := by linarith
      have heq : y ^ 3 / 6 - y ^ 2 / 4 + y / 12
          = -((y * (1 - y)) * (2*y - 1))/12 := by ring
      rw [heq, abs_le]
      constructor <;> nlinarith [ha0, ha, hb1, hb2]
    have h2 : x ^ ((-s - 3).re) ≤ ((m : ℝ)) ^ (-s.re - 3) := by
      have hre : (-s - 3).re = -s.re - 3 := by simp
      rw [hre]
      exact Real.rpow_le_rpow_of_nonpos hmpos hx.1 (by linarith)
    exact mul_le_mul hP h2 (Real.rpow_nonneg (le_of_lt hxpos) _) (by norm_num)
  have hmain : ‖∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1),
      P3c m x * (x : ℂ) ^ (-s - 3)‖
      ≤ (1/48 : ℝ) * ((m : ℝ)) ^ (-s.re - 3) * |((m : ℝ) + 1) - (m : ℝ)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      hbound x (Set.uIoc_subset_uIcc hx)
  have habs : |((m : ℝ) + 1) - (m : ℝ)| = 1 := by simp
  rw [habs, mul_one] at hmain
  exact hmain

/-- **The DC split of the first-order cell integral**: the `P₂` cell integral
is its exactly-computable common mode plus a residual carrying one more power
of decay.  This is what turns a `t²/N^{3/2}` error into `t³/N^{5/2}`. -/
theorem cell_P2_dc_split {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : s ≠ -2) :
    ∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1), P2c m x * (x : ℂ) ^ (-s - 2)
      = (s + 2) * (∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1),
            P3c m x * (x : ℂ) ^ (-s - 3))
        - (1/12) * ∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1), (x : ℂ) ^ (-s - 2) := by
  have hsplit : ∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1),
        (P2c m x + 1/12) * (x : ℂ) ^ (-s - 2)
      = (∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1), P2c m x * (x : ℂ) ^ (-s - 2))
        + (1/12) * ∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1), (x : ℂ) ^ (-s - 2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
    · apply intervalIntegral.integral_congr
      intro x _
      ring
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul
      · apply Continuous.continuousOn
        unfold P2c
        continuity
      · apply ContinuousOn.cpow_const
        · exact Complex.continuous_ofReal.continuousOn
        · intro x hx
          rw [Set.uIcc_of_le (by linarith)] at hx
          have hxpos : (0 : ℝ) < x := by
            have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
            linarith [hx.1]
          exact Or.inl (by simpa using hxpos)
    · apply IntervalIntegrable.const_mul
      have h0mem : (0 : ℝ) ∉ Set.uIcc (m : ℝ) ((m : ℝ) + 1) := by
        rw [Set.uIcc_of_le (by linarith)]
        intro h
        have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        exact absurd h.1 (by linarith)
      exact intervalIntegral.intervalIntegrable_cpow (Or.inr h0mem)
  rw [cell_P2_second_ibp hm hs] at hsplit
  linear_combination -hsplit

/-- The pure power cell integral, in closed form. -/
theorem cell_pure_integral {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : s ≠ 0) :
    ∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1), (x : ℂ) ^ (-s - 1)
      = ((((m : ℝ) : ℝ) : ℂ) ^ (-s) - ((((m : ℝ) + 1 : ℝ)) : ℂ) ^ (-s)) / s := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h0 : (0 : ℝ) ∉ Set.uIcc (m : ℝ) ((m : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    exact absurd h.1 (by linarith)
  rw [integral_cpow (Or.inr ⟨by
      intro h
      exact hs (by linear_combination -h - 1 + (1:ℂ)*0), h0⟩)]
  have he : (-s - 1) + 1 = -s := by ring
  rw [he]
  field_simp
  ring

/-- The pure power cell norm bound. -/
theorem cell_pure_norm_le {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hσ : 0 ≤ s.re) :
    ‖∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1), (x : ℂ) ^ (-s - 1)‖
      ≤ ((m : ℝ)) ^ (-s.re - 1) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hbound : ∀ x ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1),
      ‖(x : ℂ) ^ (-s - 1)‖ ≤ ((m : ℝ)) ^ (-s.re - 1) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxpos : (0 : ℝ) < x := by linarith [hx.1]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    exact Real.rpow_le_rpow_of_nonpos hmpos hx.1 (by linarith)
  have hmain : ‖∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1), (x : ℂ) ^ (-s - 1)‖
      ≤ ((m : ℝ)) ^ (-s.re - 1) * |((m : ℝ) + 1) - (m : ℝ)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      hbound x (Set.uIoc_subset_uIcc hx)
  have habs : |((m : ℝ) + 1) - (m : ℝ)| = 1 := by
    simp
  rw [habs, mul_one] at hmain
  exact hmain

/-- **E7a: the ½-mode telescoping — DC first.**  The pure lattice tail sums
EXACTLY: `Σ'_k ∫_{N+k}^{N+k+1} x^{−s−1} dx = N^{−s}/s`. -/
theorem half_mode_telescope {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hσ : 0 < s.re) :
    ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        (x : ℂ) ^ (-s - 1)
      = (((N : ℝ)) : ℂ) ^ (-s) / s := by
  have hs : s ≠ 0 := by
    intro h
    rw [h] at hσ
    simp at hσ
  set f : ℕ → ℂ := fun k => (((N + k : ℕ) : ℝ) : ℂ) ^ (-s) / s with hfdef
  -- each cell is a telescoping difference
  have hterm : ∀ k : ℕ,
      (∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        (x : ℂ) ^ (-s - 1)) = f k - f (k + 1) := by
    intro k
    rw [cell_pure_integral (by omega) hs]
    rw [hfdef]
    have hcast : (((N + (k + 1) : ℕ) : ℝ) : ℂ) = ((((N + k : ℕ) : ℝ) + 1 : ℝ) : ℂ) := by
      push_cast
      ring
    simp only [hcast]
    ring
  -- summability from the norm bound
  have hmaj : Summable (fun k : ℕ => (((N + k : ℕ) : ℝ)) ^ (-s.re - 1)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-s.re - 1)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact hbase.comp_injective (fun a b hab => by omega)
  have hsummable : Summable (fun k : ℕ =>
      ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        (x : ℂ) ^ (-s - 1)) := by
    apply Summable.of_norm_bounded hmaj
    intro k
    exact cell_pure_norm_le (by omega) (le_of_lt hσ)
  -- the tail vanishes
  have hf0 : Tendsto (fun K : ℕ => f K) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : ∀ K : ℕ, ‖f K‖ = (((N + K : ℕ) : ℝ)) ^ (-s.re) / ‖s‖ := by
      intro K
      rw [hfdef]
      simp only [norm_div]
      congr 1
      have hpos : (0 : ℝ) < ((N + K : ℕ) : ℝ) := by
        have : 1 ≤ N + K := by omega
        exact_mod_cast this
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re]
    simp only [hnorm]
    have htop : Tendsto (fun K : ℕ => ((N + K : ℕ) : ℝ)) atTop atTop := by
      apply tendsto_natCast_atTop_atTop.comp
      have h := tendsto_add_atTop_nat N
      exact h.congr fun K => by omega
    have hrpow : Tendsto (fun x : ℝ => x ^ (-s.re)) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop hσ
    have hcomp := hrpow.comp htop
    have := hcomp.div_const ‖s‖
    simpa using this
  -- telescoping partial sums
  have htel : ∀ K : ℕ, ∑ k ∈ Finset.range K, (f k - f (k + 1)) = f 0 - f K :=
    fun K => Finset.sum_range_sub' f K
  have hhs : HasSum (fun k : ℕ => f k - f (k + 1)) (f 0) := by
    have hsum2 : Summable (fun k : ℕ => f k - f (k + 1)) := by
      apply hsummable.congr
      intro k
      exact hterm k
    rw [hsum2.hasSum_iff_tendsto_nat]
    simp only [htel]
    have hconst : Tendsto (fun _ : ℕ => f 0) atTop (nhds (f 0)) :=
      tendsto_const_nhds
    have hsub := hconst.sub hf0
    simpa using hsub
  have htsum : ∑' k : ℕ, (f k - f (k + 1)) = f 0 := hhs.tsum_eq
  calc ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        (x : ℂ) ^ (-s - 1)
      = ∑' k : ℕ, (f k - f (k + 1)) := by
        apply tsum_congr
        exact hterm
    _ = f 0 := htsum
    _ = (((N : ℝ)) : ℂ) ^ (-s) / s := by
        rw [hfdef]
        norm_num

/-- **The exact defect identity.**  The Euler–Maclaurin head's defect IS
`−s(s+1)` times the `P₂` cell tail — no estimate yet.  Both the first- and
second-order enclosures are bounds on this one identity. -/
theorem zeta_defect_eq_P2_tail {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s
      - ((∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - (((N : ℝ)) : ℂ) ^ (-s) / 2)
      = -(s * (s + 1)) * (∑' k : ℕ,
          ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            P2c (N + k) x * (x : ℂ) ^ (-s - 2)) := by
  have hs : s ≠ 0 := by
    intro h
    rw [h] at hσ
    simp at hσ
  -- cpow continuity on a positive cell
  have hcell_cont : ∀ (m : ℕ), 1 ≤ m → ∀ (c : ℂ),
      ContinuousOn (fun x : ℝ => (x : ℂ) ^ c)
        (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
    intro m hm c x hx
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxpos : (0 : ℝ) < x := by linarith [hx.1]
    apply ContinuousAt.continuousWithinAt
    have hslit : ((x : ℝ) : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simpa using hxpos
    exact (continuousAt_cpow_const hslit).comp
      Complex.continuous_ofReal.continuousAt
  -- the majorant
  have hmaj2 : Summable (fun k : ℕ => (((N + k : ℕ) : ℝ)) ^ (-s.re - 2)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-s.re - 2)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact hbase.comp_injective (fun a b hab => by omega)
  -- P₂ tail summable
  have hP2sum : Summable (fun k : ℕ =>
      ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        P2c (N + k) x * (x : ℂ) ^ (-s - 2)) := by
    apply Summable.of_norm_bounded (hmaj2.mul_left (1/8 : ℝ))
    intro k
    exact cell_P2_norm_le (by omega) (le_of_lt hσ)
  -- pure tail summable
  have hmaj1 : Summable (fun k : ℕ => (((N + k : ℕ) : ℝ)) ^ (-s.re - 1)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-s.re - 1)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact hbase.comp_injective (fun a b hab => by omega)
  have hpure_sum : Summable (fun k : ℕ =>
      ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        (x : ℂ) ^ (-s - 1)) := by
    apply Summable.of_norm_bounded hmaj1
    intro k
    exact cell_pure_norm_le (by omega) (le_of_lt hσ)
  -- per-cell split: fract = centered + ½·pure, centered = (s+1)·P₂
  have hcell : ∀ k : ℕ,
      (∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      = (s + 1) * (∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
          P2c (N + k) x * (x : ℂ) ^ (-s - 2))
        + (1/2 : ℂ) * ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            (x : ℂ) ^ (-s - 1) := by
    intro k
    set m : ℕ := N + k with hmdef
    have hm : 1 ≤ m := by omega
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rw [fract_interval_congr m s]
    have hcongr : Set.EqOn
        (fun x : ℝ => ((x : ℂ) - (m : ℂ)) * (x : ℂ) ^ (-s - 1))
        (fun x : ℝ => (((x : ℂ) - m) - 1/2) * (x : ℂ) ^ (-s - 1)
          + (1/2 : ℂ) * (x : ℂ) ^ (-s - 1))
        (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
      intro x _
      ring
    rw [intervalIntegral.integral_congr hcongr]
    have hint_c : IntervalIntegrable
        (fun x : ℝ => (((x : ℂ) - m) - 1/2) * (x : ℂ) ^ (-s - 1))
        MeasureTheory.volume (m : ℝ) ((m : ℝ) + 1) := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul
      · apply Continuous.continuousOn
        continuity
      · exact hcell_cont m hm (-s - 1)
    have hint_h : IntervalIntegrable
        (fun x : ℝ => (1/2 : ℂ) * (x : ℂ) ^ (-s - 1))
        MeasureTheory.volume (m : ℝ) ((m : ℝ) + 1) := by
      apply ContinuousOn.intervalIntegrable
      exact (hcell_cont m hm (-s - 1)).const_smul (1/2 : ℂ) |>.congr
        (fun x hx => by simp [smul_eq_mul])
    rw [intervalIntegral.integral_add hint_c hint_h]
    rw [intervalIntegral.integral_const_mul]
    rw [cell_centered_ibp hm (by
      intro h
      rw [h] at hσ
      simp at hσ
      linarith)]
  -- tsum assembly
  have hT := truncated_zeta_pos_re hN hσ hs1
  rw [truncatedRep] at hT
  have htsum_split :
      (∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      = (s + 1) * (∑' k : ℕ,
          ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            P2c (N + k) x * (x : ℂ) ^ (-s - 2))
        + (1/2 : ℂ) * ((((N : ℝ)) : ℂ) ^ (-s) / s) := by
    calc (∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
        = ∑' k : ℕ, ((s + 1) *
            (∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
              P2c (N + k) x * (x : ℂ) ^ (-s - 2))
          + (1/2 : ℂ) * ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
              (x : ℂ) ^ (-s - 1)) := tsum_congr hcell
      _ = (s + 1) * (∑' k : ℕ,
            ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
              P2c (N + k) x * (x : ℂ) ^ (-s - 2))
          + (1/2 : ℂ) * ((((N : ℝ)) : ℂ) ^ (-s) / s) := by
          rw [Summable.tsum_add (hP2sum.mul_left _) (hpure_sum.mul_left _),
            tsum_mul_left, tsum_mul_left, half_mode_telescope hN hσ]
  rw [htsum_split] at hT
  -- isolate the defect
  have hdefect : riemannZeta s
      - ((∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - (((N : ℝ)) : ℂ) ^ (-s) / 2)
      = -(s * (s + 1)) * (∑' k : ℕ,
          ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            P2c (N + k) x * (x : ℂ) ^ (-s - 2)) := by
    rw [hT]
    field_simp
    ring
  exact hdefect

set_option maxHeartbeats 1600000 in
/-- **E7d: THE EULER–MACLAURIN ENCLOSURE OF ζ.**  On `Re s > 0`, `s ≠ 1`:
`‖ζ(s) − (Σ_{n≤N} n^{−s} + N^{1−s}/(s−1) − N^{−s}/2)‖
   ≤ ‖s‖·‖s+1‖/8 · Σ'_k (N+k)^{−σ−2}` — one full power of decay beyond the
compiled DVP tail.  DC first: the ½-mode is subtracted exactly, only the
centered oscillation is estimated. -/
theorem zeta_EM_enclosure {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - ((∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - (((N : ℝ)) : ℂ) ^ (-s) / 2)‖
      ≤ ‖s‖ * ‖s + 1‖ * (1/8)
        * ∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-s.re - 2) := by
  have hs : s ≠ 0 := by
    intro h
    rw [h] at hσ
    simp at hσ
  have hmaj2 : Summable (fun k : ℕ => (((N + k : ℕ) : ℝ)) ^ (-s.re - 2)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-s.re - 2)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact hbase.comp_injective (fun a b hab => by omega)
  have hP2sum : Summable (fun k : ℕ =>
      ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        P2c (N + k) x * (x : ℂ) ^ (-s - 2)) := by
    apply Summable.of_norm_bounded (hmaj2.mul_left (1/8 : ℝ))
    intro k
    exact cell_P2_norm_le (by omega) (le_of_lt hσ)
  have hdefect := zeta_defect_eq_P2_tail hN hσ hs1
  rw [hdefect]
  -- the norm bound
  rw [norm_mul]
  have hnorm_neg : ‖-(s * (s + 1))‖ = ‖s‖ * ‖s + 1‖ := by
    rw [norm_neg, norm_mul]
  rw [hnorm_neg]
  have htail : ‖∑' k : ℕ,
      ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        P2c (N + k) x * (x : ℂ) ^ (-s - 2)‖
      ≤ (1/8) * ∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-s.re - 2) := by
    calc ‖∑' k : ℕ,
        ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
          P2c (N + k) x * (x : ℂ) ^ (-s - 2)‖
        ≤ ∑' k : ℕ, ‖∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            P2c (N + k) x * (x : ℂ) ^ (-s - 2)‖ :=
          norm_tsum_le_tsum_norm (hP2sum.norm)
      _ ≤ ∑' k : ℕ, (1/8 : ℝ) * (((N + k : ℕ) : ℝ)) ^ (-s.re - 2) := by
          apply Summable.tsum_le_tsum
          · intro k
            exact cell_P2_norm_le (by omega) (le_of_lt hσ)
          · exact hP2sum.norm
          · exact hmaj2.mul_left _
      _ = (1/8) * ∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-s.re - 2) :=
          tsum_mul_left
  calc ‖s‖ * ‖s + 1‖ * ‖∑' k : ℕ,
      ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        P2c (N + k) x * (x : ℂ) ^ (-s - 2)‖
      ≤ ‖s‖ * ‖s + 1‖ * ((1/8) * ∑' k : ℕ,
          (((N + k : ℕ) : ℝ)) ^ (-s.re - 2)) := by
        apply mul_le_mul_of_nonneg_left htail
        positivity
    _ = ‖s‖ * ‖s + 1‖ * (1/8)
        * ∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-s.re - 2) := by
        ring

/-- **THE SECOND-ORDER EULER–MACLAURIN ENCLOSURE.**  The `B₂` term
`s·N^{−s−1}/12` is moved OUT of the error and INTO the head — it is the
common mode of `P₂` over each cell, telescoped exactly — leaving a residual
that carries one more power of `N`:

`‖ζ(s) − (Σ_{n≤N} n^{−s} + N^{1−s}/(s−1) − N^{−s}/2 + s·N^{−s−1}/12)‖
   ≤ ‖s‖‖s+1‖‖s+2‖/48 · Σ'_k (N+k)^{−σ−3}`.

Against the first-order bound the ratio is `≈ 63/N` at the campaign's
heights: at `t ≈ 630` the bound falls from 1.23 to 0.086 at `N = 900` and
from 0.130 to 0.0021 at `N = 4000`. -/
theorem zeta_EM_enclosure_second {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - ((∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - (((N : ℝ)) : ℂ) ^ (-s) / 2
        + s * (((N : ℝ)) : ℂ) ^ (-s - 1) / 12)‖
      ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * (1/48)
        * ∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-s.re - 3) := by
  have hs : s ≠ 0 := by
    intro h
    rw [h] at hσ
    simp at hσ
  have hs2 : s ≠ -2 := by
    intro h
    rw [h] at hσ
    simp at hσ
    linarith
  have hs1' : (s + 1) ≠ 0 := by
    intro h
    have : s.re = -1 := by
      have := congrArg Complex.re h
      simp at this
      linarith
    rw [this] at hσ
    linarith
  -- majorants
  have hmaj3 : Summable (fun k : ℕ => (((N + k : ℕ) : ℝ)) ^ (-s.re - 3)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-s.re - 3)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact hbase.comp_injective (fun a b hab => by omega)
  have hmaj2 : Summable (fun k : ℕ => (((N + k : ℕ) : ℝ)) ^ (-s.re - 2)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-s.re - 2)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact hbase.comp_injective (fun a b hab => by omega)
  have hP3sum : Summable (fun k : ℕ =>
      ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        P3c (N + k) x * (x : ℂ) ^ (-s - 3)) := by
    apply Summable.of_norm_bounded (hmaj3.mul_left (1/48 : ℝ))
    intro k
    exact cell_P3_norm_le (by omega) (le_of_lt hσ)
  have hpure2_sum : Summable (fun k : ℕ =>
      ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        (x : ℂ) ^ (-s - 2)) := by
    apply Summable.of_norm_bounded hmaj2
    intro k
    have := cell_pure_norm_le (m := N + k) (by omega) (s := s + 1)
      (by simp; linarith)
    have he : (-(s + 1) - 1 : ℂ) = -s - 2 := by ring
    have hre : (-(s + 1).re - 1) = -s.re - 2 := by simp; ring
    rw [he, hre] at this
    exact this
  -- the DC piece telescopes EXACTLY
  have hdc : (∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
      (x : ℂ) ^ (-s - 2)) = (((N : ℝ)) : ℂ) ^ (-s - 1) / (s + 1) := by
    have := half_mode_telescope (N := N) hN (s := s + 1) (by simp; linarith)
    have he : (-(s + 1) - 1 : ℂ) = -s - 2 := by ring
    have he2 : (-(s + 1) : ℂ) = -s - 1 := by ring
    rw [he, he2] at this
    exact this
  -- split the P₂ tail into DC + residual
  have hsplit : (∑' k : ℕ,
      ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        P2c (N + k) x * (x : ℂ) ^ (-s - 2))
      = (s + 2) * (∑' k : ℕ,
          ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            P3c (N + k) x * (x : ℂ) ^ (-s - 3))
        - (1/12) * ((((N : ℝ)) : ℂ) ^ (-s - 1) / (s + 1)) := by
    rw [← hdc]
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_sub
      (hP3sum.mul_left _) (hpure2_sum.mul_left _)]
    apply tsum_congr
    intro k
    exact cell_P2_dc_split (by omega) hs2
  have hdefect := zeta_defect_eq_P2_tail hN hσ hs1
  rw [hsplit] at hdefect
  -- move the DC term into the head
  have hmove : riemannZeta s - ((∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - (((N : ℝ)) : ℂ) ^ (-s) / 2
        + s * (((N : ℝ)) : ℂ) ^ (-s - 1) / 12)
      = -(s * (s + 1) * (s + 2)) * (∑' k : ℕ,
          ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            P3c (N + k) x * (x : ℂ) ^ (-s - 3)) := by
    have hexp : -(s * (s + 1)) * ((s + 2) * (∑' k : ℕ,
          ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            P3c (N + k) x * (x : ℂ) ^ (-s - 3))
        - (1/12) * ((((N : ℝ)) : ℂ) ^ (-s - 1) / (s + 1)))
        = -(s * (s + 1) * (s + 2)) * (∑' k : ℕ,
            ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
              P3c (N + k) x * (x : ℂ) ^ (-s - 3))
          + s * (((N : ℝ)) : ℂ) ^ (-s - 1) / 12 := by
      field_simp
      ring
    rw [hexp] at hdefect
    linear_combination hdefect
  rw [hmove, norm_mul]
  have hnorm_neg : ‖-(s * (s + 1) * (s + 2))‖ = ‖s‖ * ‖s + 1‖ * ‖s + 2‖ := by
    rw [norm_neg, norm_mul, norm_mul]
  rw [hnorm_neg]
  have htail : ‖∑' k : ℕ,
      ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        P3c (N + k) x * (x : ℂ) ^ (-s - 3)‖
      ≤ (1/48) * ∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-s.re - 3) := by
    calc ‖∑' k : ℕ,
        ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
          P3c (N + k) x * (x : ℂ) ^ (-s - 3)‖
        ≤ ∑' k : ℕ, ‖∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            P3c (N + k) x * (x : ℂ) ^ (-s - 3)‖ :=
          norm_tsum_le_tsum_norm (hP3sum.norm)
      _ ≤ ∑' k : ℕ, (1/48 : ℝ) * (((N + k : ℕ) : ℝ)) ^ (-s.re - 3) := by
          apply Summable.tsum_le_tsum
          · intro k
            exact cell_P3_norm_le (by omega) (le_of_lt hσ)
          · exact hP3sum.norm
          · exact hmaj3.mul_left _
      _ = (1/48) * ∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-s.re - 3) :=
          tsum_mul_left
  calc ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖∑' k : ℕ,
      ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        P3c (N + k) x * (x : ℂ) ^ (-s - 3)‖
      ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ((1/48) * ∑' k : ℕ,
          (((N + k : ℕ) : ℝ)) ^ (-s.re - 3)) := by
        apply mul_le_mul_of_nonneg_left htail
        positivity
    _ = ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * (1/48)
        * ∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-s.re - 3) := by
        ring

section UnitTelescope

variable {a σ : ℝ}

/-- The FTC identity on one unit cell:
`∫_a^{a+1} x^{−σ} = (a^{1−σ} − (a+1)^{1−σ})/(σ−1)`. -/
private theorem unit_cell_rpow_integral (ha : 1 ≤ a) (hσ : 1 < σ) :
    ∫ x : ℝ in a..(a + 1), x ^ (-σ)
      = (a ^ (1 - σ) - (a + 1) ^ (1 - σ)) / (σ - 1) := by
  have hderivG : ∀ x ∈ Set.uIcc a (a + 1),
      HasDerivAt (fun y : ℝ => -(y ^ (1 - σ) / (σ - 1))) (x ^ (-σ)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxpos : (0:ℝ) < x := by linarith [hx.1]
    have h1 := Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hxpos.ne')
    have h2 := (h1.div_const (σ - 1)).neg
    have hval : -((1 - σ) * x ^ (1 - σ - 1) / (σ - 1)) = x ^ (-σ) := by
      have hne : σ - 1 ≠ 0 := by linarith
      have hexp : (1 - σ - 1 : ℝ) = -σ := by ring
      rw [hexp]
      field_simp
      ring
    rw [hval] at h2
    exact h2
  have h0 : (0:ℝ) ∉ Set.uIcc a (a + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    exact absurd h.1 (by linarith)
  have hint : IntervalIntegrable (fun x : ℝ => x ^ (-σ))
      MeasureTheory.volume a (a + 1) :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr h0)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderivG hint
  rw [hftc]
  ring

/-- The unit telescope, upper side: `(a+1)^{−σ}` is at most the cell mass. -/
theorem rpow_unit_telescope_ge (ha : 1 ≤ a) (hσ : 1 < σ) :
    (a + 1) ^ (-σ) ≤ (a ^ (1 - σ) - (a + 1) ^ (1 - σ)) / (σ - 1) := by
  rw [← unit_cell_rpow_integral ha hσ]
  have hconst : (a + 1) ^ (-σ)
      = ∫ _ : ℝ in a..(a + 1), (a + 1) ^ (-σ) := by
    rw [intervalIntegral.integral_const]
    simp
  rw [hconst]
  have h0 : (0:ℝ) ∉ Set.uIcc a (a + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    exact absurd h.1 (by linarith)
  apply intervalIntegral.integral_mono_on (by linarith)
    intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_rpow (Or.inr h0))
  intro x hx
  exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hx.2 (by linarith)

/-- The unit telescope, lower side: the cell mass is at most `a^{−σ}`
(local copy; avoids importing the counts file). -/
theorem rpow_unit_telescope_le' (ha : 1 ≤ a) (hσ : 1 < σ) :
    (a ^ (1 - σ) - (a + 1) ^ (1 - σ)) / (σ - 1) ≤ a ^ (-σ) := by
  rw [← unit_cell_rpow_integral ha hσ]
  have hconst : a ^ (-σ)
      = ∫ _ : ℝ in a..(a + 1), a ^ (-σ) := by
    rw [intervalIntegral.integral_const]
    simp
  rw [hconst]
  have h0 : (0:ℝ) ∉ Set.uIcc a (a + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    exact absurd h.1 (by linarith)
  apply intervalIntegral.integral_mono_on (by linarith)
    (intervalIntegral.intervalIntegrable_rpow (Or.inr h0))
    intervalIntegrable_const
  intro x hx
  exact Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (by linarith)

end UnitTelescope

/-- **The numeric tail bound**: `Σ'_k (N+k)^{−p} ≤ N^{−p} + N^{1−p}/(p−1)`. -/
theorem tsum_shift_rpow_le {N : ℕ} (hN : 1 ≤ N) {p : ℝ} (hp : 1 < p) :
    ∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-p)
      ≤ ((N : ℝ)) ^ (-p) + ((N : ℝ)) ^ (1 - p) / (p - 1) := by
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  set F : ℕ → ℝ := fun k => (((N + k : ℕ) : ℝ)) ^ (1 - p) / (p - 1) with hFdef
  have hsummable : Summable (fun k : ℕ => (((N + k : ℕ) : ℝ)) ^ (-p)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-p)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact hbase.comp_injective (fun a b hab => by omega)
  -- telescoping sum of the majorant
  have hF0 : Tendsto (fun K : ℕ => F K) atTop (nhds 0) := by
    have htop : Tendsto (fun K : ℕ => ((N + K : ℕ) : ℝ)) atTop atTop := by
      apply tendsto_natCast_atTop_atTop.comp
      exact (tendsto_add_atTop_nat N).congr fun K => by omega
    have hrpow : Tendsto (fun x : ℝ => x ^ (-(p - 1))) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    have hcomp := (hrpow.comp htop).div_const (p - 1)
    have heq : ∀ K : ℕ, ((N + K : ℕ) : ℝ) ^ (-(p - 1)) / (p - 1) = F K := by
      intro K
      rw [hFdef]
      congr 1
      congr 1
      ring
    simp only [Function.comp_def] at hcomp
    simp only [heq] at hcomp
    simpa using hcomp
  have hFsum : HasSum (fun k : ℕ => F k - F (k + 1)) (F 0) := by
    have hsum2 : Summable (fun k : ℕ => F k - F (k + 1)) := by
      apply Summable.of_norm_bounded
        (g := fun k : ℕ => (((N + k : ℕ) : ℝ)) ^ (-p)) hsummable
      intro k
      rw [Real.norm_eq_abs]
      have hstep : F k - F (k + 1)
          = ((((N + k : ℕ) : ℝ)) ^ (1 - p)
            - ((((N + k : ℕ) : ℝ)) + 1) ^ (1 - p)) / (p - 1) := by
        rw [hFdef]
        dsimp only
        have hcast : (((N + (k + 1) : ℕ) : ℝ)) = (((N + k : ℕ) : ℝ)) + 1 := by
          push_cast
          ring
        rw [hcast]
        ring
      rw [hstep]
      have hlow : (0:ℝ) ≤ ((((N + k : ℕ) : ℝ)) ^ (1 - p)
          - ((((N + k : ℕ) : ℝ)) + 1) ^ (1 - p)) / (p - 1) := by
        apply div_nonneg _ (by linarith)
        have := Real.rpow_le_rpow_of_nonpos
          (x := ((N + k : ℕ) : ℝ)) (y := (((N + k : ℕ) : ℝ)) + 1)
          (by positivity) (by linarith) (by linarith : 1 - p ≤ 0)
        linarith
      rw [abs_of_nonneg hlow]
      exact rpow_unit_telescope_le'
        (by exact_mod_cast (by omega : 1 ≤ N + k)) hp
    rw [hsum2.hasSum_iff_tendsto_nat]
    simp only [Finset.sum_range_sub' F]
    have hconst : Tendsto (fun _ : ℕ => F 0) atTop (nhds (F 0)) :=
      tendsto_const_nhds
    have hsub := hconst.sub hF0
    simpa using hsub
  -- shift off the k = 0 term
  have hzero_add := hsummable.tsum_eq_zero_add
  rw [hzero_add]
  have hshift_le : ∑' k : ℕ, (((N + (k + 1) : ℕ) : ℝ)) ^ (-p)
      ≤ ((N : ℝ)) ^ (1 - p) / (p - 1) := by
    have hterm : ∀ k : ℕ, (((N + (k + 1) : ℕ) : ℝ)) ^ (-p)
        ≤ F k - F (k + 1) := by
      intro k
      have hcast : (((N + (k + 1) : ℕ) : ℝ)) = (((N + k : ℕ) : ℝ)) + 1 := by
        push_cast
        ring
      have hstep : F k - F (k + 1)
          = ((((N + k : ℕ) : ℝ)) ^ (1 - p)
            - ((((N + k : ℕ) : ℝ)) + 1) ^ (1 - p)) / (p - 1) := by
        rw [hFdef]
        dsimp only
        rw [hcast]
        ring
      rw [hcast, hstep]
      exact rpow_unit_telescope_ge
        (by exact_mod_cast (by omega : 1 ≤ N + k)) hp
    have hsum3 : Summable (fun k : ℕ => (((N + (k + 1) : ℕ) : ℝ)) ^ (-p)) := by
      have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-p)) := by
        rw [Real.summable_nat_rpow]
        linarith
      exact hbase.comp_injective (fun a b hab => by omega)
    calc ∑' k : ℕ, (((N + (k + 1) : ℕ) : ℝ)) ^ (-p)
        ≤ ∑' k : ℕ, (F k - F (k + 1)) :=
          Summable.tsum_le_tsum hterm hsum3 hFsum.summable
      _ = F 0 := hFsum.tsum_eq
      _ = ((N : ℝ)) ^ (1 - p) / (p - 1) := by
          rw [hFdef]
          norm_num
  have hfirst : (((N + 0 : ℕ) : ℝ)) ^ (-p) = ((N : ℝ)) ^ (-p) := by
    norm_num
  rw [hfirst]
  linarith [hshift_le]

/-- **The two-sided Hurwitz tail bracket**: for `p > 1` and shift `c` with
`N + c − 1 ≥ 1`,
`(N+c)^{1−p}/(p−1) ≤ Σ'ₖ (N+k+c)^{−p} ≤ (N+c−1)^{1−p}/(p−1)` —
both sides from the unit-cell FTC telescopes.  Every series tail in the
θ-anchor numerics reduces to two rational endpoints through this. -/
theorem tsum_rpow_tail_bracket {c : ℝ} {N : ℕ} {p : ℝ} (hp : 1 < p)
    (hc1 : 1 ≤ (N:ℝ) + c - 1) :
    ((N:ℝ) + c) ^ (1-p) / (p-1)
        ≤ (∑' k : ℕ, (((N:ℝ) + (k:ℝ) + c)) ^ (-p))
      ∧ (∑' k : ℕ, (((N:ℝ) + (k:ℝ) + c)) ^ (-p))
        ≤ ((N:ℝ) + c - 1) ^ (1-p) / (p-1) := by
  have hNc : (2:ℝ) ≤ (N:ℝ) + c := by linarith
  have hsummable : Summable
      (fun k : ℕ => (((N:ℝ) + (k:ℝ) + c)) ^ (-p)) := by
    have hmaj : Summable (fun k : ℕ => (((k+1:ℕ)):ℝ) ^ (-p)) := by
      have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-p)) := by
        rw [Real.summable_nat_rpow]
        linarith
      exact hbase.comp_injective (fun a b hab => by omega)
    apply Summable.of_nonneg_of_le
      (fun (k : ℕ) => Real.rpow_nonneg
        (show (0:ℝ) ≤ (N:ℝ) + (k:ℝ) + c by
          linarith [Nat.cast_nonneg (α := ℝ) k]) _)
      _ hmaj
    intro k
    have hcast : (((k+1:ℕ)):ℝ) = (k:ℝ) + 1 := by push_cast; ring
    rw [hcast]
    apply Real.rpow_le_rpow_of_nonpos
      (show (0:ℝ) < (k:ℝ) + 1 by positivity)
      (show (k:ℝ) + 1 ≤ (N:ℝ) + (k:ℝ) + c by linarith)
      (by linarith)
  -- the telescoping field at a general shift d with N + d ≥ 1
  have htelesum : ∀ d : ℝ, 1 ≤ (N:ℝ) + d →
      HasSum (fun k : ℕ =>
        ((N:ℝ) + (k:ℝ) + d) ^ (1-p) / (p-1)
          - ((N:ℝ) + ((k:ℝ)+1) + d) ^ (1-p) / (p-1))
        (((N:ℝ) + d) ^ (1-p) / (p-1)) := by
    intro d hd
    set F : ℕ → ℝ := fun k => ((N:ℝ) + (k:ℝ) + d) ^ (1-p) / (p-1) with hF
    have hFpos : ∀ k, 0 ≤ F k := by
      intro k
      rw [hF]
      dsimp only
      refine div_nonneg ?_ (show (0:ℝ) ≤ p - 1 by linarith)
      apply Real.rpow_nonneg
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hsteple : ∀ k : ℕ, 0 ≤ F k - F (k+1) := by
      intro k
      rw [hF]
      dsimp only
      push_cast
      rw [sub_nonneg]
      refine div_le_div_of_nonneg_right ?_ (show (0:ℝ) ≤ p - 1 by linarith)
      refine Real.rpow_le_rpow_of_nonpos ?_ ?_ (by linarith)
      · linarith [Nat.cast_nonneg (α := ℝ) k]
      · linarith
    have hFdiff : ∀ k : ℕ, F k - F (k+1)
        = ((N:ℝ) + (k:ℝ) + d) ^ (1-p) / (p-1)
          - ((N:ℝ) + ((k:ℝ)+1) + d) ^ (1-p) / (p-1) := by
      intro k
      rw [hF]
      push_cast
      ring
    have hsum2 : Summable (fun k : ℕ => F k - F (k+1)) := by
      have hbnd : ∀ K : ℕ, ∑ k ∈ Finset.range K, (F k - F (k+1)) ≤ F 0 := by
        intro K
        rw [Finset.sum_range_sub' F]
        linarith [hFpos K]
      exact summable_of_sum_range_le hsteple hbnd
    have hF0tend : Filter.Tendsto (fun K : ℕ => F K)
        Filter.atTop (nhds 0) := by
      rw [hF]
      have htop : Filter.Tendsto (fun K : ℕ => ((N:ℝ) + (K:ℝ) + d))
          Filter.atTop Filter.atTop := by
        apply Filter.tendsto_atTop_add_const_right
        apply Filter.tendsto_atTop_add_const_left
        exact tendsto_natCast_atTop_atTop
      have hrpow : Filter.Tendsto (fun x : ℝ => x ^ (-(p-1)))
          Filter.atTop (nhds 0) := tendsto_rpow_neg_atTop (by linarith)
      have hcomp := (hrpow.comp htop).div_const (p-1)
      have heq : ∀ K : ℕ, ((N:ℝ) + (K:ℝ) + d) ^ (-(p-1)) / (p-1)
          = ((N:ℝ) + (K:ℝ) + d) ^ (1-p) / (p-1) := by
        intro K
        congr 2
        ring
      simp only [Function.comp_def] at hcomp
      simp only [heq] at hcomp
      simpa using hcomp
    have hhs : HasSum (fun k : ℕ => F k - F (k+1)) (F 0) := by
      rw [hsum2.hasSum_iff_tendsto_nat]
      simp only [Finset.sum_range_sub' F]
      have hconst : Filter.Tendsto (fun _ : ℕ => F 0)
          Filter.atTop (nhds (F 0)) := tendsto_const_nhds
      have hsub := hconst.sub hF0tend
      simpa using hsub
    have hF0 : F 0 = ((N:ℝ) + d) ^ (1-p) / (p-1) := by
      rw [hF]
      norm_num
    rw [hF0] at hhs
    exact hhs.congr_fun (fun k => (hFdiff k).symm)
  constructor
  · -- lower: per-term telescope ≤ the summand, telescoped
    have hts := htelesum c (by linarith)
    apply le_trans (le_of_eq hts.tsum_eq.symm)
    apply Summable.tsum_le_tsum _ hts.summable hsummable
    intro k
    have ha1 : (1:ℝ) ≤ (N:ℝ) + (k:ℝ) + c := by
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hcell := rpow_unit_telescope_le' ha1 hp
    have hplus : ((N:ℝ) + ((k:ℝ)+1) + c) = ((N:ℝ) + (k:ℝ) + c) + 1 := by
      ring
    rw [hplus]
    calc ((N:ℝ) + (k:ℝ) + c) ^ (1-p) / (p-1)
          - (((N:ℝ) + (k:ℝ) + c) + 1) ^ (1-p) / (p-1)
        = (((N:ℝ) + (k:ℝ) + c) ^ (1-p)
          - (((N:ℝ) + (k:ℝ) + c) + 1) ^ (1-p)) / (p-1) := by
          ring
      _ ≤ ((N:ℝ) + (k:ℝ) + c) ^ (-p) := hcell
  · -- upper: the summand ≤ per-term telescope at shift c − 1, telescoped
    have hts := htelesum (c - 1) (by linarith)
    have hval : ((N:ℝ) + (c - 1)) = ((N:ℝ) + c - 1) := by ring
    rw [hval] at hts
    apply le_trans _ (le_of_eq hts.tsum_eq)
    apply Summable.tsum_le_tsum _ hsummable hts.summable
    intro k
    have ha1 : (1:ℝ) ≤ (N:ℝ) + (k:ℝ) + (c - 1) := by
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hcell := rpow_unit_telescope_ge ha1 hp
    have hplus1 : ((N:ℝ) + (k:ℝ) + (c-1)) + 1 = ((N:ℝ) + (k:ℝ) + c) := by
      ring
    rw [hplus1] at hcell
    have hplus2 : ((N:ℝ) + ((k:ℝ)+1) + (c-1)) = ((N:ℝ) + (k:ℝ) + c) := by
      ring
    rw [hplus2]
    calc ((N:ℝ) + (k:ℝ) + c) ^ (-p)
        ≤ (((N:ℝ) + (k:ℝ) + (c-1)) ^ (1-p)
          - ((N:ℝ) + (k:ℝ) + c) ^ (1-p)) / (p-1) := hcell
      _ = ((N:ℝ) + (k:ℝ) + (c-1)) ^ (1-p) / (p-1)
          - ((N:ℝ) + (k:ℝ) + c) ^ (1-p) / (p-1) := by
          ring

/-- The FTC identity on a unit cell for exponents in `(−1, 0)`:
`∫_a^{a+1} x^{−q} = ((a+1)^{1−q} − a^{1−q})/(1−q)`. -/
theorem unit_cell_rpow_integral_lt {a q : ℝ} (ha : 1 ≤ a)
    (hq0 : 0 < q) (hq1 : q < 1) :
    ∫ x : ℝ in a..(a + 1), x ^ (-q)
      = ((a + 1) ^ (1 - q) - a ^ (1 - q)) / (1 - q) := by
  have hderivG : ∀ x ∈ Set.uIcc a (a + 1),
      HasDerivAt (fun y : ℝ => y ^ (1 - q) / (1 - q)) (x ^ (-q)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxpos : (0:ℝ) < x := by linarith [hx.1]
    have h1 := Real.hasDerivAt_rpow_const (p := 1 - q) (Or.inl hxpos.ne')
    have h2 := h1.div_const (1 - q)
    have hval : (1 - q) * x ^ (1 - q - 1) / (1 - q) = x ^ (-q) := by
      have hne : (1:ℝ) - q ≠ 0 := by linarith
      have hexp : (1 - q - 1 : ℝ) = -q := by ring
      rw [hexp]
      field_simp
    rw [hval] at h2
    exact h2
  have h0 : (0:ℝ) ∉ Set.uIcc a (a + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    exact absurd h.1 (by linarith)
  have hint : IntervalIntegrable (fun x : ℝ => x ^ (-q))
      MeasureTheory.volume a (a + 1) :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr h0)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderivG hint
  rw [hftc]
  ring

/-- Per-cell upper bound for the decreasing integrand:
`((a+1)^{1−q} − a^{1−q})/(1−q) ≤ a^{−q}`. -/
theorem rpow_unit_cell_le_lt {a q : ℝ} (ha : 1 ≤ a)
    (hq0 : 0 < q) (hq1 : q < 1) :
    ((a + 1) ^ (1 - q) - a ^ (1 - q)) / (1 - q) ≤ a ^ (-q) := by
  rw [← unit_cell_rpow_integral_lt ha hq0 hq1]
  have hconst : a ^ (-q) = ∫ _ : ℝ in a..(a + 1), a ^ (-q) := by
    rw [intervalIntegral.integral_const]
    simp
  rw [hconst]
  have h0 : (0:ℝ) ∉ Set.uIcc a (a + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    exact absurd h.1 (by linarith)
  apply intervalIntegral.integral_mono_on (by linarith)
    (intervalIntegral.intervalIntegrable_rpow (Or.inr h0))
    intervalIntegrable_const
  intro x hx
  exact Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (by linarith)

/-- **The sub-unit-exponent partial-sum bound**:
`Σ_{n ≤ N} n^{−q} ≤ 1 + N^{1−q}/(1−q)` for `0 < q < 1`. -/
theorem partial_rpow_le_lt {N : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∑ n ∈ Finset.range (N + 1), ((n:ℝ)) ^ (-q)
      ≤ 1 + ((N:ℝ)) ^ (1 - q) / (1 - q) := by
  induction N with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_zero]
    have h0 : ((0:ℕ):ℝ) ^ (-q) = 0 := by
      rw [Nat.cast_zero]
      exact Real.zero_rpow (by linarith)
    rw [h0]
    have hnn : (0:ℝ) ≤ ((0:ℕ):ℝ) ^ (1 - q) / (1 - q) := by
      apply div_nonneg _ (by linarith)
      exact Real.rpow_nonneg (by norm_num) _
    linarith
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      rw [Finset.sum_range_succ, Finset.sum_range_zero]
      have h0 : ((0:ℕ):ℝ) ^ (-q) = 0 := by
        rw [Nat.cast_zero]
        exact Real.zero_rpow (by linarith)
      have h1 : (((0+1:ℕ)):ℝ) ^ (-q) = 1 := by
        norm_num
      rw [h0, h1]
      have hnn : (0:ℝ) ≤ (((0+1:ℕ)):ℝ) ^ (1 - q) / (1 - q) := by
        apply div_nonneg _ (by linarith)
        exact Real.rpow_nonneg (by positivity) _
      push_cast at hnn ⊢
      linarith
    · have hcell := rpow_unit_cell_le_lt
        (a := ((n:ℕ):ℝ)) (by exact_mod_cast hnpos) hq0 hq1
      have hcast : (((n+1:ℕ)):ℝ) = ((n:ℕ):ℝ) + 1 := by
        push_cast
        ring
      have hstep : (((n+1:ℕ)):ℝ) ^ (-q)
          ≤ ((((n:ℕ):ℝ) + 1) ^ (1 - q) - ((n:ℕ):ℝ) ^ (1 - q)) / (1 - q) := by
        rw [hcast]
        rw [← unit_cell_rpow_integral_lt (by exact_mod_cast hnpos) hq0 hq1]
        have hconst : (((n:ℕ):ℝ) + 1) ^ (-q)
            = ∫ _ : ℝ in ((n:ℕ):ℝ)..(((n:ℕ):ℝ) + 1),
                (((n:ℕ):ℝ) + 1) ^ (-q) := by
          rw [intervalIntegral.integral_const]
          simp
        rw [hconst]
        have h0 : (0:ℝ) ∉ Set.uIcc ((n:ℕ):ℝ) (((n:ℕ):ℝ) + 1) := by
          rw [Set.uIcc_of_le (by linarith)]
          intro h
          have h1 : (1:ℝ) ≤ ((n:ℕ):ℝ) := by exact_mod_cast hnpos
          exact absurd h.1 (by linarith)
        apply intervalIntegral.integral_mono_on (by linarith)
          intervalIntegrable_const
          (intervalIntegral.intervalIntegrable_rpow (Or.inr h0))
        intro x hx
        have h1 : (1:ℝ) ≤ ((n:ℕ):ℝ) := by exact_mod_cast hnpos
        exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hx.2
          (by linarith)
      calc ∑ i ∈ Finset.range (n + 1), ((i:ℝ)) ^ (-q)
            + (((n+1:ℕ)):ℝ) ^ (-q)
          ≤ (1 + ((n:ℝ)) ^ (1 - q) / (1 - q))
            + ((((n:ℕ):ℝ) + 1) ^ (1 - q) - ((n:ℕ):ℝ) ^ (1 - q)) / (1 - q) := by
            push_cast at hstep ⊢
            exact add_le_add ih hstep
        _ = 1 + (((n:ℕ):ℝ) + 1) ^ (1 - q) / (1 - q) := by
            push_cast
            ring
        _ = 1 + (((n+1:ℕ)):ℝ) ^ (1 - q) / (1 - q) := by
            rw [hcast]

/-- **The closed-form Euler–Maclaurin enclosure** — everything on the right
is elementary in `N` and `s`. -/
theorem zeta_EM_enclosure_numeric {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - ((∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - (((N : ℝ)) : ℂ) ^ (-s) / 2)‖
      ≤ ‖s‖ * ‖s + 1‖ * (1/8)
        * (((N : ℝ)) ^ (-s.re - 2) + ((N : ℝ)) ^ (-s.re - 1) / (s.re + 1)) := by
  have h1 := zeta_EM_enclosure hN hσ hs1
  have hp : (1:ℝ) < s.re + 2 := by linarith
  have h2 := tsum_shift_rpow_le hN hp
  have hexp1 : -(s.re + 2) = -s.re - 2 := by ring
  have hexp2 : (1 : ℝ) - (s.re + 2) = -s.re - 1 := by ring
  have hexp3 : s.re + 2 - 1 = s.re + 1 := by ring
  rw [hexp1, hexp2, hexp3] at h2
  calc ‖riemannZeta s - ((∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - (((N : ℝ)) : ℂ) ^ (-s) / 2)‖
      ≤ ‖s‖ * ‖s + 1‖ * (1/8)
        * ∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-s.re - 2) := h1
    _ ≤ ‖s‖ * ‖s + 1‖ * (1/8)
        * (((N : ℝ)) ^ (-s.re - 2) + ((N : ℝ)) ^ (-s.re - 1) / (s.re + 1)) := by
        exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **The closed-form second-order enclosure** — the `Σ'(N+k)^{−σ−3}` tail
replaced by its Hurwitz bound, so every quantity is elementary and the
station/segment generators can consume it directly:

`‖ζ(s) − (head + s·N^{−s−1}/12)‖
   ≤ ‖s‖‖s+1‖‖s+2‖/48 · (N^{−σ−3} + N^{−σ−2}/(σ+2))`. -/
theorem zeta_EM_enclosure_second_numeric {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - ((∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - (((N : ℝ)) : ℂ) ^ (-s) / 2
        + s * (((N : ℝ)) : ℂ) ^ (-s - 1) / 12)‖
      ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * (1/48)
        * (((N : ℝ)) ^ (-s.re - 3) + ((N : ℝ)) ^ (-s.re - 2) / (s.re + 2)) := by
  have h1 := zeta_EM_enclosure_second hN hσ hs1
  have hp : (1:ℝ) < s.re + 3 := by linarith
  have h2 := tsum_shift_rpow_le hN hp
  have hexp1 : -(s.re + 3) = -s.re - 3 := by ring
  have hexp2 : (1 : ℝ) - (s.re + 3) = -s.re - 2 := by ring
  have hexp3 : s.re + 3 - 1 = s.re + 2 := by ring
  rw [hexp1, hexp2, hexp3] at h2
  calc ‖riemannZeta s - ((∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - (((N : ℝ)) : ℂ) ^ (-s) / 2
        + s * (((N : ℝ)) : ℂ) ^ (-s - 1) / 12)‖
      ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * (1/48)
        * ∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-s.re - 3) := h1
    _ ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * (1/48)
        * (((N : ℝ)) ^ (-s.re - 3) + ((N : ℝ)) ^ (-s.re - 2) / (s.re + 2)) := by
        exact mul_le_mul_of_nonneg_left h2 (by positivity)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cell_centered_ibp
#print axioms CriticalLinePhasor.DVP.cell_P2_norm_le
#print axioms CriticalLinePhasor.DVP.cell_pure_integral
#print axioms CriticalLinePhasor.DVP.cell_pure_norm_le
#print axioms CriticalLinePhasor.DVP.half_mode_telescope
#print axioms CriticalLinePhasor.DVP.zeta_EM_enclosure
#print axioms CriticalLinePhasor.DVP.rpow_unit_telescope_ge
#print axioms CriticalLinePhasor.DVP.tsum_shift_rpow_le
#print axioms CriticalLinePhasor.DVP.zeta_EM_enclosure_numeric
#print axioms CriticalLinePhasor.DVP.tsum_rpow_tail_bracket
end AxiomAudit

section SecondOrderAudit
#print axioms CriticalLinePhasor.DVP.zeta_EM_enclosure_second_numeric
#print axioms CriticalLinePhasor.DVP.zeta_defect_eq_P2_tail
#print axioms CriticalLinePhasor.DVP.zeta_EM_enclosure_second
#print axioms CriticalLinePhasor.DVP.cell_P2_second_ibp
#print axioms CriticalLinePhasor.DVP.cell_P3_norm_le
#print axioms CriticalLinePhasor.DVP.cell_P2_dc_split
end SecondOrderAudit
