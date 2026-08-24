import RequestProject.DVPCellMass

/-!
# The local ζ bound at heights 40–60: `‖ζ‖ ≤ 35`

A general-purpose instrument (any Cauchy `ζ'` consumer gets a ~30× sharper
constant than the global `200·|t|^{3/4} ≈ 4211` at `t ≈ 58`): on
`σ ≥ 1/4`, `40 ≤ |Im s| ≤ 60`, the EM enclosure at `N = 58` gives
`‖ζ(s)‖ ≤ 35` — head sum by the `q = 1/4` integral bracket (≤ 30.34), pole
term by the height floor (≤ 0.55), half term (≤ 0.5), remainder (≤ 2.76).
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.DVP

/-- `58^{3/4} ≤ 22`. -/
theorem rpow_58_34 : ((58:ℝ)) ^ ((3:ℝ)/4) ≤ 22 := by
  by_contra hc
  push_neg at hc
  have h1 : (((58:ℝ)) ^ ((3:ℝ)/4)) ^ (4:ℕ) = 58 ^ (3:ℕ) := by
    rw [← Real.rpow_natCast (((58:ℝ)) ^ ((3:ℝ)/4)) 4,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 58)]
    norm_num
  have hpow : (22:ℝ)^(4:ℕ) < (((58:ℝ)) ^ ((3:ℝ)/4))^(4:ℕ) :=
    pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
  rw [h1] at hpow
  norm_num at hpow

/-- `58^{-1/4} ≤ 2/5`. -/
theorem rpow_58_neg14 : ((58:ℝ)) ^ (-((1:ℝ)/4)) ≤ 2/5 := by
  have hq : ((5:ℝ)/2) ≤ ((58:ℝ)) ^ ((1:ℝ)/4) := by
    by_contra hc
    push_neg at hc
    have h1 : (((58:ℝ)) ^ ((1:ℝ)/4)) ^ (4:ℕ) = 58 := by
      rw [← Real.rpow_natCast (((58:ℝ)) ^ ((1:ℝ)/4)) 4,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 58)]
      norm_num
    have hpow : (((58:ℝ)) ^ ((1:ℝ)/4))^(4:ℕ) < ((5:ℝ)/2)^(4:ℕ) :=
      pow_lt_pow_left₀ hc
        (Real.rpow_nonneg (by norm_num) _) (by norm_num)
    rw [h1] at hpow
    norm_num at hpow
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 58)]
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  linarith

/-- **The local ζ bound**: `‖ζ(s)‖ ≤ 35` for `σ ≥ 1/4`, `40 ≤ |Im s| ≤ 60`. -/
theorem zeta_local_bound {s : ℂ} (hσl : (1:ℝ)/4 ≤ s.re)
    (himl : (40:ℝ) ≤ |s.im|) (himu : |s.im| ≤ 60) :
    ‖riemannZeta s‖ ≤ 35 := by
  rcases le_or_gt 2 s.re with hσ2 | hσ2
  · have := zeta_norm_le_edge hσ2
    linarith
  have hσ0 : (0:ℝ) < s.re := by linarith
  have him0 : s.im ≠ 0 := by
    intro h
    rw [h] at himl
    simp at himl
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at him0
    simp at him0
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at him0
    simp at him0
  have hEM := zeta_EM_enclosure_numeric (N := 58) (by norm_num) hσ0 hs1
  -- head sum ≤ 1 + (4/3)·22
  have hhead : ‖∑ n ∈ Finset.range 59, (((n : ℝ)) : ℂ) ^ (-s)‖
      ≤ 1 + (4/3) * 22 := by
    calc ‖∑ n ∈ Finset.range 59, (((n : ℝ)) : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Finset.range 59, ‖(((n : ℝ)) : ℂ) ^ (-s)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range 59, ((n:ℝ)) ^ (-((1:ℝ)/4)) := by
          apply Finset.sum_le_sum
          intro n _
          rcases Nat.eq_zero_or_pos n with h0 | hpos
          · subst h0
            have hz : (((0:ℕ):ℝ) : ℂ) ^ (-s) = 0 := by
              rw [show (((0:ℕ):ℝ) : ℂ) = 0 by norm_num]
              exact Complex.zero_cpow (neg_ne_zero.mpr hs0)
            rw [hz, norm_zero]
            positivity
          · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hpos
            have hnc : ‖(((n : ℝ)) : ℂ) ^ (-s)‖ = ((n:ℝ)) ^ (-s.re) := by
              rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
              simp
            rw [hnc]
            apply Real.rpow_le_rpow_of_exponent_le hn1
            linarith
      _ ≤ 1 + ((58:ℝ)) ^ ((3:ℝ)/4) / ((3:ℝ)/4) := by
          have h := partial_rpow_le_lt (N := 58)
            (q := (1:ℝ)/4) (by norm_num) (by norm_num)
          have hexp : (1 - (1:ℝ)/4) = (3:ℝ)/4 := by norm_num
          rw [hexp] at h
          convert h using 2
          norm_num
      _ ≤ 1 + (4/3) * 22 := by
          nlinarith [rpow_58_34,
            Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 58) ((3:ℝ)/4)]
  -- pole term ≤ 22/40
  have hpole : ‖(((58:ℝ)) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 22/40 := by
    rw [norm_div]
    have hnum : ‖(((58:ℝ)) : ℂ) ^ (1 - s)‖ ≤ 22 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 58)]
      have hre : (1 - s).re = 1 - s.re := by simp
      rw [hre]
      calc ((58:ℝ)) ^ (1 - s.re) ≤ ((58:ℝ)) ^ ((3:ℝ)/4) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ ≤ 22 := rpow_58_34
    have hden : (40:ℝ) ≤ ‖s - 1‖ := by
      have h1 := Complex.abs_im_le_norm (s - 1)
      have h2 : (s - 1).im = s.im := by simp
      rw [h2] at h1
      linarith
    have hden0 : (0:ℝ) < ‖s - 1‖ := by linarith
    rw [div_le_div_iff₀ hden0 (by norm_num)]
    nlinarith [hnum, hden, norm_nonneg ((((58:ℝ)) : ℂ) ^ (1 - s))]
  -- half term ≤ 1/2·(2/5)
  have hhalf : ‖(((58:ℝ)) : ℂ) ^ (-s) / 2‖ ≤ 1/5 := by
    rw [norm_div]
    have hnum : ‖(((58:ℝ)) : ℂ) ^ (-s)‖ ≤ 2/5 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 58)]
      have hre : (-s).re = -s.re := by simp
      rw [hre]
      calc ((58:ℝ)) ^ (-s.re) ≤ ((58:ℝ)) ^ (-((1:ℝ)/4)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ ≤ 2/5 := rpow_58_neg14
    have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
    rw [h2]
    linarith
  -- remainder ≤ 62·63/8·(58^{-2}·(2/5) + 58^{-1}·(2/5)/(5/4))
  have herr : ‖s‖ * ‖s + 1‖ * (1/8)
      * (((58:ℝ)) ^ (-s.re - 2) + ((58:ℝ)) ^ (-s.re - 1) / (s.re + 1))
      ≤ 3 := by
    have hsn : ‖s‖ ≤ 62 := by
      calc ‖s‖ = ‖(s.re : ℂ) + (s.im : ℂ) * I‖ := by rw [Complex.re_add_im]
        _ ≤ ‖(s.re : ℂ)‖ + ‖(s.im : ℂ) * I‖ := norm_add_le _ _
        _ = |s.re| + |s.im| := by simp
        _ ≤ 62 := by
            have h1 : |s.re| ≤ 2 := by
              rw [abs_le]
              constructor <;> linarith
            linarith
    have hsn1 : ‖s + 1‖ ≤ 63 := by
      calc ‖s + 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_add_le _ _
        _ ≤ 63 := by
            rw [norm_one]
            linarith
    have ht1 : ((58:ℝ)) ^ (-s.re - 2) ≤ (2/5) * (1/58)^2 := by
      have h1 : ((58:ℝ)) ^ (-s.re - 2) ≤ ((58:ℝ)) ^ (-((1:ℝ)/4) - 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h2 : ((58:ℝ)) ^ (-((1:ℝ)/4) - 2)
          = ((58:ℝ)) ^ (-((1:ℝ)/4)) * ((58:ℝ)) ^ (-(2:ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 58)]
        norm_num
      have h3 : ((58:ℝ)) ^ (-(2:ℝ)) = (1/58)^2 := by
        rw [show (-(2:ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        norm_num
      rw [h2, h3] at h1
      have h4 := rpow_58_neg14
      have h7 : ((58:ℝ)) ^ (-((1:ℝ)/4)) * (1/58)^2
          ≤ (2/5) * (1/58)^2 := by linarith [h4]
      linarith [h1, h7]
    have ht2 : ((58:ℝ)) ^ (-s.re - 1) / (s.re + 1)
        ≤ (4/5) * ((2/5) * (1/58)) := by
      have h1 : ((58:ℝ)) ^ (-s.re - 1) ≤ ((58:ℝ)) ^ (-((1:ℝ)/4) - 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h2 : ((58:ℝ)) ^ (-((1:ℝ)/4) - 1)
          = ((58:ℝ)) ^ (-((1:ℝ)/4)) * ((58:ℝ)) ^ (-(1:ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 58)]
        norm_num
      have h3 : ((58:ℝ)) ^ (-(1:ℝ)) = 1/58 := by
        rw [show (-(1:ℝ)) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        norm_num
      have h4 := rpow_58_neg14
      have hnn := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 58) (-s.re - 1)
      have h6 : ((58:ℝ)) ^ (-s.re - 1) / (s.re + 1)
          ≤ (4/5) * ((58:ℝ)) ^ (-s.re - 1) := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < s.re + 1)]
        nlinarith [hnn, hσl]
      rw [h2, h3] at h1
      have h7 : ((58:ℝ)) ^ (-((1:ℝ)/4)) * (1/58) ≤ (2/5) * (1/58) := by
        linarith [h4]
      nlinarith [h6, h1, h7]
    have hprod : (0:ℝ) ≤ ‖s‖ * ‖s + 1‖ * (1/8) := by positivity
    have hsum : ((58:ℝ)) ^ (-s.re - 2)
        + ((58:ℝ)) ^ (-s.re - 1) / (s.re + 1)
        ≤ (2/5) * (1/58)^2 + (4/5) * ((2/5) * (1/58)) := by
      linarith [ht1, ht2]
    have hbig : ‖s‖ * ‖s + 1‖ * (1/8) ≤ 62 * 63 * (1/8) := by
      have h1 := mul_le_mul hsn hsn1 (norm_nonneg _)
        (by norm_num : (0:ℝ) ≤ 62)
      linarith
    calc ‖s‖ * ‖s + 1‖ * (1/8)
        * (((58:ℝ)) ^ (-s.re - 2) + ((58:ℝ)) ^ (-s.re - 1) / (s.re + 1))
        ≤ (62 * 63 * (1/8)) * ((2/5) * (1/58)^2 + (4/5) * ((2/5) * (1/58))) := by
          have hc : (0:ℝ) ≤ ((58:ℝ)) ^ (-s.re - 2)
              + ((58:ℝ)) ^ (-s.re - 1) / (s.re + 1) := by
            have h1 := Real.rpow_nonneg
              (by norm_num : (0:ℝ) ≤ 58) (-s.re - 2)
            have h2 := Real.rpow_nonneg
              (by norm_num : (0:ℝ) ≤ 58) (-s.re - 1)
            have h3 : (0:ℝ) < s.re + 1 := by linarith
            have h4 : (0:ℝ) ≤ ((58:ℝ)) ^ (-s.re - 1) / (s.re + 1) :=
              div_nonneg h2 h3.le
            linarith
          exact mul_le_mul hbig hsum hc (by positivity)
      _ ≤ 3 := by norm_num
  -- assemble
  have hmain : ‖(∑ n ∈ Finset.range 59, (((n : ℝ)) : ℂ) ^ (-s))
      + (((58:ℝ)) : ℂ) ^ (1 - s) / (s - 1)
      - (((58:ℝ)) : ℂ) ^ (-s) / 2‖
      ≤ (1 + (4/3) * 22) + 22/40 + 1/5 := by
    calc ‖(∑ n ∈ Finset.range 59, (((n : ℝ)) : ℂ) ^ (-s))
        + (((58:ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - (((58:ℝ)) : ℂ) ^ (-s) / 2‖
        ≤ ‖(∑ n ∈ Finset.range 59, (((n : ℝ)) : ℂ) ^ (-s))
            + (((58:ℝ)) : ℂ) ^ (1 - s) / (s - 1)‖
          + ‖(((58:ℝ)) : ℂ) ^ (-s) / 2‖ := by
          rw [sub_eq_add_neg]
          refine (norm_add_le _ _).trans ?_
          rw [norm_neg]
      _ ≤ (‖∑ n ∈ Finset.range 59, (((n : ℝ)) : ℂ) ^ (-s)‖
            + ‖(((58:ℝ)) : ℂ) ^ (1 - s) / (s - 1)‖)
          + ‖(((58:ℝ)) : ℂ) ^ (-s) / 2‖ := by
          have := norm_add_le
            (∑ n ∈ Finset.range 59, (((n : ℝ)) : ℂ) ^ (-s))
            ((((58:ℝ)) : ℂ) ^ (1 - s) / (s - 1))
          linarith
      _ ≤ (1 + (4/3) * 22) + 22/40 + 1/5 := by
          linarith [hhead, hpole, hhalf]
  have htri : ‖riemannZeta s‖
      ≤ ‖(∑ n ∈ Finset.range 59, (((n : ℝ)) : ℂ) ^ (-s))
          + (((58:ℝ)) : ℂ) ^ (1 - s) / (s - 1)
          - (((58:ℝ)) : ℂ) ^ (-s) / 2‖
        + ‖riemannZeta s - ((∑ n ∈ Finset.range 59, (((n : ℝ)) : ℂ) ^ (-s))
            + (((58:ℝ)) : ℂ) ^ (1 - s) / (s - 1)
            - (((58:ℝ)) : ℂ) ^ (-s) / 2)‖ := by
    have h := norm_add_le
      ((∑ n ∈ Finset.range 59, (((n : ℝ)) : ℂ) ^ (-s))
        + (((58:ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - (((58:ℝ)) : ℂ) ^ (-s) / 2)
      (riemannZeta s - ((∑ n ∈ Finset.range 59, (((n : ℝ)) : ℂ) ^ (-s))
        + (((58:ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - (((58:ℝ)) : ℂ) ^ (-s) / 2))
    have heq : ((∑ n ∈ Finset.range 59, (((n : ℝ)) : ℂ) ^ (-s))
        + (((58:ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - (((58:ℝ)) : ℂ) ^ (-s) / 2)
        + (riemannZeta s - ((∑ n ∈ Finset.range 59, (((n : ℝ)) : ℂ) ^ (-s))
          + (((58:ℝ)) : ℂ) ^ (1 - s) / (s - 1)
          - (((58:ℝ)) : ℂ) ^ (-s) / 2)) = riemannZeta s := by
      ring
    rw [heq] at h
    exact h
  have hEM' := hEM
  calc ‖riemannZeta s‖
      ≤ ((1 + (4/3) * 22) + 22/40 + 1/5) + 3 := by
        linarith [htri, hmain, hEM', herr]
    _ ≤ 35 := by norm_num

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.rpow_58_34
#print axioms CriticalLinePhasor.DVP.rpow_58_neg14
#print axioms CriticalLinePhasor.DVP.zeta_local_bound
end AxiomAudit
