import RequestProject.DVPSegment435o2Core
import RequestProject.DVPWeights289o2
import RequestProject.DVPWeights63
import RequestProject.DVPWeights74
import RequestProject.DVPWeights81

/-!
# Segment positivity at `t = 435/2`: rung-217.5 (seven σ-intervals)
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

set_option maxRecDepth 8192 in
theorem seg435o2_interval_1 {σ : ℝ} (ha : (1/2:ℝ) ≤ σ) (hb : σ ≤ (3/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((435:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta435o2_lower h1 h2
  have hc2 : ((499639/500000 : ℚ) : ℝ) ≤ cos435o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 2 - ((499659/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((3296387788421/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos435o2c 2 := by
    have hwlo : ((6597539/10000000 : ℚ) : ℝ) ≤ ((2:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_2_6).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((2:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((6597539/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc2).1
      (by push_cast; norm_num)
    calc ((3296387788421/5000000000000 : ℚ) : ℝ)
        = ((6597539/10000000 : ℚ) : ℝ) * ((499639/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((122813/125000 : ℚ) : ℝ) ≤ cos435o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 3 - ((61409/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((317644648517/625000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos435o2c 3 := by
    have hwlo : ((2586409/5000000 : ℚ) : ℝ) ≤ ((3:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_3_6).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((3:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((2586409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc3).1
      (by push_cast; norm_num)
    calc ((317644648517/625000000000 : ℚ) : ℝ)
        = ((2586409/5000000 : ℚ) : ℝ) * ((122813/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((997233/1000000 : ℚ) : ℝ) ≤ cos435o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 4 - ((997273/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((271294245951/625000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos435o2c 4 := by
    have hwlo : ((272047/625000 : ℚ) : ℝ) ≤ ((4:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_4_6).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((4:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((272047/625000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc4).1
      (by push_cast; norm_num)
    calc ((271294245951/625000000000 : ℚ) : ℝ)
        = ((272047/625000 : ℚ) : ℝ) * ((997233/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-46543/200000 : ℚ) : ℝ) ≤ cos435o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 5 - ((-9307/40000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-26018328231/250000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos435o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((559017/1250000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-26018328231/250000000000 : ℚ) : ℝ)
        = ((559017/1250000 : ℚ) : ℝ) * ((-46543/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((494351/500000 : ℚ) : ℝ) ≤ cos435o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 6 - ((494371/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((1687114666237/5000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos435o2c 6 := by
    have hwlo : ((3412787/10000000 : ℚ) : ℝ) ≤ ((6:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_6_6).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((6:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((3412787/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc6).1
      (by push_cast; norm_num)
    calc ((1687114666237/5000000000000 : ℚ) : ℝ)
        = ((3412787/10000000 : ℚ) : ℝ) * ((494351/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-637537/1000000 : ℚ) : ℝ) ≤ cos435o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 7 - ((-637497/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-481932706873/2000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos435o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((755929/2000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-481932706873/2000000000000 : ℚ) : ℝ)
        = ((755929/2000000 : ℚ) : ℝ) * ((-637537/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((993827/1000000 : ℚ) : ℝ) ≤ cos435o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 8 - ((993867/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((570803543623/2000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos435o2c 8 := by
    have hwlo : ((574349/2000000 : ℚ) : ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_8_6).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((8:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((574349/2000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc8).1
      (by push_cast; norm_num)
    calc ((570803543623/2000000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((993827/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((46537/50000 : ℚ) : ℝ) ≤ cos435o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 9 - ((46539/50000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((24904787457/100000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos435o2c 9 := by
    have hwlo : ((535161/2000000 : ℚ) : ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_9_6).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((9:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((535161/2000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc9).1
      (by push_cast; norm_num)
    calc ((24904787457/100000000000 : ℚ) : ℝ)
        = ((535161/2000000 : ℚ) : ℝ) * ((46537/50000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-134243/500000 : ℚ) : ℝ) ≤ cos435o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 10 - ((-134223/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-212256842777/2500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos435o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((1581139/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-212256842777/2500000000000 : ℚ) : ℝ)
        = ((1581139/5000000 : ℚ) : ℝ) * ((-134243/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hanti : ∀ k : ℕ, 11 ≤ k →
      (((k+1:ℕ)) : ℝ) ^ (-σ) ≤ ((k:ℕ) : ℝ) ^ (-σ) := by
    intro k hk
    apply rpow_neg_anti
    · exact_mod_cast (by omega : 1 ≤ k)
    · push_cast
      linarith
    · linarith
  have hnn : ∀ k : ℕ, 11 ≤ k → (0:ℝ) ≤ ((k:ℕ) : ℝ) ^ (-σ) :=
    fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _
  have habel := abel_icc_lower (c := cos435o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum435o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((1507557/5000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_5).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw250lo : ((22757/625000 : ℚ) : ℝ) ≤ ((250:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_250_6).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((65139249931/156250000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum435o2_250
    have hx1 : ((1507557/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((22757/625000 : ℚ) : ℝ)
          * (((2862383/250000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos435o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/435 + 1/2)
      ≤ ((79057/1250000 : ℚ) : ℝ) * (500/435 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_250_5).2
    have hexp : (-((((5:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(1/2) : ℝ) := by
      norm_num
    have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (250 : ℝ) ^ (-σ - 2) ≤ ((11/10000000 : ℚ) : ℝ) := by
    have hbr := (wbr_250_25).2
    have hexp : (-((((25:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(5/2) : ℝ) := by
      norm_num
    have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (250 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((253/1000000 : ℚ) : ℝ) / (3/2) := by
    have hnum : (250 : ℝ) ^ (-σ - 1) ≤ ((253/1000000 : ℚ) : ℝ) := by
      have hbr := (wbr_250_15).2
      have hexp : (-((((15:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(3/2) : ℝ) := by
        norm_num
      have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos435o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos435o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos435o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos435o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos435o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos435o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos435o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos435o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos435o2c 10) := by
    rw [show Finset.Icc (2:ℕ) 10 = {2, 3, 4, 5, 6, 7, 8, 9, 10} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ring
  rw [hsplitsum, hexpand] at hcore
  push_cast at hterm2 hterm3 hterm4 hterm5 hterm6 hterm7 hterm8 hterm9 hterm10 htail hcost1 hrp2 hrp3 hcore ⊢
  linarith [hcore, hterm2, hterm3, hterm4, hterm5, hterm6, hterm7, hterm8,
    hterm9, hterm10, htail, hcost1, hrp2, hrp3]

set_option maxRecDepth 8192 in
theorem seg435o2_interval_2 {σ : ℝ} (ha : (3/5:ℝ) ≤ σ) (hb : σ ≤ (7/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((435:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta435o2_lower h1 h2
  have hc2 : ((499639/500000 : ℚ) : ℝ) ≤ cos435o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 2 - ((499659/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1537819392179/2500000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos435o2c 2 := by
    have hwlo : ((3077861/5000000 : ℚ) : ℝ) ≤ ((2:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_2_7).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((2:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((3077861/5000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc2).1
      (by push_cast; norm_num)
    calc ((1537819392179/2500000000000 : ℚ) : ℝ)
        = ((3077861/5000000 : ℚ) : ℝ) * ((499639/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((122813/125000 : ℚ) : ℝ) ≤ cos435o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 3 - ((61409/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((56919281419/125000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos435o2c 3 := by
    have hwlo : ((463463/1000000 : ℚ) : ℝ) ≤ ((3:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_3_7).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((3:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((463463/1000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc3).1
      (by push_cast; norm_num)
    calc ((56919281419/125000000000 : ℚ) : ℝ)
        = ((463463/1000000 : ℚ) : ℝ) * ((122813/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((997233/1000000 : ℚ) : ℝ) ≤ cos435o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 4 - ((997273/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((3778806031803/10000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos435o2c 4 := by
    have hwlo : ((3789291/10000000 : ℚ) : ℝ) ≤ ((4:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_4_7).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((4:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((3789291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc4).1
      (by push_cast; norm_num)
    calc ((3778806031803/10000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((997233/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-46543/200000 : ℚ) : ℝ) ≤ cos435o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 5 - ((-9307/40000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-44300884061/500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos435o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((951827/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_6).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-44300884061/500000000000 : ℚ) : ℝ)
        = ((951827/2500000 : ℚ) : ℝ) * ((-46543/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((494351/500000 : ℚ) : ℝ) ≤ cos435o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 6 - ((494371/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((1410358191099/5000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos435o2c 6 := by
    have hwlo : ((2852949/10000000 : ℚ) : ℝ) ≤ ((6:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_6_7).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((6:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((2852949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc6).1
      (by push_cast; norm_num)
    calc ((1410358191099/5000000000000 : ℚ) : ℝ)
        = ((2852949/10000000 : ℚ) : ℝ) * ((494351/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-637537/1000000 : ℚ) : ℝ) ≤ cos435o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 7 - ((-637497/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-396713136083/2000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos435o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((622259/2000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_6).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-396713136083/2000000000000 : ℚ) : ℝ)
        = ((622259/2000000 : ℚ) : ℝ) * ((-637537/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((993827/1000000 : ℚ) : ℝ) ≤ cos435o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 8 - ((993867/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((1159091485657/5000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos435o2c 8 := by
    have hwlo : ((1166291/5000000 : ℚ) : ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_8_7).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((8:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((1166291/5000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc8).1
      (by push_cast; norm_num)
    calc ((1159091485657/5000000000000 : ℚ) : ℝ)
        = ((1166291/5000000 : ℚ) : ℝ) * ((993827/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((46537/50000 : ℚ) : ℝ) ≤ cos435o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 9 - ((46539/50000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((4998027263/25000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos435o2c 9 := by
    have hwlo : ((107399/500000 : ℚ) : ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_9_7).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((9:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((107399/500000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc9).1
      (by push_cast; norm_num)
    calc ((4998027263/25000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((46537/50000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-134243/500000 : ℚ) : ℝ) ≤ cos435o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 10 - ((-134223/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-337203246541/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos435o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((2511887/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_6).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-337203246541/5000000000000 : ℚ) : ℝ)
        = ((2511887/10000000 : ℚ) : ℝ) * ((-134243/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hanti : ∀ k : ℕ, 11 ≤ k →
      (((k+1:ℕ)) : ℝ) ^ (-σ) ≤ ((k:ℕ) : ℝ) ^ (-σ) := by
    intro k hk
    apply rpow_neg_anti
    · exact_mod_cast (by omega : 1 ≤ k)
    · push_cast
      linarith
    · linarith
  have hnn : ∀ k : ℕ, 11 ≤ k → (0:ℝ) ≤ ((k:ℕ) : ℝ) ^ (-σ) :=
    fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _
  have habel := abel_icc_lower (c := cos435o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum435o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((148267/625000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_6).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw250lo : ((26203/1250000 : ℚ) : ℝ) ≤ ((250:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_250_7).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((75003021749/312500000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum435o2_250
    have hx1 : ((148267/625000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((26203/1250000 : ℚ) : ℝ)
          * (((2862383/250000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos435o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/435 + 1/2)
      ≤ ((364113/10000000 : ℚ) : ℝ) * (500/435 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_250_6).2
    have hexp : (-((((6:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(3/5) : ℝ) := by
      norm_num
    have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (250 : ℝ) ^ (-σ - 2) ≤ ((3/5000000 : ℚ) : ℝ) := by
    have hbr := (wbr_250_26).2
    have hexp : (-((((26:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(13/5) : ℝ) := by
      norm_num
    have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (250 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((1457/10000000 : ℚ) : ℝ) / (3/2) := by
    have hnum : (250 : ℝ) ^ (-σ - 1) ≤ ((1457/10000000 : ℚ) : ℝ) := by
      have hbr := (wbr_250_16).2
      have hexp : (-((((16:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(8/5) : ℝ) := by
        norm_num
      have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos435o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos435o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos435o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos435o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos435o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos435o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos435o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos435o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos435o2c 10) := by
    rw [show Finset.Icc (2:ℕ) 10 = {2, 3, 4, 5, 6, 7, 8, 9, 10} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ring
  rw [hsplitsum, hexpand] at hcore
  push_cast at hterm2 hterm3 hterm4 hterm5 hterm6 hterm7 hterm8 hterm9 hterm10 htail hcost1 hrp2 hrp3 hcore ⊢
  linarith [hcore, hterm2, hterm3, hterm4, hterm5, hterm6, hterm7, hterm8,
    hterm9, hterm10, htail, hcost1, hrp2, hrp3]

set_option maxRecDepth 8192 in
theorem seg435o2_interval_3 {σ : ℝ} (ha : (7/10:ℝ) ≤ σ) (hb : σ ≤ (9/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((435:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta435o2_lower h1 h2
  have hc2 : ((499639/500000 : ℚ) : ℝ) ≤ cos435o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 2 - ((499659/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((2677498949013/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos435o2c 2 := by
    have hwlo : ((5358867/10000000 : ℚ) : ℝ) ≤ ((2:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_2_9).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((2:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((5358867/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc2).1
      (by push_cast; norm_num)
    calc ((2677498949013/5000000000000 : ℚ) : ℝ)
        = ((5358867/10000000 : ℚ) : ℝ) * ((499639/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((122813/125000 : ℚ) : ℝ) ≤ cos435o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 3 - ((61409/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((45691471333/125000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos435o2c 3 := by
    have hwlo : ((372041/1000000 : ℚ) : ℝ) ≤ ((3:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_3_9).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((3:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((372041/1000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc3).1
      (by push_cast; norm_num)
    calc ((45691471333/125000000000 : ℚ) : ℝ)
        = ((372041/1000000 : ℚ) : ℝ) * ((122813/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((997233/1000000 : ℚ) : ℝ) ≤ cos435o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 4 - ((997273/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((572759776317/2000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos435o2c 4 := by
    have hwlo : ((574349/2000000 : ℚ) : ℝ) ≤ ((4:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_4_9).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((4:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((574349/2000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc4).1
      (by push_cast; norm_num)
    calc ((572759776317/2000000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((997233/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-46543/200000 : ℚ) : ℝ) ≤ cos435o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 5 - ((-9307/40000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-75430238751/1000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos435o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((1620657/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-75430238751/1000000000000 : ℚ) : ℝ)
        = ((1620657/5000000 : ℚ) : ℝ) * ((-46543/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((494351/500000 : ℚ) : ℝ) ≤ cos435o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 6 - ((494371/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((492798243509/2500000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos435o2c 6 := by
    have hwlo : ((996859/5000000 : ℚ) : ℝ) ≤ ((6:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_6_9).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((6:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((996859/5000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc6).1
      (by push_cast; norm_num)
    calc ((492798243509/2500000000000 : ℚ) : ℝ)
        = ((996859/5000000 : ℚ) : ℝ) * ((494351/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-637537/1000000 : ℚ) : ℝ) ≤ cos435o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 7 - ((-637497/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-1632814499273/10000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos435o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((2561129/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-1632814499273/10000000000000 : ℚ) : ℝ)
        = ((2561129/10000000 : ℚ) : ℝ) * ((-637537/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((993827/1000000 : ℚ) : ℝ) ≤ cos435o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 8 - ((993867/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((152943018511/1000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos435o2c 8 := by
    have hwlo : ((153893/1000000 : ℚ) : ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_8_9).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((8:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((153893/1000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc8).1
      (by push_cast; norm_num)
    calc ((152943018511/1000000000000 : ℚ) : ℝ)
        = ((153893/1000000 : ℚ) : ℝ) * ((993827/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((46537/50000 : ℚ) : ℝ) ≤ cos435o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 9 - ((46539/50000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((12882791173/100000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos435o2c 9 := by
    have hwlo : ((276829/2000000 : ℚ) : ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_9_9).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((9:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((276829/2000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc9).1
      (by push_cast; norm_num)
    calc ((12882791173/100000000000 : ℚ) : ℝ)
        = ((276829/2000000 : ℚ) : ℝ) * ((46537/50000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-134243/500000 : ℚ) : ℝ) ≤ cos435o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 10 - ((-134223/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-267850090909/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos435o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((1995263/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-267850090909/5000000000000 : ℚ) : ℝ)
        = ((1995263/10000000 : ℚ) : ℝ) * ((-134243/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hanti : ∀ k : ℕ, 11 ≤ k →
      (((k+1:ℕ)) : ℝ) ^ (-σ) ≤ ((k:ℕ) : ℝ) ^ (-σ) := by
    intro k hk
    apply rpow_neg_anti
    · exact_mod_cast (by omega : 1 ≤ k)
    · push_cast
      linarith
    · linarith
  have hnn : ∀ k : ℕ, 11 ≤ k → (0:ℝ) ≤ ((k:ℕ) : ℝ) ^ (-σ) :=
    fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _
  have habel := abel_icc_lower (c := cos435o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum435o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((233311/1250000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_7).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw250lo : ((69479/10000000 : ℚ) : ℝ) ≤ ((250:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_250_9).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((198875508457/2500000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum435o2_250
    have hx1 : ((233311/1250000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((69479/10000000 : ℚ) : ℝ)
          * (((2862383/250000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos435o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/435 + 1/2)
      ≤ ((1677/80000 : ℚ) : ℝ) * (500/435 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_250_7).2
    have hexp : (-((((7:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(7/10) : ℝ) := by
      norm_num
    have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (250 : ℝ) ^ (-σ - 2) ≤ ((1/2500000 : ℚ) : ℝ) := by
    have hbr := (wbr_250_27).2
    have hexp : (-((((27:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(27/10) : ℝ) := by
      norm_num
    have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (250 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((839/10000000 : ℚ) : ℝ) / (3/2) := by
    have hnum : (250 : ℝ) ^ (-σ - 1) ≤ ((839/10000000 : ℚ) : ℝ) := by
      have hbr := (wbr_250_17).2
      have hexp : (-((((17:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(17/10) : ℝ) := by
        norm_num
      have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos435o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos435o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos435o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos435o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos435o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos435o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos435o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos435o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos435o2c 10) := by
    rw [show Finset.Icc (2:ℕ) 10 = {2, 3, 4, 5, 6, 7, 8, 9, 10} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ring
  rw [hsplitsum, hexpand] at hcore
  push_cast at hterm2 hterm3 hterm4 hterm5 hterm6 hterm7 hterm8 hterm9 hterm10 htail hcost1 hrp2 hrp3 hcore ⊢
  linarith [hcore, hterm2, hterm3, hterm4, hterm5, hterm6, hterm7, hterm8,
    hterm9, hterm10, htail, hcost1, hrp2, hrp3]

set_option maxRecDepth 8192 in
theorem seg435o2_interval_4 {σ : ℝ} (ha : (9/10:ℝ) ≤ σ) (hb : σ ≤ (11/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((435:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta435o2_lower h1 h2
  have hc2 : ((499639/500000 : ℚ) : ℝ) ≤ cos435o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 2 - ((499659/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((582724468949/1250000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos435o2c 2 := by
    have hwlo : ((1166291/2500000 : ℚ) : ℝ) ≤ ((2:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_2_11).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((2:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((1166291/2500000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc2).1
      (by push_cast; norm_num)
    calc ((582724468949/1250000000000 : ℚ) : ℝ)
        = ((1166291/2500000 : ℚ) : ℝ) * ((499639/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((122813/125000 : ℚ) : ℝ) ≤ cos435o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 3 - ((61409/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((11462014477/39062500000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos435o2c 3 := by
    have hwlo : ((93329/312500 : ℚ) : ℝ) ≤ ((3:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_3_11).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((3:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((93329/312500 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc3).1
      (by push_cast; norm_num)
    calc ((11462014477/39062500000 : ℚ) : ℝ)
        = ((93329/312500 : ℚ) : ℝ) * ((122813/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((997233/1000000 : ℚ) : ℝ) ≤ cos435o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 4 - ((997273/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((271294245951/1250000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos435o2c 4 := by
    have hwlo : ((272047/1250000 : ℚ) : ℝ) ≤ ((4:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_4_11).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((4:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((272047/1250000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc4).1
      (by push_cast; norm_num)
    calc ((271294245951/1250000000000 : ℚ) : ℝ)
        = ((272047/1250000 : ℚ) : ℝ) * ((997233/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-46543/200000 : ℚ) : ℝ) ≤ cos435o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 5 - ((-9307/40000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-54670292117/1000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos435o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((1174619/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-54670292117/1000000000000 : ℚ) : ℝ)
        = ((1174619/5000000 : ℚ) : ℝ) * ((-46543/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((494351/500000 : ℚ) : ℝ) ≤ cos435o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 6 - ((494371/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((43047590729/312500000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos435o2c 6 := by
    have hwlo : ((87079/625000 : ℚ) : ℝ) ≤ ((6:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_6_11).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((6:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((87079/625000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc6).1
      (by push_cast; norm_num)
    calc ((43047590729/312500000000 : ℚ) : ℝ)
        = ((87079/625000 : ℚ) : ℝ) * ((494351/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-637537/1000000 : ℚ) : ℝ) ≤ cos435o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 7 - ((-637497/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-1106412949113/10000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos435o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((1735449/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-1106412949113/10000000000000 : ℚ) : ℝ)
        = ((1735449/10000000 : ℚ) : ℝ) * ((-637537/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((993827/1000000 : ℚ) : ℝ) ≤ cos435o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 8 - ((993867/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((201809492101/2000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos435o2c 8 := by
    have hwlo : ((203063/2000000 : ℚ) : ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_8_11).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((8:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((203063/2000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc8).1
      (by push_cast; norm_num)
    calc ((201809492101/2000000000000 : ℚ) : ℝ)
        = ((203063/2000000 : ℚ) : ℝ) * ((993827/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((46537/50000 : ℚ) : ℝ) ≤ cos435o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 9 - ((46539/50000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((8301595819/100000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos435o2c 9 := by
    have hwlo : ((178387/2000000 : ℚ) : ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_9_11).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((9:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((178387/2000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc9).1
      (by push_cast; norm_num)
    calc ((8301595819/100000000000 : ℚ) : ℝ)
        = ((178387/2000000 : ℚ) : ℝ) * ((46537/50000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-134243/500000 : ℚ) : ℝ) ≤ cos435o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 10 - ((-134223/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-84501001509/2500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos435o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((629463/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-84501001509/2500000000000 : ℚ) : ℝ)
        = ((629463/5000000 : ℚ) : ℝ) * ((-134243/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hanti : ∀ k : ℕ, 11 ≤ k →
      (((k+1:ℕ)) : ℝ) ^ (-σ) ≤ ((k:ℕ) : ℝ) ^ (-σ) := by
    intro k hk
    apply rpow_neg_anti
    · exact_mod_cast (by omega : 1 ≤ k)
    · push_cast
      linarith
    · linarith
  have hnn : ∀ k : ℕ, 11 ≤ k → (0:ℝ) ≤ ((k:ℕ) : ℝ) ^ (-σ) :=
    fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _
  have habel := abel_icc_lower (c := cos435o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum435o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((577719/5000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_9).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw250lo : ((5757/2500000 : ℚ) : ℝ) ≤ ((250:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_250_11).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((16478738931/625000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum435o2_250
    have hx1 : ((577719/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((5757/2500000 : ℚ) : ℝ)
          * (((2862383/250000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos435o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/435 + 1/2)
      ≤ ((1737/250000 : ℚ) : ℝ) * (500/435 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_250_9).2
    have hexp : (-((((9:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(9/10) : ℝ) := by
      norm_num
    have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (250 : ℝ) ^ (-σ - 2) ≤ ((1/5000000 : ℚ) : ℝ) := by
    have hbr := (wbr_250_29).2
    have hexp : (-((((29:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(29/10) : ℝ) := by
      norm_num
    have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (250 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((139/5000000 : ℚ) : ℝ) / (3/2) := by
    have hnum : (250 : ℝ) ^ (-σ - 1) ≤ ((139/5000000 : ℚ) : ℝ) := by
      have hbr := (wbr_250_19).2
      have hexp : (-((((19:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(19/10) : ℝ) := by
        norm_num
      have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos435o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos435o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos435o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos435o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos435o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos435o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos435o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos435o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos435o2c 10) := by
    rw [show Finset.Icc (2:ℕ) 10 = {2, 3, 4, 5, 6, 7, 8, 9, 10} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ring
  rw [hsplitsum, hexpand] at hcore
  push_cast at hterm2 hterm3 hterm4 hterm5 hterm6 hterm7 hterm8 hterm9 hterm10 htail hcost1 hrp2 hrp3 hcore ⊢
  linarith [hcore, hterm2, hterm3, hterm4, hterm5, hterm6, hterm7, hterm8,
    hterm9, hterm10, htail, hcost1, hrp2, hrp3]

set_option maxRecDepth 8192 in
theorem seg435o2_interval_5 {σ : ℝ} (ha : (11/10:ℝ) ≤ σ) (hb : σ ≤ (7/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((435:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta435o2_lower h1 h2
  have hc2 : ((499639/500000 : ℚ) : ℝ) ≤ cos435o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 2 - ((499659/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1893277565949/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos435o2c 2 := by
    have hwlo : ((3789291/10000000 : ℚ) : ℝ) ≤ ((2:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_2_14).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((2:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((3789291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc2).1
      (by push_cast; norm_num)
    calc ((1893277565949/5000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((499639/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((122813/125000 : ℚ) : ℝ) ≤ cos435o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 3 - ((61409/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((13189993387/62500000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos435o2c 3 := by
    have hwlo : ((107399/500000 : ℚ) : ℝ) ≤ ((3:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_3_14).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((3:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((107399/500000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc3).1
      (by push_cast; norm_num)
    calc ((13189993387/62500000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((122813/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((997233/1000000 : ℚ) : ℝ) ≤ cos435o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 4 - ((997273/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((44746841943/312500000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos435o2c 4 := by
    have hwlo : ((44871/312500 : ℚ) : ℝ) ≤ ((4:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_4_14).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((4:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((44871/312500 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc4).1
      (by push_cast; norm_num)
    calc ((44746841943/312500000000 : ℚ) : ℝ)
        = ((44871/312500 : ℚ) : ℝ) * ((997233/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-46543/200000 : ℚ) : ℝ) ≤ cos435o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 5 - ((-9307/40000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-1981195881/50000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos435o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((42567/250000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-1981195881/50000000000 : ℚ) : ℝ)
        = ((42567/250000 : ℚ) : ℝ) * ((-46543/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((494351/500000 : ℚ) : ℝ) ≤ cos435o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 6 - ((494371/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((100592024533/1250000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos435o2c 6 := by
    have hwlo : ((203483/2500000 : ℚ) : ℝ) ≤ ((6:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_6_14).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((6:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((203483/2500000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc6).1
      (by push_cast; norm_num)
    calc ((100592024533/1250000000000 : ℚ) : ℝ)
        = ((203483/2500000 : ℚ) : ℝ) * ((494351/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-637537/1000000 : ℚ) : ℝ) ≤ cos435o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 7 - ((-637497/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-749717372983/10000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos435o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((1175959/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-749717372983/10000000000000 : ℚ) : ℝ)
        = ((1175959/10000000 : ℚ) : ℝ) * ((-637537/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((993827/1000000 : ℚ) : ℝ) ≤ cos435o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 8 - ((993867/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((270367653869/5000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos435o2c 8 := by
    have hwlo : ((272047/5000000 : ℚ) : ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_8_14).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((8:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((272047/5000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc8).1
      (by push_cast; norm_num)
    calc ((270367653869/5000000000000 : ℚ) : ℝ)
        = ((272047/5000000 : ℚ) : ℝ) * ((993827/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((46537/50000 : ℚ) : ℝ) ≤ cos435o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 9 - ((46539/50000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((21471287597/500000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos435o2c 9 := by
    have hwlo : ((461381/10000000 : ℚ) : ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_9_14).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((9:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((461381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc9).1
      (by push_cast; norm_num)
    calc ((21471287597/500000000000 : ℚ) : ℝ)
        = ((461381/10000000 : ℚ) : ℝ) * ((46537/50000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-134243/500000 : ℚ) : ℝ) ≤ cos435o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 10 - ((-134223/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-106633107947/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos435o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((794329/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-106633107947/5000000000000 : ℚ) : ℝ)
        = ((794329/10000000 : ℚ) : ℝ) * ((-134243/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hanti : ∀ k : ℕ, 11 ≤ k →
      (((k+1:ℕ)) : ℝ) ^ (-σ) ≤ ((k:ℕ) : ℝ) ^ (-σ) := by
    intro k hk
    apply rpow_neg_anti
    · exact_mod_cast (by omega : 1 ≤ k)
    · push_cast
      linarith
    · linarith
  have hnn : ∀ k : ℕ, 11 ≤ k → (0:ℝ) ≤ ((k:ℕ) : ℝ) ^ (-σ) :=
    fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _
  have habel := abel_icc_lower (c := cos435o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum435o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((715267/10000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_11).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw250lo : ((2197/5000000 : ℚ) : ℝ) ≤ ((250:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_250_14).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((6288655451/1250000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum435o2_250
    have hx1 : ((715267/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((2197/5000000 : ℚ) : ℝ)
          * (((2862383/250000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos435o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/435 + 1/2)
      ≤ ((23029/10000000 : ℚ) : ℝ) * (500/435 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_250_11).2
    have hexp : (-((((11:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(11/10) : ℝ) := by
      norm_num
    have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (250 : ℝ) ^ (-σ - 2) ≤ ((1/10000000 : ℚ) : ℝ) := by
    have hbr := (wbr_250_31).2
    have hexp : (-((((31:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(31/10) : ℝ) := by
      norm_num
    have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (250 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((93/10000000 : ℚ) : ℝ) / (3/2) := by
    have hnum : (250 : ℝ) ^ (-σ - 1) ≤ ((93/10000000 : ℚ) : ℝ) := by
      have hbr := (wbr_250_21).2
      have hexp : (-((((21:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(21/10) : ℝ) := by
        norm_num
      have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos435o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos435o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos435o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos435o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos435o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos435o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos435o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos435o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos435o2c 10) := by
    rw [show Finset.Icc (2:ℕ) 10 = {2, 3, 4, 5, 6, 7, 8, 9, 10} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ring
  rw [hsplitsum, hexpand] at hcore
  push_cast at hterm2 hterm3 hterm4 hterm5 hterm6 hterm7 hterm8 hterm9 hterm10 htail hcost1 hrp2 hrp3 hcore ⊢
  linarith [hcore, hterm2, hterm3, hterm4, hterm5, hterm6, hterm7, hterm8,
    hterm9, hterm10, htail, hcost1, hrp2, hrp3]

set_option maxRecDepth 8192 in
theorem seg435o2_interval_6 {σ : ℝ} (ha : (7/5:ℝ) ≤ σ) (hb : σ ≤ (17/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((435:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta435o2_lower h1 h2
  have hc2 : ((499639/500000 : ℚ) : ℝ) ≤ cos435o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 2 - ((499659/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1537819392179/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos435o2c 2 := by
    have hwlo : ((3077861/10000000 : ℚ) : ℝ) ≤ ((2:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_2_17).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((2:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((3077861/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc2).1
      (by push_cast; norm_num)
    calc ((1537819392179/5000000000000 : ℚ) : ℝ)
        = ((3077861/10000000 : ℚ) : ℝ) * ((499639/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((122813/125000 : ℚ) : ℝ) ≤ cos435o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 3 - ((61409/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((47432714047/312500000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos435o2c 3 := by
    have hwlo : ((386219/2500000 : ℚ) : ℝ) ≤ ((3:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_3_17).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((3:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((386219/2500000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc3).1
      (by push_cast; norm_num)
    calc ((47432714047/312500000000 : ℚ) : ℝ)
        = ((386219/2500000 : ℚ) : ℝ) * ((122813/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((997233/1000000 : ℚ) : ℝ) ≤ cos435o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 4 - ((997273/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((472350380013/5000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos435o2c 4 := by
    have hwlo : ((473661/5000000 : ℚ) : ℝ) ≤ ((4:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_4_17).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((4:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((473661/5000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc4).1
      (by push_cast; norm_num)
    calc ((472350380013/5000000000000 : ℚ) : ℝ)
        = ((473661/5000000 : ℚ) : ℝ) * ((997233/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-46543/200000 : ℚ) : ℝ) ≤ cos435o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 5 - ((-9307/40000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-12224658579/500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos435o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((262653/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-12224658579/500000000000 : ℚ) : ℝ)
        = ((262653/2500000 : ℚ) : ℝ) * ((-46543/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((494351/500000 : ℚ) : ℝ) ≤ cos435o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 6 - ((494371/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((235059451341/5000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos435o2c 6 := by
    have hwlo : ((475491/10000000 : ℚ) : ℝ) ≤ ((6:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_6_17).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((6:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((475491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc6).1
      (by push_cast; norm_num)
    calc ((235059451341/5000000000000 : ℚ) : ℝ)
        = ((475491/10000000 : ℚ) : ℝ) * ((494351/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-637537/1000000 : ℚ) : ℝ) ≤ cos435o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 7 - ((-637497/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-209092372353/5000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos435o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((327969/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-209092372353/5000000000000 : ℚ) : ℝ)
        = ((327969/5000000 : ℚ) : ℝ) * ((-637537/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((993827/1000000 : ℚ) : ℝ) ≤ cos435o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 8 - ((993867/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((72443031511/2500000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos435o2c 8 := by
    have hwlo : ((72893/2500000 : ℚ) : ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_8_17).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((8:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((72893/2500000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc8).1
      (by push_cast; norm_num)
    calc ((72443031511/2500000000000 : ℚ) : ℝ)
        = ((72893/2500000 : ℚ) : ℝ) * ((993827/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((46537/50000 : ℚ) : ℝ) ≤ cos435o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 9 - ((46539/50000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((1388338321/62500000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos435o2c 9 := by
    have hwlo : ((29833/1250000 : ℚ) : ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_9_17).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((9:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((29833/1250000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc9).1
      (by push_cast; norm_num)
    calc ((1388338321/62500000000 : ℚ) : ℝ)
        = ((29833/1250000 : ℚ) : ℝ) * ((46537/50000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-134243/500000 : ℚ) : ℝ) ≤ cos435o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 10 - ((-134223/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-13360803061/1250000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos435o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((99527/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-13360803061/1250000000000 : ℚ) : ℝ)
        = ((99527/2500000 : ℚ) : ℝ) * ((-134243/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hanti : ∀ k : ℕ, 11 ≤ k →
      (((k+1:ℕ)) : ℝ) ^ (-σ) ≤ ((k:ℕ) : ℝ) ^ (-σ) := by
    intro k hk
    apply rpow_neg_anti
    · exact_mod_cast (by omega : 1 ≤ k)
    · push_cast
      linarith
    · linarith
  have hnn : ∀ k : ℕ, 11 ≤ k → (0:ℝ) ≤ ((k:ℕ) : ℝ) ^ (-σ) :=
    fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _
  have habel := abel_icc_lower (c := cos435o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum435o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((174189/5000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_14).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw250lo : ((419/5000000 : ℚ) : ℝ) ≤ ((250:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_250_17).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((1199338477/1250000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum435o2_250
    have hx1 : ((174189/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((419/5000000 : ℚ) : ℝ)
          * (((2862383/250000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos435o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/435 + 1/2)
      ≤ ((879/2000000 : ℚ) : ℝ) * (500/435 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_250_14).2
    have hexp : (-((((14:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(7/5) : ℝ) := by
      norm_num
    have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (250 : ℝ) ^ (-σ - 2) ≤ ((1/10000000 : ℚ) : ℝ) := by
    have hbr := (wbr_250_34).2
    have hexp : (-((((34:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(17/5) : ℝ) := by
      norm_num
    have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (250 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((9/5000000 : ℚ) : ℝ) / (3/2) := by
    have hnum : (250 : ℝ) ^ (-σ - 1) ≤ ((9/5000000 : ℚ) : ℝ) := by
      have hbr := (wbr_250_24).2
      have hexp : (-((((24:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(12/5) : ℝ) := by
        norm_num
      have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos435o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos435o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos435o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos435o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos435o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos435o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos435o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos435o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos435o2c 10) := by
    rw [show Finset.Icc (2:ℕ) 10 = {2, 3, 4, 5, 6, 7, 8, 9, 10} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ring
  rw [hsplitsum, hexpand] at hcore
  push_cast at hterm2 hterm3 hterm4 hterm5 hterm6 hterm7 hterm8 hterm9 hterm10 htail hcost1 hrp2 hrp3 hcore ⊢
  linarith [hcore, hterm2, hterm3, hterm4, hterm5, hterm6, hterm7, hterm8,
    hterm9, hterm10, htail, hcost1, hrp2, hrp3]

set_option maxRecDepth 8192 in
theorem seg435o2_interval_7 {σ : ℝ} (ha : (17/10:ℝ) ≤ σ) (hb : σ ≤ (2:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((435:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta435o2_lower h1 h2
  have hc2 : ((499639/500000 : ℚ) : ℝ) ≤ cos435o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 2 - ((499659/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((499639/2000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos435o2c 2 := by
    have hwlo : ((1/4 : ℚ) : ℝ) ≤ ((2:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_2_20).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((2:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc2).1
      (by push_cast; norm_num)
    calc ((499639/2000000 : ℚ) : ℝ)
        = ((1/4 : ℚ) : ℝ) * ((499639/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((122813/125000 : ℚ) : ℝ) ≤ cos435o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 3 - ((61409/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((136458875243/1250000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos435o2c 3 := by
    have hwlo : ((1111111/10000000 : ℚ) : ℝ) ≤ ((3:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_3_20).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((3:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc3).1
      (by push_cast; norm_num)
    calc ((136458875243/1250000000000 : ℚ) : ℝ)
        = ((1111111/10000000 : ℚ) : ℝ) * ((122813/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((997233/1000000 : ℚ) : ℝ) ≤ cos435o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 4 - ((997273/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((997233/16000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos435o2c 4 := by
    have hwlo : ((1/16 : ℚ) : ℝ) ≤ ((4:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_4_20).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((4:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc4).1
      (by push_cast; norm_num)
    calc ((997233/16000000 : ℚ) : ℝ)
        = ((1/16 : ℚ) : ℝ) * ((997233/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-46543/200000 : ℚ) : ℝ) ≤ cos435o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 5 - ((-9307/40000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-30172104809/2000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos435o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((648263/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-30172104809/2000000000000 : ℚ) : ℝ)
        = ((648263/10000000 : ℚ) : ℝ) * ((-46543/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((494351/500000 : ℚ) : ℝ) ≤ cos435o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 6 - ((494371/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((137319337727/5000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos435o2c 6 := by
    have hwlo : ((277777/10000000 : ℚ) : ℝ) ≤ ((6:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_6_20).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((6:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((277777/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc6).1
      (by push_cast; norm_num)
    calc ((137319337727/5000000000000 : ℚ) : ℝ)
        = ((277777/10000000 : ℚ) : ℝ) * ((494351/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-637537/1000000 : ℚ) : ℝ) ≤ cos435o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 7 - ((-637497/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-58314871853/2500000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos435o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((91469/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-58314871853/2500000000000 : ℚ) : ℝ)
        = ((91469/2500000 : ℚ) : ℝ) * ((-637537/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((993827/1000000 : ℚ) : ℝ) ≤ cos435o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 8 - ((993867/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((993827/64000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos435o2c 8 := by
    have hwlo : ((1/64 : ℚ) : ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_8_20).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((8:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((1/64 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc8).1
      (by push_cast; norm_num)
    calc ((993827/64000000 : ℚ) : ℝ)
        = ((1/64 : ℚ) : ℝ) * ((993827/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((46537/50000 : ℚ) : ℝ) ≤ cos435o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 9 - ((46539/50000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((89769873/7812500000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos435o2c 9 := by
    have hwlo : ((1929/156250 : ℚ) : ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_9_20).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((9:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((1929/156250 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc9).1
      (by push_cast; norm_num)
    calc ((89769873/7812500000 : ℚ) : ℝ)
        = ((1929/156250 : ℚ) : ℝ) * ((46537/50000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-134243/500000 : ℚ) : ℝ) ≤ cos435o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos435o2c 10 - ((-134223/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos435o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-26785103061/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos435o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((199527/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-26785103061/5000000000000 : ℚ) : ℝ)
        = ((199527/10000000 : ℚ) : ℝ) * ((-134243/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hanti : ∀ k : ℕ, 11 ≤ k →
      (((k+1:ℕ)) : ℝ) ^ (-σ) ≤ ((k:ℕ) : ℝ) ^ (-σ) := by
    intro k hk
    apply rpow_neg_anti
    · exact_mod_cast (by omega : 1 ≤ k)
    · push_cast
      linarith
    · linarith
  have hnn : ∀ k : ℕ, 11 ≤ k → (0:ℝ) ≤ ((k:ℕ) : ℝ) ^ (-σ) :=
    fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _
  have habel := abel_icc_lower (c := cos435o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum435o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((169681/10000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_17).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw250lo : ((1/62500 : ℚ) : ℝ) ≤ ((250:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_250_20).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((2862383/15625000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum435o2_250
    have hx1 : ((169681/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((1/62500 : ℚ) : ℝ)
          * (((2862383/250000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos435o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/435 + 1/2)
      ≤ ((839/10000000 : ℚ) : ℝ) * (500/435 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_250_17).2
    have hexp : (-((((17:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(17/10) : ℝ) := by
      norm_num
    have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (250 : ℝ) ^ (-σ - 2) ≤ ((1/10000000 : ℚ) : ℝ) := by
    have hbr := (wbr_250_37).2
    have hexp : (-((((37:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(37/10) : ℝ) := by
      norm_num
    have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (250 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((1/2500000 : ℚ) : ℝ) / (3/2) := by
    have hnum : (250 : ℝ) ^ (-σ - 1) ≤ ((1/2500000 : ℚ) : ℝ) := by
      have hbr := (wbr_250_27).2
      have hexp : (-((((27:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(27/10) : ℝ) := by
        norm_num
      have hbase : (((250:ℕ)) : ℝ) = (250 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos435o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos435o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos435o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos435o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos435o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos435o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos435o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos435o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos435o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos435o2c 10) := by
    rw [show Finset.Icc (2:ℕ) 10 = {2, 3, 4, 5, 6, 7, 8, 9, 10} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ring
  rw [hsplitsum, hexpand] at hcore
  push_cast at hterm2 hterm3 hterm4 hterm5 hterm6 hterm7 hterm8 hterm9 hterm10 htail hcost1 hrp2 hrp3 hcore ⊢
  linarith [hcore, hterm2, hterm3, hterm4, hterm5, hterm6, hterm7, hterm8,
    hterm9, hterm10, htail, hcost1, hrp2, hrp3]

set_option maxRecDepth 8192 in
/-- **Segment positivity at the half-integer anchor 435/2.** -/
theorem segment435o2_re_pos {σ : ℝ} (h1 : (1/2:ℝ) ≤ σ) (h2 : σ ≤ 2) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((435:ℕ)):ℝ)/2) * Complex.I)).re := by
  rcases le_total σ (3/5 : ℝ) with hc | hc
  · exact seg435o2_interval_1 h1 hc
  rcases le_total σ (7/10 : ℝ) with hc2 | hc2
  · exact seg435o2_interval_2 hc hc2
  rcases le_total σ (9/10 : ℝ) with hc3 | hc3
  · exact seg435o2_interval_3 hc2 hc3
  rcases le_total σ (11/10 : ℝ) with hc4 | hc4
  · exact seg435o2_interval_4 hc3 hc4
  rcases le_total σ (7/5 : ℝ) with hc5 | hc5
  · exact seg435o2_interval_5 hc4 hc5
  rcases le_total σ (17/10 : ℝ) with hc6 | hc6
  · exact seg435o2_interval_6 hc5 hc6
  exact seg435o2_interval_7 hc6 h2

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.segment435o2_re_pos
end AxiomAudit
