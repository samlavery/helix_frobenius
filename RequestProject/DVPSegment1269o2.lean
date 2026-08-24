import RequestProject.DVPSegment1269o2Core
import RequestProject.DVPWeights289o2
import RequestProject.DVPWeights581o2
import RequestProject.DVPWeights1000col
import RequestProject.DVPWeights63
import RequestProject.DVPWeights74
import RequestProject.DVPWeights81

/-!
# Segment positivity at `t = 1269/2`: rung-634.5 (seven σ-intervals, N = 1000)
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3200000 in
theorem seg1269o2_interval_1 {σ : ℝ} (ha : (1/2:ℝ) ≤ σ) (hb : σ ≤ (3/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((1269:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta1269o2_lower h1 h2
  have hc2 : ((9996773/10000000 : ℚ) : ℝ) ≤ cos1269o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 2 - ((9997773/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((65954099741647/100000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos1269o2c 2 := by
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
    calc ((65954099741647/100000000000000 : ℚ) : ℝ)
        = ((6597539/10000000 : ℚ) : ℝ) * ((9996773/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((9343459/10000000 : ℚ) : ℝ) ≤ cos1269o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 3 - ((9344459/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((24166006448731/50000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos1269o2c 3 := by
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
    calc ((24166006448731/50000000000000 : ℚ) : ℝ)
        = ((2586409/5000000 : ℚ) : ℝ) * ((9343459/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((4995053/5000000 : ℚ) : ℝ) ≤ cos1269o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 4 - ((4995553/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((1358889183491/3125000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos1269o2c 4 := by
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
    calc ((1358889183491/3125000000000 : ℚ) : ℝ)
        = ((272047/625000 : ℚ) : ℝ) * ((4995053/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-9855547/10000000 : ℚ) : ℝ) ≤ cos1269o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 5 - ((-9854547/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-5509418317299/12500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos1269o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((559017/1250000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-5509418317299/12500000000000 : ℚ) : ℝ)
        = ((559017/1250000 : ℚ) : ℝ) * ((-9855547/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((9266347/10000000 : ℚ) : ℝ) ≤ cos1269o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 6 - ((9267347/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((31624068579089/100000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos1269o2c 6 := by
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
    calc ((31624068579089/100000000000000 : ℚ) : ℝ)
        = ((3412787/10000000 : ℚ) : ℝ) * ((9266347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-4997597/5000000 : ℚ) : ℝ) ≤ cos1269o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 7 - ((-4997097/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-3777828502613/10000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos1269o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((755929/2000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-3777828502613/10000000000000 : ℚ) : ℝ)
        = ((755929/2000000 : ℚ) : ℝ) * ((-4997597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((9979003/10000000 : ℚ) : ℝ) ≤ cos1269o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 8 - ((9980003/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((5731430394047/20000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos1269o2c 8 := by
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
    calc ((5731430394047/20000000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((9979003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((3731497/5000000 : ℚ) : ℝ) ≤ cos1269o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 9 - ((3731997/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((1996951666017/10000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos1269o2c 9 := by
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
    calc ((1996951666017/10000000000000 : ℚ) : ℝ)
        = ((535161/2000000 : ℚ) : ℝ) * ((3731497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-9889263/10000000 : ℚ) : ℝ) ≤ cos1269o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 10 - ((-9888263/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-15636299410557/50000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos1269o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((1581139/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-15636299410557/50000000000000 : ℚ) : ℝ)
        = ((1581139/5000000 : ℚ) : ℝ) * ((-9889263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos1269o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum1269o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((1507557/5000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_5).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw1000lo : ((1584893/100000000 : ℚ) : ℝ) ≤ ((1000:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_1000_6).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((300821102427151/1000000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum1269o2_1000
    have hx1 : ((1507557/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((1584893/100000000 : ℚ) : ℝ)
          * (((189805307/10000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos1269o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/1269 + 1/2)
      ≤ ((1581139/50000000 : ℚ) : ℝ) * (2000/1269 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_1000_5).2
    have hexp : (-((((5:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(5/10) : ℝ) := by
      norm_num
    have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (1000 : ℝ) ^ (-σ - 2) ≤ ((1/25000000 : ℚ) : ℝ) := by
    have hbr := (wbr_1000_25).2
    have hexp : (-((((25:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(25/10) : ℝ) := by
      norm_num
    have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (1000 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((3163/100000000 : ℚ) : ℝ) / (3/2) := by
    have hnum : (1000 : ℝ) ^ (-σ - 1) ≤ ((3163/100000000 : ℚ) : ℝ) := by
      have hbr := (wbr_1000_15).2
      have hexp : (-((((15:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(15/10) : ℝ) := by
        norm_num
      have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos1269o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos1269o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos1269o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos1269o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos1269o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos1269o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos1269o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos1269o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos1269o2c 10) := by
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

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3200000 in
theorem seg1269o2_interval_2 {σ : ℝ} (ha : (3/5:ℝ) ≤ σ) (hb : σ ≤ (7/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((1269:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta1269o2_lower h1 h2
  have hc2 : ((9996773/10000000 : ℚ) : ℝ) ≤ cos1269o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 2 - ((9997773/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((30768677742553/50000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos1269o2c 2 := by
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
    calc ((30768677742553/50000000000000 : ℚ) : ℝ)
        = ((3077861/5000000 : ℚ) : ℝ) * ((9996773/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((9343459/10000000 : ℚ) : ℝ) ≤ cos1269o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 3 - ((9344459/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((4330347538517/10000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos1269o2c 3 := by
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
    calc ((4330347538517/10000000000000 : ℚ) : ℝ)
        = ((463463/1000000 : ℚ) : ℝ) * ((9343459/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((4995053/5000000 : ℚ) : ℝ) ≤ cos1269o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 4 - ((4995553/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((18927709377423/50000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos1269o2c 4 := by
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
    calc ((18927709377423/50000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((4995053/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-9855547/10000000 : ℚ) : ℝ) ≤ cos1269o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 5 - ((-9854547/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-9380775734369/25000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos1269o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((951827/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_6).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-9380775734369/25000000000000 : ℚ) : ℝ)
        = ((951827/2500000 : ℚ) : ℝ) * ((-9855547/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((9266347/10000000 : ℚ) : ℝ) ≤ cos1269o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 6 - ((9267347/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((26436415407303/100000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos1269o2c 6 := by
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
    calc ((26436415407303/100000000000000 : ℚ) : ℝ)
        = ((2852949/10000000 : ℚ) : ℝ) * ((9266347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-4997597/5000000 : ℚ) : ℝ) ≤ cos1269o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 7 - ((-4997097/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-3109799711623/10000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos1269o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((622259/2000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_6).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-3109799711623/10000000000000 : ℚ) : ℝ)
        = ((622259/2000000 : ℚ) : ℝ) * ((-4997597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((9979003/10000000 : ℚ) : ℝ) ≤ cos1269o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 8 - ((9980003/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((11638421387873/50000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos1269o2c 8 := by
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
    calc ((11638421387873/50000000000000 : ℚ) : ℝ)
        = ((1166291/5000000 : ℚ) : ℝ) * ((9979003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((3731497/5000000 : ℚ) : ℝ) ≤ cos1269o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 9 - ((3731997/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((400759046303/2500000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos1269o2c 9 := by
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
    calc ((400759046303/2500000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((3731497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-9889263/10000000 : ℚ) : ℝ) ≤ cos1269o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 10 - ((-9888263/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-24840711169281/100000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos1269o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((2511887/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_6).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-24840711169281/100000000000000 : ℚ) : ℝ)
        = ((2511887/10000000 : ℚ) : ℝ) * ((-9889263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos1269o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum1269o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((148267/625000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_6).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw1000lo : ((99291/12500000 : ℚ) : ℝ) ≤ ((1000:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_1000_7).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((18845958737337/125000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum1269o2_1000
    have hx1 : ((148267/625000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((99291/12500000 : ℚ) : ℝ)
          * (((189805307/10000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos1269o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/1269 + 1/2)
      ≤ ((792447/50000000 : ℚ) : ℝ) * (2000/1269 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_1000_6).2
    have hexp : (-((((6:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(6/10) : ℝ) := by
      norm_num
    have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (1000 : ℝ) ^ (-σ - 2) ≤ ((1/50000000 : ℚ) : ℝ) := by
    have hbr := (wbr_1000_26).2
    have hexp : (-((((26:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(26/10) : ℝ) := by
      norm_num
    have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (1000 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((317/20000000 : ℚ) : ℝ) / (8/5) := by
    have hnum : (1000 : ℝ) ^ (-σ - 1) ≤ ((317/20000000 : ℚ) : ℝ) := by
      have hbr := (wbr_1000_16).2
      have hexp : (-((((16:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(16/10) : ℝ) := by
        norm_num
      have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos1269o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos1269o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos1269o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos1269o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos1269o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos1269o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos1269o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos1269o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos1269o2c 10) := by
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

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3200000 in
theorem seg1269o2_interval_3 {σ : ℝ} (ha : (7/10:ℝ) ≤ σ) (hb : σ ≤ (9/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((1269:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta1269o2_lower h1 h2
  have hc2 : ((9996773/10000000 : ℚ) : ℝ) ≤ cos1269o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 2 - ((9997773/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((53571376936191/100000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos1269o2c 2 := by
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
    calc ((53571376936191/100000000000000 : ℚ) : ℝ)
        = ((5358867/10000000 : ℚ) : ℝ) * ((9996773/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((9343459/10000000 : ℚ) : ℝ) ≤ cos1269o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 3 - ((9344459/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((3476149829819/10000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos1269o2c 3 := by
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
    calc ((3476149829819/10000000000000 : ℚ) : ℝ)
        = ((372041/1000000 : ℚ) : ℝ) * ((9343459/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((4995053/5000000 : ℚ) : ℝ) ≤ cos1269o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 4 - ((4995553/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((2868903695497/10000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos1269o2c 4 := by
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
    calc ((2868903695497/10000000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((4995053/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-9855547/10000000 : ℚ) : ℝ) ≤ cos1269o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 5 - ((-9854547/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-15972461234379/50000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos1269o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((1620657/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-15972461234379/50000000000000 : ℚ) : ℝ)
        = ((1620657/5000000 : ℚ) : ℝ) * ((-9855547/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((9266347/10000000 : ℚ) : ℝ) ≤ cos1269o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 6 - ((9267347/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((9237241404073/50000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos1269o2c 6 := by
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
    calc ((9237241404073/50000000000000 : ℚ) : ℝ)
        = ((996859/5000000 : ℚ) : ℝ) * ((9266347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-4997597/5000000 : ℚ) : ℝ) ≤ cos1269o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 7 - ((-4997097/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-12799490607013/50000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos1269o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((2561129/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-12799490607013/50000000000000 : ℚ) : ℝ)
        = ((2561129/10000000 : ℚ) : ℝ) * ((-4997597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((9979003/10000000 : ℚ) : ℝ) ≤ cos1269o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 8 - ((9980003/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((1535698708679/10000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos1269o2c 8 := by
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
    calc ((1535698708679/10000000000000 : ℚ) : ℝ)
        = ((153893/1000000 : ℚ) : ℝ) * ((9979003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((3731497/5000000 : ℚ) : ℝ) ≤ cos1269o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 9 - ((3731997/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((1032986583013/10000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos1269o2c 9 := by
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
    calc ((1032986583013/10000000000000 : ℚ) : ℝ)
        = ((276829/2000000 : ℚ) : ℝ) * ((3731497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-9889263/10000000 : ℚ) : ℝ) ≤ cos1269o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 10 - ((-9888263/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-19731680561169/100000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos1269o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((1995263/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-19731680561169/100000000000000 : ℚ) : ℝ)
        = ((1995263/10000000 : ℚ) : ℝ) * ((-9889263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos1269o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum1269o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((233311/1250000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_7).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw1000lo : ((99763/50000000 : ℚ) : ℝ) ≤ ((1000:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_1000_9).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((18935546842241/500000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum1269o2_1000
    have hx1 : ((233311/1250000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((99763/50000000 : ℚ) : ℝ)
          * (((189805307/10000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos1269o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/1269 + 1/2)
      ≤ ((794329/100000000 : ℚ) : ℝ) * (2000/1269 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_1000_7).2
    have hexp : (-((((7:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(7/10) : ℝ) := by
      norm_num
    have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (1000 : ℝ) ^ (-σ - 2) ≤ ((1/100000000 : ℚ) : ℝ) := by
    have hbr := (wbr_1000_27).2
    have hexp : (-((((27:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(27/10) : ℝ) := by
      norm_num
    have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (1000 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((159/20000000 : ℚ) : ℝ) / (17/10) := by
    have hnum : (1000 : ℝ) ^ (-σ - 1) ≤ ((159/20000000 : ℚ) : ℝ) := by
      have hbr := (wbr_1000_17).2
      have hexp : (-((((17:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(17/10) : ℝ) := by
        norm_num
      have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos1269o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos1269o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos1269o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos1269o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos1269o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos1269o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos1269o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos1269o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos1269o2c 10) := by
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

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3200000 in
theorem seg1269o2_interval_4 {σ : ℝ} (ha : (9/10:ℝ) ≤ σ) (hb : σ ≤ (11/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((1269:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta1269o2_lower h1 h2
  have hc2 : ((9996773/10000000 : ℚ) : ℝ) ≤ cos1269o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 2 - ((9997773/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((11659146378943/25000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos1269o2c 2 := by
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
    calc ((11659146378943/25000000000000 : ℚ) : ℝ)
        = ((1166291/2500000 : ℚ) : ℝ) * ((9996773/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((9343459/10000000 : ℚ) : ℝ) ≤ cos1269o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 3 - ((9344459/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((872015685011/3125000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos1269o2c 3 := by
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
    calc ((872015685011/3125000000000 : ℚ) : ℝ)
        = ((93329/312500 : ℚ) : ℝ) * ((9343459/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((4995053/5000000 : ℚ) : ℝ) ≤ cos1269o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 4 - ((4995553/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((1358889183491/6250000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos1269o2c 4 := by
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
    calc ((1358889183491/6250000000000 : ℚ) : ℝ)
        = ((272047/1250000 : ℚ) : ℝ) * ((4995053/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-9855547/10000000 : ℚ) : ℝ) ≤ cos1269o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 5 - ((-9854547/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-11576512761593/50000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos1269o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((1174619/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-11576512761593/50000000000000 : ℚ) : ℝ)
        = ((1174619/5000000 : ℚ) : ℝ) * ((-9855547/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((9266347/10000000 : ℚ) : ℝ) ≤ cos1269o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 6 - ((9267347/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((806904230413/6250000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos1269o2c 6 := by
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
    calc ((806904230413/6250000000000 : ℚ) : ℝ)
        = ((87079/625000 : ℚ) : ℝ) * ((9266347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-4997597/5000000 : ℚ) : ℝ) ≤ cos1269o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 7 - ((-4997097/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-8673074716053/50000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos1269o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((1735449/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-8673074716053/50000000000000 : ℚ) : ℝ)
        = ((1735449/10000000 : ℚ) : ℝ) * ((-4997597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((9979003/10000000 : ℚ) : ℝ) ≤ cos1269o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 8 - ((9980003/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((2026366286189/20000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos1269o2c 8 := by
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
    calc ((2026366286189/20000000000000 : ℚ) : ℝ)
        = ((203063/2000000 : ℚ) : ℝ) * ((9979003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((3731497/5000000 : ℚ) : ℝ) ≤ cos1269o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 9 - ((3731997/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((665650555339/10000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos1269o2c 9 := by
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
    calc ((665650555339/10000000000000 : ℚ) : ℝ)
        = ((178387/2000000 : ℚ) : ℝ) * ((3731497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-9889263/10000000 : ℚ) : ℝ) ≤ cos1269o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 10 - ((-9888263/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-6224925155769/50000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos1269o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((629463/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-6224925155769/50000000000000 : ℚ) : ℝ)
        = ((629463/5000000 : ℚ) : ℝ) * ((-9889263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos1269o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum1269o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((577719/5000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_9).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw1000lo : ((25059/50000000 : ℚ) : ℝ) ≤ ((1000:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_1000_11).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((4756331188113/500000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum1269o2_1000
    have hx1 : ((577719/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((25059/50000000 : ℚ) : ℝ)
          * (((189805307/10000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos1269o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/1269 + 1/2)
      ≤ ((199527/100000000 : ℚ) : ℝ) * (2000/1269 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_1000_9).2
    have hexp : (-((((9:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(9/10) : ℝ) := by
      norm_num
    have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (1000 : ℝ) ^ (-σ - 2) ≤ ((1/100000000 : ℚ) : ℝ) := by
    have hbr := (wbr_1000_29).2
    have hexp : (-((((29:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(29/10) : ℝ) := by
      norm_num
    have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (1000 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((1/500000 : ℚ) : ℝ) / (19/10) := by
    have hnum : (1000 : ℝ) ^ (-σ - 1) ≤ ((1/500000 : ℚ) : ℝ) := by
      have hbr := (wbr_1000_19).2
      have hexp : (-((((19:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(19/10) : ℝ) := by
        norm_num
      have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos1269o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos1269o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos1269o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos1269o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos1269o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos1269o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos1269o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos1269o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos1269o2c 10) := by
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

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3200000 in
theorem seg1269o2_interval_5 {σ : ℝ} (ha : (11/10:ℝ) ≤ σ) (hb : σ ≤ (7/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((1269:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta1269o2_lower h1 h2
  have hc2 : ((9996773/10000000 : ℚ) : ℝ) ≤ cos1269o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 2 - ((9997773/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((37880681957943/100000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos1269o2c 2 := by
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
    calc ((37880681957943/100000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((9996773/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((9343459/10000000 : ℚ) : ℝ) ≤ cos1269o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 3 - ((9344459/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((1003478153141/5000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos1269o2c 3 := by
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
    calc ((1003478153141/5000000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((9343459/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((4995053/5000000 : ℚ) : ℝ) ≤ cos1269o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 4 - ((4995553/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((224133023163/1562500000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos1269o2c 4 := by
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
    calc ((224133023163/1562500000000 : ℚ) : ℝ)
        = ((44871/312500 : ℚ) : ℝ) * ((4995053/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-9855547/10000000 : ℚ) : ℝ) ≤ cos1269o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 5 - ((-9854547/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-419521069149/2500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos1269o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((42567/250000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-419521069149/2500000000000 : ℚ) : ℝ)
        = ((42567/250000 : ℚ) : ℝ) * ((-9855547/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((9266347/10000000 : ℚ) : ℝ) ≤ cos1269o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 6 - ((9267347/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((1885544086601/25000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos1269o2c 6 := by
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
    calc ((1885544086601/25000000000000 : ℚ) : ℝ)
        = ((203483/2500000 : ℚ) : ℝ) * ((9266347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-4997597/5000000 : ℚ) : ℝ) ≤ cos1269o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 7 - ((-4997097/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-5876969170523/50000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos1269o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((1175959/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-5876969170523/50000000000000 : ℚ) : ℝ)
        = ((1175959/10000000 : ℚ) : ℝ) * ((-4997597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((9979003/10000000 : ℚ) : ℝ) ≤ cos1269o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 8 - ((9980003/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((2714757829141/50000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos1269o2c 8 := by
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
    calc ((2714757829141/50000000000000 : ℚ) : ℝ)
        = ((272047/5000000 : ℚ) : ℝ) * ((9979003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((3731497/5000000 : ℚ) : ℝ) ≤ cos1269o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 9 - ((3731997/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((1721641817357/50000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos1269o2c 9 := by
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
    calc ((1721641817357/50000000000000 : ℚ) : ℝ)
        = ((461381/10000000 : ℚ) : ℝ) * ((3731497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-9889263/10000000 : ℚ) : ℝ) ≤ cos1269o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 10 - ((-9888263/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-7855328389527/100000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos1269o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((794329/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-7855328389527/100000000000000 : ℚ) : ℝ)
        = ((794329/10000000 : ℚ) : ℝ) * ((-9889263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos1269o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum1269o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((715267/10000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_11).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw1000lo : ((6309/100000000 : ℚ) : ℝ) ≤ ((1000:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_1000_14).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((1197481681863/1000000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum1269o2_1000
    have hx1 : ((715267/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((6309/100000000 : ℚ) : ℝ)
          * (((189805307/10000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos1269o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/1269 + 1/2)
      ≤ ((50119/100000000 : ℚ) : ℝ) * (2000/1269 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_1000_11).2
    have hexp : (-((((11:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(11/10) : ℝ) := by
      norm_num
    have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (1000 : ℝ) ^ (-σ - 2) ≤ ((1/100000000 : ℚ) : ℝ) := by
    have hbr := (wbr_1000_31).2
    have hexp : (-((((31:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(31/10) : ℝ) := by
      norm_num
    have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (1000 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((51/100000000 : ℚ) : ℝ) / (21/10) := by
    have hnum : (1000 : ℝ) ^ (-σ - 1) ≤ ((51/100000000 : ℚ) : ℝ) := by
      have hbr := (wbr_1000_21).2
      have hexp : (-((((21:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(21/10) : ℝ) := by
        norm_num
      have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos1269o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos1269o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos1269o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos1269o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos1269o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos1269o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos1269o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos1269o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos1269o2c 10) := by
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

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3200000 in
theorem seg1269o2_interval_6 {σ : ℝ} (ha : (7/5:ℝ) ≤ σ) (hb : σ ≤ (17/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((1269:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta1269o2_lower h1 h2
  have hc2 : ((9996773/10000000 : ℚ) : ℝ) ≤ cos1269o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 2 - ((9997773/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((30768677742553/100000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos1269o2c 2 := by
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
    calc ((30768677742553/100000000000000 : ℚ) : ℝ)
        = ((3077861/10000000 : ℚ) : ℝ) * ((9996773/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((9343459/10000000 : ℚ) : ℝ) ≤ cos1269o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 3 - ((9344459/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((3608621391521/25000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos1269o2c 3 := by
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
    calc ((3608621391521/25000000000000 : ℚ) : ℝ)
        = ((386219/2500000 : ℚ) : ℝ) * ((9343459/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((4995053/5000000 : ℚ) : ℝ) ≤ cos1269o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 4 - ((4995553/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((2365961799033/25000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos1269o2c 4 := by
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
    calc ((2365961799033/25000000000000 : ℚ) : ℝ)
        = ((473661/5000000 : ℚ) : ℝ) * ((4995053/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-9855547/10000000 : ℚ) : ℝ) ≤ cos1269o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 5 - ((-9854547/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-2588588986191/25000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos1269o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((262653/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-2588588986191/25000000000000 : ℚ) : ℝ)
        = ((262653/2500000 : ℚ) : ℝ) * ((-9855547/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((9266347/10000000 : ℚ) : ℝ) ≤ cos1269o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 6 - ((9267347/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((4406064601377/100000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos1269o2c 6 := by
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
    calc ((4406064601377/100000000000000 : ℚ) : ℝ)
        = ((475491/10000000 : ℚ) : ℝ) * ((9266347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-4997597/5000000 : ℚ) : ℝ) ≤ cos1269o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 7 - ((-4997097/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-1639056890493/25000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos1269o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((327969/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-1639056890493/25000000000000 : ℚ) : ℝ)
        = ((327969/5000000 : ℚ) : ℝ) * ((-4997597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((9979003/10000000 : ℚ) : ℝ) ≤ cos1269o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 8 - ((9980003/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((727399465679/25000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos1269o2c 8 := by
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
    calc ((727399465679/25000000000000 : ℚ) : ℝ)
        = ((72893/2500000 : ℚ) : ℝ) * ((9979003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((3731497/5000000 : ℚ) : ℝ) ≤ cos1269o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 9 - ((3731997/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((111321750001/6250000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos1269o2c 9 := by
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
    calc ((111321750001/6250000000000 : ℚ) : ℝ)
        = ((29833/1250000 : ℚ) : ℝ) * ((3731497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-9889263/10000000 : ℚ) : ℝ) ≤ cos1269o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 10 - ((-9888263/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-984248678601/25000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos1269o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((99527/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-984248678601/25000000000000 : ℚ) : ℝ)
        = ((99527/2500000 : ℚ) : ℝ) * ((-9889263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos1269o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum1269o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((174189/5000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_14).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw1000lo : ((397/50000000 : ℚ) : ℝ) ≤ ((1000:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_1000_17).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((75352706879/500000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum1269o2_1000
    have hx1 : ((174189/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((397/50000000 : ℚ) : ℝ)
          * (((189805307/10000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos1269o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/1269 + 1/2)
      ≤ ((631/10000000 : ℚ) : ℝ) * (2000/1269 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_1000_14).2
    have hexp : (-((((14:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(14/10) : ℝ) := by
      norm_num
    have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (1000 : ℝ) ^ (-σ - 2) ≤ ((1/100000000 : ℚ) : ℝ) := by
    have hbr := (wbr_1000_34).2
    have hexp : (-((((34:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(34/10) : ℝ) := by
      norm_num
    have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (1000 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((7/100000000 : ℚ) : ℝ) / (12/5) := by
    have hnum : (1000 : ℝ) ^ (-σ - 1) ≤ ((7/100000000 : ℚ) : ℝ) := by
      have hbr := (wbr_1000_24).2
      have hexp : (-((((24:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(24/10) : ℝ) := by
        norm_num
      have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos1269o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos1269o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos1269o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos1269o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos1269o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos1269o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos1269o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos1269o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos1269o2c 10) := by
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

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3200000 in
theorem seg1269o2_interval_7 {σ : ℝ} (ha : (17/10:ℝ) ≤ σ) (hb : σ ≤ (2:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((1269:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta1269o2_lower h1 h2
  have hc2 : ((9996773/10000000 : ℚ) : ℝ) ≤ cos1269o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 2 - ((9997773/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((9996773/40000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos1269o2c 2 := by
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
    calc ((9996773/40000000 : ℚ) : ℝ)
        = ((1/4 : ℚ) : ℝ) * ((9996773/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((9343459/10000000 : ℚ) : ℝ) ≤ cos1269o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 3 - ((9344459/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((10381620072949/100000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos1269o2c 3 := by
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
    calc ((10381620072949/100000000000000 : ℚ) : ℝ)
        = ((1111111/10000000 : ℚ) : ℝ) * ((9343459/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((4995053/5000000 : ℚ) : ℝ) ≤ cos1269o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 4 - ((4995553/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((4995053/80000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos1269o2c 4 := by
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
    calc ((4995053/80000000 : ℚ) : ℝ)
        = ((1/16 : ℚ) : ℝ) * ((4995053/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-9855547/10000000 : ℚ) : ℝ) ≤ cos1269o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 5 - ((-9854547/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-6388986464861/100000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos1269o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((648263/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-6388986464861/100000000000000 : ℚ) : ℝ)
        = ((648263/10000000 : ℚ) : ℝ) * ((-9855547/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((9266347/10000000 : ℚ) : ℝ) ≤ cos1269o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 6 - ((9267347/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((2573978070619/100000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos1269o2c 6 := by
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
    calc ((2573978070619/100000000000000 : ℚ) : ℝ)
        = ((277777/10000000 : ℚ) : ℝ) * ((9266347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-4997597/5000000 : ℚ) : ℝ) ≤ cos1269o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 7 - ((-4997097/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-457125199993/12500000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos1269o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((91469/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-457125199993/12500000000000 : ℚ) : ℝ)
        = ((91469/2500000 : ℚ) : ℝ) * ((-4997597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((9979003/10000000 : ℚ) : ℝ) ≤ cos1269o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 8 - ((9980003/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((9979003/640000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos1269o2c 8 := by
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
    calc ((9979003/640000000 : ℚ) : ℝ)
        = ((1/64 : ℚ) : ℝ) * ((9979003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((3731497/5000000 : ℚ) : ℝ) ≤ cos1269o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 9 - ((3731997/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((7198057713/781250000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos1269o2c 9 := by
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
    calc ((7198057713/781250000000 : ℚ) : ℝ)
        = ((1929/156250 : ℚ) : ℝ) * ((3731497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-9889263/10000000 : ℚ) : ℝ) ≤ cos1269o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 10 - ((-9888263/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1269o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-1973174978601/100000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos1269o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((199527/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-1973174978601/100000000000000 : ℚ) : ℝ)
        = ((199527/10000000 : ℚ) : ℝ) * ((-9889263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos1269o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum1269o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((169681/10000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_17).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw1000lo : ((1/1000000 : ℚ) : ℝ) ≤ ((1000:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_1000_20).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((189805307/10000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum1269o2_1000
    have hx1 : ((169681/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((1/1000000 : ℚ) : ℝ)
          * (((189805307/10000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos1269o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/1269 + 1/2)
      ≤ ((159/20000000 : ℚ) : ℝ) * (2000/1269 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_1000_17).2
    have hexp : (-((((17:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(17/10) : ℝ) := by
      norm_num
    have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (1000 : ℝ) ^ (-σ - 2) ≤ ((1/100000000 : ℚ) : ℝ) := by
    have hbr := (wbr_1000_37).2
    have hexp : (-((((37:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(37/10) : ℝ) := by
      norm_num
    have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (1000 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((1/100000000 : ℚ) : ℝ) / (27/10) := by
    have hnum : (1000 : ℝ) ^ (-σ - 1) ≤ ((1/100000000 : ℚ) : ℝ) := by
      have hbr := (wbr_1000_27).2
      have hexp : (-((((27:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(27/10) : ℝ) := by
        norm_num
      have hbase : (((1000:ℕ)) : ℝ) = (1000 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1269o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos1269o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos1269o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos1269o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos1269o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos1269o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos1269o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos1269o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos1269o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos1269o2c 10) := by
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

set_option maxRecDepth 32768 in
/-- **Segment positivity at the anchor 1269/2.** -/
theorem segment1269o2_re_pos {σ : ℝ} (h1 : (1/2:ℝ) ≤ σ) (h2 : σ ≤ 2) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((1269:ℕ)):ℝ)/2) * Complex.I)).re := by
  rcases le_total σ (3/5 : ℝ) with hc | hc
  · exact seg1269o2_interval_1 h1 hc
  rcases le_total σ (7/10 : ℝ) with hc2 | hc2
  · exact seg1269o2_interval_2 hc hc2
  rcases le_total σ (9/10 : ℝ) with hc3 | hc3
  · exact seg1269o2_interval_3 hc2 hc3
  rcases le_total σ (11/10 : ℝ) with hc4 | hc4
  · exact seg1269o2_interval_4 hc3 hc4
  rcases le_total σ (7/5 : ℝ) with hc5 | hc5
  · exact seg1269o2_interval_5 hc4 hc5
  rcases le_total σ (17/10 : ℝ) with hc6 | hc6
  · exact seg1269o2_interval_6 hc5 hc6
  exact seg1269o2_interval_7 hc6 h2

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.segment1269o2_re_pos
end AxiomAudit
