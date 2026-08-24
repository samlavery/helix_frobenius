import RequestProject.DVPSegment995o2Core
import RequestProject.DVPWeights289o2
import RequestProject.DVPWeights581o2
import RequestProject.DVPWeights1000col
import RequestProject.DVPWeights63
import RequestProject.DVPWeights74
import RequestProject.DVPWeights81

/-!
# Segment positivity at `t = 995/2`: rung-497.5 (seven σ-intervals, N = 1000)
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3200000 in
theorem seg995o2_interval_1 {σ : ℝ} (ha : (1/2:ℝ) ≤ σ) (hb : σ ≤ (3/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((995:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta995o2_lower h1 h2
  have hc2 : ((3710381/5000000 : ℚ) : ℝ) ≤ cos995o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 2 - ((3710881/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((24479383352359/50000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos995o2c 2 := by
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
    calc ((24479383352359/50000000000000 : ℚ) : ℝ)
        = ((6597539/10000000 : ℚ) : ℝ) * ((3710381/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((9968963/10000000 : ℚ) : ℝ) ≤ cos995o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 3 - ((9969963/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((25783815623867/50000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos995o2c 3 := by
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
    calc ((25783815623867/50000000000000 : ℚ) : ℝ)
        = ((2586409/5000000 : ℚ) : ℝ) * ((9968963/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((253939/2500000 : ℚ) : ℝ) ≤ cos995o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 4 - ((254189/2500000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((69083343133/1562500000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos995o2c 4 := by
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
    calc ((69083343133/1562500000000 : ℚ) : ℝ)
        = ((272047/625000 : ℚ) : ℝ) * ((253939/2500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-916923/1000000 : ℚ) : ℝ) ≤ cos995o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 5 - ((-916823/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-512575544691/1250000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos995o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((559017/1250000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-512575544691/1250000000000 : ℚ) : ℝ)
        = ((559017/1250000 : ℚ) : ℝ) * ((-916923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((6879577/10000000 : ℚ) : ℝ) ≤ cos995o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 6 - ((6880577/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((23478530951099/100000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos995o2c 6 := by
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
    calc ((23478530951099/100000000000000 : ℚ) : ℝ)
        = ((3412787/10000000 : ℚ) : ℝ) * ((6879577/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((8870047/10000000 : ℚ) : ℝ) ≤ cos995o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 7 - ((8871047/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((13798662005409/50000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos995o2c 7 := by
    have hwlo : ((1555647/5000000 : ℚ) : ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_7_6).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((7:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((1555647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc7).1
      (by push_cast; norm_num)
    calc ((13798662005409/50000000000000 : ℚ) : ℝ)
        = ((1555647/5000000 : ℚ) : ℝ) * ((8870047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-5913503/10000000 : ℚ) : ℝ) ≤ cos995o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 8 - ((-5912503/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-10453695457801/50000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos995o2c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((1767767/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-10453695457801/50000000000000 : ℚ) : ℝ)
        = ((1767767/5000000 : ℚ) : ℝ) * ((-5913503/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((9879069/10000000 : ℚ) : ℝ) ≤ cos995o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 9 - ((9880069/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((5286892445109/20000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos995o2c 9 := by
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
    calc ((5286892445109/20000000000000 : ℚ) : ℝ)
        = ((535161/2000000 : ℚ) : ℝ) * ((9879069/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-516141/1250000 : ℚ) : ℝ) ≤ cos995o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 10 - ((-32251/78125 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-816090664599/6250000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos995o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((1581139/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-816090664599/6250000000000 : ℚ) : ℝ)
        = ((1581139/5000000 : ℚ) : ℝ) * ((-516141/1250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos995o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum995o2_floor
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
  have htail : ((214665203182479/1000000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum995o2_1000
    have hx1 : ((1507557/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((1584893/100000000 : ℚ) : ℝ)
          * (((135444603/10000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos995o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/995 + 1/2)
      ≤ ((1581139/50000000 : ℚ) : ℝ) * (2000/995 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos995o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos995o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos995o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos995o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos995o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos995o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos995o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos995o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos995o2c 10) := by
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
theorem seg995o2_interval_2 {σ : ℝ} (ha : (3/5:ℝ) ≤ σ) (hb : σ ≤ (7/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((995:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta995o2_lower h1 h2
  have hc2 : ((3710381/5000000 : ℚ) : ℝ) ≤ cos995o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 2 - ((3710881/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((11420036975041/25000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos995o2c 2 := by
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
    calc ((11420036975041/25000000000000 : ℚ) : ℝ)
        = ((3077861/5000000 : ℚ) : ℝ) * ((3710381/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((9968963/10000000 : ℚ) : ℝ) ≤ cos995o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 3 - ((9969963/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((4620245498869/10000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos995o2c 3 := by
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
    calc ((4620245498869/10000000000000 : ℚ) : ℝ)
        = ((463463/1000000 : ℚ) : ℝ) * ((9968963/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((253939/2500000 : ℚ) : ℝ) ≤ cos995o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 4 - ((254189/2500000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((962248767249/25000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos995o2c 4 := by
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
    calc ((962248767249/25000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((253939/2500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-916923/1000000 : ℚ) : ℝ) ≤ cos995o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 5 - ((-916823/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-872752068321/2500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos995o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((951827/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_6).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-872752068321/2500000000000 : ℚ) : ℝ)
        = ((951827/2500000 : ℚ) : ℝ) * ((-916923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((6879577/10000000 : ℚ) : ℝ) ≤ cos995o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 6 - ((6880577/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((19627082322573/100000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos995o2c 6 := by
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
    calc ((19627082322573/100000000000000 : ℚ) : ℝ)
        = ((2852949/10000000 : ℚ) : ℝ) * ((6879577/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((8870047/10000000 : ℚ) : ℝ) ≤ cos995o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 7 - ((8871047/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((2839665716627/12500000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos995o2c 7 := by
    have hwlo : ((320141/1250000 : ℚ) : ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_7_7).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((7:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((320141/1250000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc7).1
      (by push_cast; norm_num)
    calc ((2839665716627/12500000000000 : ℚ) : ℝ)
        = ((320141/1250000 : ℚ) : ℝ) * ((8870047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-5913503/10000000 : ℚ) : ℝ) ≤ cos995o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 8 - ((-5912503/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-8491039293119/50000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos995o2c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((1435873/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_6).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-8491039293119/50000000000000 : ℚ) : ℝ)
        = ((1435873/5000000 : ℚ) : ℝ) * ((-5913503/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((9879069/10000000 : ℚ) : ℝ) ≤ cos995o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 9 - ((9880069/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((1061002131531/5000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos995o2c 9 := by
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
    calc ((1061002131531/5000000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((9879069/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-516141/1250000 : ℚ) : ℝ) ≤ cos995o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 10 - ((-32251/78125 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-1296487868067/12500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos995o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((2511887/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_6).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-1296487868067/12500000000000 : ℚ) : ℝ)
        = ((2511887/10000000 : ℚ) : ℝ) * ((-516141/1250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos995o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum995o2_floor
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
  have htail : ((13448430076473/125000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum995o2_1000
    have hx1 : ((148267/625000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((99291/12500000 : ℚ) : ℝ)
          * (((135444603/10000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos995o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/995 + 1/2)
      ≤ ((792447/50000000 : ℚ) : ℝ) * (2000/995 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos995o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos995o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos995o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos995o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos995o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos995o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos995o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos995o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos995o2c 10) := by
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
theorem seg995o2_interval_3 {σ : ℝ} (ha : (7/10:ℝ) ≤ σ) (hb : σ ≤ (9/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((995:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta995o2_lower h1 h2
  have hc2 : ((3710381/5000000 : ℚ) : ℝ) ≤ cos995o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 2 - ((3710881/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((19883438298327/50000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos995o2c 2 := by
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
    calc ((19883438298327/50000000000000 : ℚ) : ℝ)
        = ((5358867/10000000 : ℚ) : ℝ) * ((3710381/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((9968963/10000000 : ℚ) : ℝ) ≤ cos995o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 3 - ((9969963/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((3708862963483/10000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos995o2c 3 := by
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
    calc ((3708862963483/10000000000000 : ℚ) : ℝ)
        = ((372041/1000000 : ℚ) : ℝ) * ((9968963/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((253939/2500000 : ℚ) : ℝ) ≤ cos995o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 4 - ((254189/2500000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((145849610711/5000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos995o2c 4 := by
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
    calc ((145849610711/5000000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((253939/2500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-916923/1000000 : ℚ) : ℝ) ≤ cos995o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 5 - ((-916823/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-1486017678411/5000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos995o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((1620657/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-1486017678411/5000000000000 : ℚ) : ℝ)
        = ((1620657/5000000 : ℚ) : ℝ) * ((-916923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((6879577/10000000 : ℚ) : ℝ) ≤ cos995o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 6 - ((6880577/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((6857968248643/50000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos995o2c 6 := by
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
    calc ((6857968248643/50000000000000 : ℚ) : ℝ)
        = ((996859/5000000 : ℚ) : ℝ) * ((6879577/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((8870047/10000000 : ℚ) : ℝ) ≤ cos995o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 7 - ((8871047/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((1924188165757/12500000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos995o2c 7 := by
    have hwlo : ((216931/1250000 : ℚ) : ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_7_9).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((7:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((216931/1250000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc7).1
      (by push_cast; norm_num)
    calc ((1924188165757/12500000000000 : ℚ) : ℝ)
        = ((216931/1250000 : ℚ) : ℝ) * ((8870047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-5913503/10000000 : ℚ) : ℝ) ≤ cos995o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 8 - ((-5912503/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-13793736568249/100000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos995o2c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((2332583/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-13793736568249/100000000000000 : ℚ) : ℝ)
        = ((2332583/10000000 : ℚ) : ℝ) * ((-5913503/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((9879069/10000000 : ℚ) : ℝ) ≤ cos995o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 9 - ((9880069/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((2734812792201/20000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos995o2c 9 := by
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
    calc ((2734812792201/20000000000000 : ℚ) : ℝ)
        = ((276829/2000000 : ℚ) : ℝ) * ((9879069/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-516141/1250000 : ℚ) : ℝ) ≤ cos995o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 10 - ((-32251/78125 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-1029837040083/12500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos995o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((1995263/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-1029837040083/12500000000000 : ℚ) : ℝ)
        = ((1995263/10000000 : ℚ) : ℝ) * ((-516141/1250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos995o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum995o2_floor
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
  have htail : ((13512359929089/500000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum995o2_1000
    have hx1 : ((233311/1250000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((99763/50000000 : ℚ) : ℝ)
          * (((135444603/10000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos995o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/995 + 1/2)
      ≤ ((794329/100000000 : ℚ) : ℝ) * (2000/995 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos995o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos995o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos995o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos995o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos995o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos995o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos995o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos995o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos995o2c 10) := by
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
theorem seg995o2_interval_4 {σ : ℝ} (ha : (9/10:ℝ) ≤ σ) (hb : σ ≤ (11/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((995:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta995o2_lower h1 h2
  have hc2 : ((3710381/5000000 : ℚ) : ℝ) ≤ cos995o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 2 - ((3710881/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((4327383966871/12500000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos995o2c 2 := by
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
    calc ((4327383966871/12500000000000 : ℚ) : ℝ)
        = ((1166291/2500000 : ℚ) : ℝ) * ((3710381/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((9968963/10000000 : ℚ) : ℝ) ≤ cos995o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 3 - ((9969963/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((930393347827/3125000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos995o2c 3 := by
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
    calc ((930393347827/3125000000000 : ℚ) : ℝ)
        = ((93329/312500 : ℚ) : ℝ) * ((9968963/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((253939/2500000 : ℚ) : ℝ) ≤ cos995o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 4 - ((254189/2500000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((69083343133/3125000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos995o2c 4 := by
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
    calc ((69083343133/3125000000000 : ℚ) : ℝ)
        = ((272047/1250000 : ℚ) : ℝ) * ((253939/2500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-916923/1000000 : ℚ) : ℝ) ≤ cos995o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 5 - ((-916823/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-1077035177337/5000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos995o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((1174619/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-1077035177337/5000000000000 : ℚ) : ℝ)
        = ((1174619/5000000 : ℚ) : ℝ) * ((-916923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((6879577/10000000 : ℚ) : ℝ) ≤ cos995o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 6 - ((6880577/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((599066685583/6250000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos995o2c 6 := by
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
    calc ((599066685583/6250000000000 : ℚ) : ℝ)
        = ((87079/625000 : ℚ) : ℝ) * ((6879577/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((8870047/10000000 : ℚ) : ℝ) ≤ cos995o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 7 - ((8871047/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((5215401365013/50000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos995o2c 7 := by
    have hwlo : ((587979/5000000 : ℚ) : ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_7_11).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((7:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((587979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc7).1
      (by push_cast; norm_num)
    calc ((5215401365013/50000000000000 : ℚ) : ℝ)
        = ((587979/5000000 : ℚ) : ℝ) * ((8870047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-5913503/10000000 : ℚ) : ℝ) ≤ cos995o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 8 - ((-5912503/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-9100473085293/100000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos995o2c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((1538931/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-9100473085293/100000000000000 : ℚ) : ℝ)
        = ((1538931/10000000 : ℚ) : ℝ) * ((-5913503/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((9879069/10000000 : ℚ) : ℝ) ≤ cos995o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 9 - ((9880069/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((1762297481703/20000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos995o2c 9 := by
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
    calc ((1762297481703/20000000000000 : ℚ) : ℝ)
        = ((178387/2000000 : ℚ) : ℝ) * ((9879069/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-516141/1250000 : ℚ) : ℝ) ≤ cos995o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 10 - ((-32251/78125 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-324891662283/6250000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos995o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((629463/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-324891662283/6250000000000 : ℚ) : ℝ)
        = ((629463/5000000 : ℚ) : ℝ) * ((-516141/1250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos995o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum995o2_floor
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
  have htail : ((3394106306577/500000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum995o2_1000
    have hx1 : ((577719/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((25059/50000000 : ℚ) : ℝ)
          * (((135444603/10000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos995o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/995 + 1/2)
      ≤ ((199527/100000000 : ℚ) : ℝ) * (2000/995 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos995o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos995o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos995o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos995o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos995o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos995o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos995o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos995o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos995o2c 10) := by
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
theorem seg995o2_interval_5 {σ : ℝ} (ha : (11/10:ℝ) ≤ σ) (hb : σ ≤ (7/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((995:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta995o2_lower h1 h2
  have hc2 : ((3710381/5000000 : ℚ) : ℝ) ≤ cos995o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 2 - ((3710881/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((14059713329871/50000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos995o2c 2 := by
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
    calc ((14059713329871/50000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((3710381/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((9968963/10000000 : ℚ) : ℝ) ≤ cos995o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 3 - ((9969963/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((1070656657237/5000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos995o2c 3 := by
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
    calc ((1070656657237/5000000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((9968963/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((253939/2500000 : ℚ) : ℝ) ≤ cos995o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 4 - ((254189/2500000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((11394496869/781250000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos995o2c 4 := by
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
    calc ((11394496869/781250000000 : ℚ) : ℝ)
        = ((44871/312500 : ℚ) : ℝ) * ((253939/2500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-916923/1000000 : ℚ) : ℝ) ≤ cos995o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 5 - ((-916823/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-39030661341/250000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos995o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((42567/250000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-39030661341/250000000000 : ℚ) : ℝ)
        = ((42567/250000 : ℚ) : ℝ) * ((-916923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((6879577/10000000 : ℚ) : ℝ) ≤ cos995o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 6 - ((6880577/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((1399876966691/25000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos995o2c 6 := by
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
    calc ((1399876966691/25000000000000 : ℚ) : ℝ)
        = ((203483/2500000 : ℚ) : ℝ) * ((6879577/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((8870047/10000000 : ℚ) : ℝ) ≤ cos995o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 7 - ((8871047/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((5818192019039/100000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos995o2c 7 := by
    have hwlo : ((655937/10000000 : ℚ) : ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_7_14).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((7:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((655937/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc7).1
      (by push_cast; norm_num)
    calc ((5818192019039/100000000000000 : ℚ) : ℝ)
        = ((655937/10000000 : ℚ) : ℝ) * ((8870047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-5913503/10000000 : ℚ) : ℝ) ≤ cos995o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 8 - ((-5912503/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-1501018552987/25000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos995o2c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((253829/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-1501018552987/25000000000000 : ℚ) : ℝ)
        = ((253829/2500000 : ℚ) : ℝ) * ((-5913503/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((9879069/10000000 : ℚ) : ℝ) ≤ cos995o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 9 - ((9880069/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((4558014734289/100000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos995o2c 9 := by
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
    calc ((4558014734289/100000000000000 : ℚ) : ℝ)
        = ((461381/10000000 : ℚ) : ℝ) * ((9879069/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-516141/1250000 : ℚ) : ℝ) ≤ cos995o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 10 - ((-32251/78125 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-409985764389/12500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos995o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((794329/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-409985764389/12500000000000 : ℚ) : ℝ)
        = ((794329/10000000 : ℚ) : ℝ) * ((-516141/1250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos995o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum995o2_floor
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
  have htail : ((854520000327/1000000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum995o2_1000
    have hx1 : ((715267/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((6309/100000000 : ℚ) : ℝ)
          * (((135444603/10000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos995o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/995 + 1/2)
      ≤ ((50119/100000000 : ℚ) : ℝ) * (2000/995 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos995o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos995o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos995o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos995o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos995o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos995o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos995o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos995o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos995o2c 10) := by
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
theorem seg995o2_interval_6 {σ : ℝ} (ha : (7/5:ℝ) ≤ σ) (hb : σ ≤ (17/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((995:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta995o2_lower h1 h2
  have hc2 : ((3710381/5000000 : ℚ) : ℝ) ≤ cos995o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 2 - ((3710881/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((11420036975041/50000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos995o2c 2 := by
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
    calc ((11420036975041/50000000000000 : ℚ) : ℝ)
        = ((3077861/10000000 : ℚ) : ℝ) * ((3710381/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((9968963/10000000 : ℚ) : ℝ) ≤ cos995o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 3 - ((9969963/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((3850202920897/25000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos995o2c 3 := by
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
    calc ((3850202920897/25000000000000 : ℚ) : ℝ)
        = ((386219/2500000 : ℚ) : ℝ) * ((9968963/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((253939/2500000 : ℚ) : ℝ) ≤ cos995o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 4 - ((254189/2500000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((120281000679/12500000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos995o2c 4 := by
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
    calc ((120281000679/12500000000000 : ℚ) : ℝ)
        = ((473661/5000000 : ℚ) : ℝ) * ((253939/2500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-916923/1000000 : ℚ) : ℝ) ≤ cos995o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 5 - ((-916823/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-240832576719/2500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos995o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((262653/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-240832576719/2500000000000 : ℚ) : ℝ)
        = ((262653/2500000 : ℚ) : ℝ) * ((-916923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((6879577/10000000 : ℚ) : ℝ) ≤ cos995o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 6 - ((6880577/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((3271176947307/100000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos995o2c 6 := by
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
    calc ((3271176947307/100000000000000 : ℚ) : ℝ)
        = ((475491/10000000 : ℚ) : ℝ) * ((6879577/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((8870047/10000000 : ℚ) : ℝ) ≤ cos995o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 7 - ((8871047/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((25962627569/800000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos995o2c 7 := by
    have hwlo : ((2927/80000 : ℚ) : ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_7_17).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((7:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((2927/80000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc7).1
      (by push_cast; norm_num)
    calc ((25962627569/800000000000 : ℚ) : ℝ)
        = ((2927/80000 : ℚ) : ℝ) * ((8870047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-5913503/10000000 : ℚ) : ℝ) ≤ cos995o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 8 - ((-5912503/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-643501482957/20000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos995o2c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((108819/2000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-643501482957/20000000000000 : ℚ) : ℝ)
        = ((108819/2000000 : ℚ) : ℝ) * ((-5913503/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((9879069/10000000 : ℚ) : ℝ) ≤ cos995o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 9 - ((9880069/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((294722265477/12500000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos995o2c 9 := by
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
    calc ((294722265477/12500000000000 : ℚ) : ℝ)
        = ((29833/1250000 : ℚ) : ℝ) * ((9879069/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-516141/1250000 : ℚ) : ℝ) ≤ cos995o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 10 - ((-32251/78125 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-51369965307/3125000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos995o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((99527/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-51369965307/3125000000000 : ℚ) : ℝ)
        = ((99527/2500000 : ℚ) : ℝ) * ((-516141/1250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos995o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum995o2_floor
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
  have htail : ((53771507391/500000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum995o2_1000
    have hx1 : ((174189/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((397/50000000 : ℚ) : ℝ)
          * (((135444603/10000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos995o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/995 + 1/2)
      ≤ ((631/10000000 : ℚ) : ℝ) * (2000/995 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos995o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos995o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos995o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos995o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos995o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos995o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos995o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos995o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos995o2c 10) := by
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
theorem seg995o2_interval_7 {σ : ℝ} (ha : (17/10:ℝ) ≤ σ) (hb : σ ≤ (2:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((995:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta995o2_lower h1 h2
  have hc2 : ((3710381/5000000 : ℚ) : ℝ) ≤ cos995o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 2 - ((3710881/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((3710381/20000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos995o2c 2 := by
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
    calc ((3710381/20000000 : ℚ) : ℝ)
        = ((1/4 : ℚ) : ℝ) * ((3710381/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((9968963/10000000 : ℚ) : ℝ) ≤ cos995o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 3 - ((9969963/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((11076624447893/100000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos995o2c 3 := by
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
    calc ((11076624447893/100000000000000 : ℚ) : ℝ)
        = ((1111111/10000000 : ℚ) : ℝ) * ((9968963/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((253939/2500000 : ℚ) : ℝ) ≤ cos995o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 4 - ((254189/2500000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((253939/40000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos995o2c 4 := by
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
    calc ((253939/40000000 : ℚ) : ℝ)
        = ((1/16 : ℚ) : ℝ) * ((253939/2500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-916923/1000000 : ℚ) : ℝ) ≤ cos995o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 5 - ((-916823/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-594407254749/10000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos995o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((648263/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-594407254749/10000000000000 : ℚ) : ℝ)
        = ((648263/10000000 : ℚ) : ℝ) * ((-916923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((6879577/10000000 : ℚ) : ℝ) ≤ cos995o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 6 - ((6880577/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((1910988260329/100000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos995o2c 6 := by
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
    calc ((1910988260329/100000000000000 : ℚ) : ℝ)
        = ((277777/10000000 : ℚ) : ℝ) * ((6879577/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((8870047/10000000 : ℚ) : ℝ) ≤ cos995o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 7 - ((8871047/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((1810208061807/100000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos995o2c 7 := by
    have hwlo : ((204081/10000000 : ℚ) : ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_7_20).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((7:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((204081/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc7).1
      (by push_cast; norm_num)
    calc ((1810208061807/100000000000000 : ℚ) : ℝ)
        = ((204081/10000000 : ℚ) : ℝ) * ((8870047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-5913503/10000000 : ℚ) : ℝ) ≤ cos995o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 8 - ((-5912503/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-1724217810219/100000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos995o2c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((291573/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-1724217810219/100000000000000 : ℚ) : ℝ)
        = ((291573/10000000 : ℚ) : ℝ) * ((-5913503/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((9879069/10000000 : ℚ) : ℝ) ≤ cos995o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 9 - ((9880069/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((19056724101/1562500000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos995o2c 9 := by
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
    calc ((19056724101/1562500000000 : ℚ) : ℝ)
        = ((1929/156250 : ℚ) : ℝ) * ((9879069/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-516141/1250000 : ℚ) : ℝ) ≤ cos995o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 10 - ((-32251/78125 : ℚ) : ℝ) :=
      (abs_le.mp cos995o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-102984065307/12500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos995o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((199527/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-102984065307/12500000000000 : ℚ) : ℝ)
        = ((199527/10000000 : ℚ) : ℝ) * ((-516141/1250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos995o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum995o2_floor
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
  have htail : ((135444603/10000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum995o2_1000
    have hx1 : ((169681/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((1/1000000 : ℚ) : ℝ)
          * (((135444603/10000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos995o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/995 + 1/2)
      ≤ ((159/20000000 : ℚ) : ℝ) * (2000/995 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos995o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos995o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos995o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos995o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos995o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos995o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos995o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos995o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos995o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos995o2c 10) := by
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
/-- **Segment positivity at the anchor 995/2.** -/
theorem segment995o2_re_pos {σ : ℝ} (h1 : (1/2:ℝ) ≤ σ) (h2 : σ ≤ 2) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((995:ℕ)):ℝ)/2) * Complex.I)).re := by
  rcases le_total σ (3/5 : ℝ) with hc | hc
  · exact seg995o2_interval_1 h1 hc
  rcases le_total σ (7/10 : ℝ) with hc2 | hc2
  · exact seg995o2_interval_2 hc hc2
  rcases le_total σ (9/10 : ℝ) with hc3 | hc3
  · exact seg995o2_interval_3 hc2 hc3
  rcases le_total σ (11/10 : ℝ) with hc4 | hc4
  · exact seg995o2_interval_4 hc3 hc4
  rcases le_total σ (7/5 : ℝ) with hc5 | hc5
  · exact seg995o2_interval_5 hc4 hc5
  rcases le_total σ (17/10 : ℝ) with hc6 | hc6
  · exact seg995o2_interval_6 hc5 hc6
  exact seg995o2_interval_7 hc6 h2

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.segment995o2_re_pos
end AxiomAudit
