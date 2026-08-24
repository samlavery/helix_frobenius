import RequestProject.DVPSegment581o2Core
import RequestProject.DVPWeights289o2
import RequestProject.DVPWeights581o2
import RequestProject.DVPWeights63
import RequestProject.DVPWeights74
import RequestProject.DVPWeights81

/-!
# Segment positivity at `t = 581/2`: rung-290.5 (seven σ-intervals, N = 500)
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
theorem seg581o2_interval_1 {σ : ℝ} (ha : (1/2:ℝ) ≤ σ) (hb : σ ≤ (3/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((581:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta581o2_lower h1 h2
  have hc2 : ((478013/500000 : ℚ) : ℝ) ≤ cos581o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 2 - ((478063/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((3153709410007/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos581o2c 2 := by
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
    calc ((3153709410007/5000000000000 : ℚ) : ℝ)
        = ((6597539/10000000 : ℚ) : ℝ) * ((478013/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((67911/250000 : ℚ) : ℝ) ≤ cos581o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 3 - ((4246/15625 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((175645621599/1250000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos581o2c 3 := by
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
    calc ((175645621599/1250000000000 : ℚ) : ℝ)
        = ((2586409/5000000 : ℚ) : ℝ) * ((67911/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((165649/200000 : ℚ) : ℝ) ≤ cos581o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 4 - ((165669/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((45064313503/125000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos581o2c 4 := by
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
    calc ((45064313503/125000000000 : ℚ) : ℝ)
        = ((272047/625000 : ℚ) : ℝ) * ((165649/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-424847/500000 : ℚ) : ℝ) ≤ cos581o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 5 - ((-424797/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-237496695399/625000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos581o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((559017/1250000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-237496695399/625000000000 : ℚ) : ℝ)
        = ((559017/1250000 : ℚ) : ℝ) * ((-424847/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((108333/200000 : ℚ) : ℝ) ≤ cos581o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 6 - ((108353/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((369717454071/2000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos581o2c 6 := by
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
    calc ((369717454071/2000000000000 : ℚ) : ℝ)
        = ((3412787/10000000 : ℚ) : ℝ) * ((108333/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((98001/100000 : ℚ) : ℝ) ≤ cos581o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 7 - ((98011/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((152454961647/500000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos581o2c 7 := by
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
    calc ((152454961647/500000000000 : ℚ) : ℝ)
        = ((1555647/5000000 : ℚ) : ℝ) * ((98001/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((156943/250000 : ℚ) : ℝ) ≤ cos581o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 8 - ((19621/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((90140055107/500000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos581o2c 8 := by
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
    calc ((90140055107/500000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((156943/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((-852403/1000000 : ℚ) : ℝ) ≤ cos581o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 9 - ((-852303/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((-1420671950801/5000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos581o2c 9 := by
    have hw : ((9:ℕ) : ℝ) ^ (-σ) ≤ ((1666667/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_9_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc9).2
      (by push_cast; norm_num)
    calc ((-1420671950801/5000000000000 : ℚ) : ℝ)
        = ((1666667/5000000 : ℚ) : ℝ) * ((-852403/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-966931/1000000 : ℚ) : ℝ) ≤ cos581o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 10 - ((-966831/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-1528852314409/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos581o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((1581139/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-1528852314409/5000000000000 : ℚ) : ℝ)
        = ((1581139/5000000 : ℚ) : ℝ) * ((-966931/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos581o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum581o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((1507557/5000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_5).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw500lo : ((7507/312500 : ℚ) : ℝ) ≤ ((500:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_500_6).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((8357685733/31250000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum581o2_500
    have hx1 : ((1507557/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((7507/312500 : ℚ) : ℝ)
          * (((1113319/100000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos581o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/581 + 1/2)
      ≤ ((223607/5000000 : ℚ) : ℝ) * (1000/581 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_500_5).2
    have hexp : (-((((5:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(5/10) : ℝ) := by
      norm_num
    have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (500 : ℝ) ^ (-σ - 2) ≤ ((1/5000000 : ℚ) : ℝ) := by
    have hbr := (wbr_500_25).2
    have hexp : (-((((25:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(25/10) : ℝ) := by
      norm_num
    have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (500 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((179/2000000 : ℚ) : ℝ) / (3/2) := by
    have hnum : (500 : ℝ) ^ (-σ - 1) ≤ ((179/2000000 : ℚ) : ℝ) := by
      have hbr := (wbr_500_15).2
      have hexp : (-((((15:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(15/10) : ℝ) := by
        norm_num
      have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos581o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos581o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos581o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos581o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos581o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos581o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos581o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos581o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos581o2c 10) := by
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

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
theorem seg581o2_interval_2 {σ : ℝ} (ha : (3/5:ℝ) ≤ σ) (hb : σ ≤ (7/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((581:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta581o2_lower h1 h2
  have hc2 : ((478013/500000 : ℚ) : ℝ) ≤ cos581o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 2 - ((478063/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1471257570193/2500000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos581o2c 2 := by
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
    calc ((1471257570193/2500000000000 : ℚ) : ℝ)
        = ((3077861/5000000 : ℚ) : ℝ) * ((478013/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((67911/250000 : ℚ) : ℝ) ≤ cos581o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 3 - ((4246/15625 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((31474235793/250000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos581o2c 3 := by
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
    calc ((31474235793/250000000000 : ℚ) : ℝ)
        = ((463463/1000000 : ℚ) : ℝ) * ((67911/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((165649/200000 : ℚ) : ℝ) ≤ cos581o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 4 - ((165669/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((627692264859/2000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos581o2c 4 := by
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
    calc ((627692264859/2000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((165649/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-424847/500000 : ℚ) : ℝ) ≤ cos581o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 5 - ((-424797/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-404380845469/1250000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos581o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((951827/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_6).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-404380845469/1250000000000 : ℚ) : ℝ)
        = ((951827/2500000 : ℚ) : ℝ) * ((-424847/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((108333/200000 : ℚ) : ℝ) ≤ cos581o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 6 - ((108353/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((309068524017/2000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos581o2c 6 := by
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
    calc ((309068524017/2000000000000 : ℚ) : ℝ)
        = ((2852949/10000000 : ℚ) : ℝ) * ((108333/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((98001/100000 : ℚ) : ℝ) ≤ cos581o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 7 - ((98011/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((31374138141/125000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos581o2c 7 := by
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
    calc ((31374138141/125000000000 : ℚ) : ℝ)
        = ((320141/1250000 : ℚ) : ℝ) * ((98001/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((156943/250000 : ℚ) : ℝ) ≤ cos581o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 8 - ((19621/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((183041208413/1250000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos581o2c 8 := by
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
    calc ((183041208413/1250000000000 : ℚ) : ℝ)
        = ((1166291/5000000 : ℚ) : ℝ) * ((156943/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((-852403/1000000 : ℚ) : ℝ) ≤ cos581o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 9 - ((-852303/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((-1140432530909/5000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos581o2c 9 := by
    have hw : ((9:ℕ) : ℝ) ^ (-σ) ≤ ((1337903/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_9_6).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc9).2
      (by push_cast; norm_num)
    calc ((-1140432530909/5000000000000 : ℚ) : ℝ)
        = ((1337903/5000000 : ℚ) : ℝ) * ((-852403/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-966931/1000000 : ℚ) : ℝ) ≤ cos581o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 10 - ((-966831/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-2428821408797/10000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos581o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((2511887/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_6).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-2428821408797/10000000000000 : ℚ) : ℝ)
        = ((2511887/10000000 : ℚ) : ℝ) * ((-966931/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos581o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum581o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((148267/625000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_6).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw500lo : ((129039/10000000 : ℚ) : ℝ) ≤ ((500:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_500_7).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((143661570441/1000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum581o2_500
    have hx1 : ((148267/625000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((129039/10000000 : ℚ) : ℝ)
          * (((1113319/100000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos581o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/581 + 1/2)
      ≤ ((9609/400000 : ℚ) : ℝ) * (1000/581 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_500_6).2
    have hexp : (-((((6:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(6/10) : ℝ) := by
      norm_num
    have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (500 : ℝ) ^ (-σ - 2) ≤ ((1/10000000 : ℚ) : ℝ) := by
    have hbr := (wbr_500_26).2
    have hexp : (-((((26:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(26/10) : ℝ) := by
      norm_num
    have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (500 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((481/10000000 : ℚ) : ℝ) / (8/5) := by
    have hnum : (500 : ℝ) ^ (-σ - 1) ≤ ((481/10000000 : ℚ) : ℝ) := by
      have hbr := (wbr_500_16).2
      have hexp : (-((((16:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(16/10) : ℝ) := by
        norm_num
      have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos581o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos581o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos581o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos581o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos581o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos581o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos581o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos581o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos581o2c 10) := by
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

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
theorem seg581o2_interval_3 {σ : ℝ} (ha : (7/10:ℝ) ≤ σ) (hb : σ ≤ (9/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((581:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta581o2_lower h1 h2
  have hc2 : ((478013/500000 : ℚ) : ℝ) ≤ cos581o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 2 - ((478063/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((2561608091271/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos581o2c 2 := by
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
    calc ((2561608091271/5000000000000 : ℚ) : ℝ)
        = ((5358867/10000000 : ℚ) : ℝ) * ((478013/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((67911/250000 : ℚ) : ℝ) ≤ cos581o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 3 - ((4246/15625 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((25265676351/250000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos581o2c 3 := by
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
    calc ((25265676351/250000000000 : ℚ) : ℝ)
        = ((372041/1000000 : ℚ) : ℝ) * ((67911/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((165649/200000 : ℚ) : ℝ) ≤ cos581o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 4 - ((165669/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((95140337501/400000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos581o2c 4 := by
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
    calc ((95140337501/400000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((165649/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-424847/500000 : ℚ) : ℝ) ≤ cos581o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 5 - ((-424797/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-688531264479/2500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos581o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((1620657/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-688531264479/2500000000000 : ℚ) : ℝ)
        = ((1620657/5000000 : ℚ) : ℝ) * ((-424847/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((108333/200000 : ℚ) : ℝ) ≤ cos581o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 6 - ((108353/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((107992726047/1000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos581o2c 6 := by
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
    calc ((107992726047/1000000000000 : ℚ) : ℝ)
        = ((996859/5000000 : ℚ) : ℝ) * ((108333/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((98001/100000 : ℚ) : ℝ) ≤ cos581o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 7 - ((98011/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((21259454931/125000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos581o2c 7 := by
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
    calc ((21259454931/125000000000 : ℚ) : ℝ)
        = ((216931/1250000 : ℚ) : ℝ) * ((98001/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((156943/250000 : ℚ) : ℝ) ≤ cos581o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 8 - ((19621/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((24152429099/250000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos581o2c 8 := by
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
    calc ((24152429099/250000000000 : ℚ) : ℝ)
        = ((153893/1000000 : ℚ) : ℝ) * ((156943/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((-852403/1000000 : ℚ) : ℝ) ≤ cos581o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 9 - ((-852303/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((-1830945448343/10000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos581o2c 9 := by
    have hw : ((9:ℕ) : ℝ) ^ (-σ) ≤ ((2147981/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_9_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc9).2
      (by push_cast; norm_num)
    calc ((-1830945448343/10000000000000 : ℚ) : ℝ)
        = ((2147981/10000000 : ℚ) : ℝ) * ((-852403/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-966931/1000000 : ℚ) : ℝ) ≤ cos581o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 10 - ((-966831/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-1929281647853/10000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos581o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((1995263/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-1929281647853/10000000000000 : ℚ) : ℝ)
        = ((1995263/10000000 : ℚ) : ℝ) * ((-966931/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos581o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum581o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((233311/1250000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_7).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw500lo : ((2327/625000 : ℚ) : ℝ) ≤ ((500:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_500_9).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((2590693313/62500000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum581o2_500
    have hx1 : ((233311/1250000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((2327/625000 : ℚ) : ℝ)
          * (((1113319/100000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos581o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/581 + 1/2)
      ≤ ((1613/125000 : ℚ) : ℝ) * (1000/581 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_500_7).2
    have hexp : (-((((7:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(7/10) : ℝ) := by
      norm_num
    have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (500 : ℝ) ^ (-σ - 2) ≤ ((1/10000000 : ℚ) : ℝ) := by
    have hbr := (wbr_500_27).2
    have hexp : (-((((27:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(27/10) : ℝ) := by
      norm_num
    have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (500 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((259/10000000 : ℚ) : ℝ) / (17/10) := by
    have hnum : (500 : ℝ) ^ (-σ - 1) ≤ ((259/10000000 : ℚ) : ℝ) := by
      have hbr := (wbr_500_17).2
      have hexp : (-((((17:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(17/10) : ℝ) := by
        norm_num
      have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos581o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos581o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos581o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos581o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos581o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos581o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos581o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos581o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos581o2c 10) := by
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

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
theorem seg581o2_interval_4 {σ : ℝ} (ha : (9/10:ℝ) ≤ σ) (hb : σ ≤ (11/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((581:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta581o2_lower h1 h2
  have hc2 : ((478013/500000 : ℚ) : ℝ) ≤ cos581o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 2 - ((478063/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((557502259783/1250000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos581o2c 2 := by
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
    calc ((557502259783/1250000000000 : ℚ) : ℝ)
        = ((1166291/2500000 : ℚ) : ℝ) * ((478013/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((67911/250000 : ℚ) : ℝ) ≤ cos581o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 3 - ((4246/15625 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((6338065719/78125000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos581o2c 3 := by
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
    calc ((6338065719/78125000000 : ℚ) : ℝ)
        = ((93329/312500 : ℚ) : ℝ) * ((67911/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((165649/200000 : ℚ) : ℝ) ≤ cos581o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 4 - ((165669/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((45064313503/250000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos581o2c 4 := by
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
    calc ((45064313503/250000000000 : ℚ) : ℝ)
        = ((272047/1250000 : ℚ) : ℝ) * ((165649/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-424847/500000 : ℚ) : ℝ) ≤ cos581o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 5 - ((-424797/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-499033358293/2500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos581o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((1174619/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-499033358293/2500000000000 : ℚ) : ℝ)
        = ((1174619/5000000 : ℚ) : ℝ) * ((-424847/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((108333/200000 : ℚ) : ℝ) ≤ cos581o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 6 - ((108353/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((9433529307/125000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos581o2c 6 := by
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
    calc ((9433529307/125000000000 : ℚ) : ℝ)
        = ((87079/625000 : ℚ) : ℝ) * ((108333/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((98001/100000 : ℚ) : ℝ) ≤ cos581o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 7 - ((98011/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((57622529979/500000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos581o2c 7 := by
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
    calc ((57622529979/500000000000 : ℚ) : ℝ)
        = ((587979/5000000 : ℚ) : ℝ) * ((98001/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((156943/250000 : ℚ) : ℝ) ≤ cos581o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 8 - ((19621/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((31869316409/500000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos581o2c 8 := by
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
    calc ((31869316409/500000000000 : ℚ) : ℝ)
        = ((203063/2000000 : ℚ) : ℝ) * ((156943/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((-852403/1000000 : ℚ) : ℝ) ≤ cos581o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 9 - ((-852303/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((-589925101419/5000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos581o2c 9 := by
    have hw : ((9:ℕ) : ℝ) ^ (-σ) ≤ ((692073/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_9_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc9).2
      (by push_cast; norm_num)
    calc ((-589925101419/5000000000000 : ℚ) : ℝ)
        = ((692073/5000000 : ℚ) : ℝ) * ((-852403/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-966931/1000000 : ℚ) : ℝ) ≤ cos581o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 10 - ((-966831/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-608647288053/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos581o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((629463/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-608647288053/5000000000000 : ℚ) : ℝ)
        = ((629463/5000000 : ℚ) : ℝ) * ((-966931/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos581o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum581o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((577719/5000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_9).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw500lo : ((10743/10000000 : ℚ) : ℝ) ≤ ((500:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_500_11).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((11960386017/1000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum581o2_500
    have hx1 : ((577719/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((10743/10000000 : ℚ) : ℝ)
          * (((1113319/100000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos581o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/581 + 1/2)
      ≤ ((37233/10000000 : ℚ) : ℝ) * (1000/581 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_500_9).2
    have hexp : (-((((9:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(9/10) : ℝ) := by
      norm_num
    have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (500 : ℝ) ^ (-σ - 2) ≤ ((1/10000000 : ℚ) : ℝ) := by
    have hbr := (wbr_500_29).2
    have hexp : (-((((29:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(29/10) : ℝ) := by
      norm_num
    have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (500 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((3/400000 : ℚ) : ℝ) / (19/10) := by
    have hnum : (500 : ℝ) ^ (-σ - 1) ≤ ((3/400000 : ℚ) : ℝ) := by
      have hbr := (wbr_500_19).2
      have hexp : (-((((19:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(19/10) : ℝ) := by
        norm_num
      have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos581o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos581o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos581o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos581o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos581o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos581o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos581o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos581o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos581o2c 10) := by
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

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
theorem seg581o2_interval_5 {σ : ℝ} (ha : (11/10:ℝ) ≤ σ) (hb : σ ≤ (7/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((581:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta581o2_lower h1 h2
  have hc2 : ((478013/500000 : ℚ) : ℝ) ≤ cos581o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 2 - ((478063/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1811330358783/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos581o2c 2 := by
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
    calc ((1811330358783/5000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((478013/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((67911/250000 : ℚ) : ℝ) ≤ cos581o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 3 - ((4246/15625 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((7293573489/125000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos581o2c 3 := by
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
    calc ((7293573489/125000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((67911/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((165649/200000 : ℚ) : ℝ) ≤ cos581o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 4 - ((165669/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((7432836279/62500000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos581o2c 4 := by
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
    calc ((7432836279/62500000000 : ℚ) : ℝ)
        = ((44871/312500 : ℚ) : ℝ) * ((165649/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-424847/500000 : ℚ) : ℝ) ≤ cos581o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 5 - ((-424797/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-18084462249/125000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos581o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((42567/250000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-18084462249/125000000000 : ℚ) : ℝ)
        = ((42567/250000 : ℚ) : ℝ) * ((-424847/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((108333/200000 : ℚ) : ℝ) ≤ cos581o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 6 - ((108353/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((22043923839/500000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos581o2c 6 := by
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
    calc ((22043923839/500000000000 : ℚ) : ℝ)
        = ((203483/2500000 : ℚ) : ℝ) * ((108333/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((98001/100000 : ℚ) : ℝ) ≤ cos581o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 7 - ((98011/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((64282481937/1000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos581o2c 7 := by
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
    calc ((64282481937/1000000000000 : ℚ) : ℝ)
        = ((655937/10000000 : ℚ) : ℝ) * ((98001/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((156943/250000 : ℚ) : ℝ) ≤ cos581o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 8 - ((19621/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((42695872321/1250000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos581o2c 8 := by
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
    calc ((42695872321/1250000000000 : ℚ) : ℝ)
        = ((272047/5000000 : ℚ) : ℝ) * ((156943/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((-852403/1000000 : ℚ) : ℝ) ≤ cos581o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 9 - ((-852303/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((-23759028819/312500000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos581o2c 9 := by
    have hw : ((9:ℕ) : ℝ) ^ (-σ) ≤ ((27873/312500 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_9_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc9).2
      (by push_cast; norm_num)
    calc ((-23759028819/312500000000 : ℚ) : ℝ)
        = ((27873/312500 : ℚ) : ℝ) * ((-852403/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-966931/1000000 : ℚ) : ℝ) ≤ cos581o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 10 - ((-966831/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-768061334299/10000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos581o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((794329/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-768061334299/10000000000000 : ℚ) : ℝ)
        = ((794329/10000000 : ℚ) : ℝ) * ((-966931/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos581o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum581o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((715267/10000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_11).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw500lo : ((333/2000000 : ℚ) : ℝ) ≤ ((500:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_500_14).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((370735227/200000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum581o2_500
    have hx1 : ((715267/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((333/2000000 : ℚ) : ℝ)
          * (((1113319/100000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos581o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/581 + 1/2)
      ≤ ((1343/1250000 : ℚ) : ℝ) * (1000/581 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_500_11).2
    have hexp : (-((((11:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(11/10) : ℝ) := by
      norm_num
    have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (500 : ℝ) ^ (-σ - 2) ≤ ((1/10000000 : ℚ) : ℝ) := by
    have hbr := (wbr_500_31).2
    have hexp : (-((((31:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(31/10) : ℝ) := by
      norm_num
    have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (500 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((11/5000000 : ℚ) : ℝ) / (21/10) := by
    have hnum : (500 : ℝ) ^ (-σ - 1) ≤ ((11/5000000 : ℚ) : ℝ) := by
      have hbr := (wbr_500_21).2
      have hexp : (-((((21:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(21/10) : ℝ) := by
        norm_num
      have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos581o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos581o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos581o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos581o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos581o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos581o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos581o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos581o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos581o2c 10) := by
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

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
theorem seg581o2_interval_6 {σ : ℝ} (ha : (7/5:ℝ) ≤ σ) (hb : σ ≤ (17/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((581:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta581o2_lower h1 h2
  have hc2 : ((478013/500000 : ℚ) : ℝ) ≤ cos581o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 2 - ((478063/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1471257570193/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos581o2c 2 := by
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
    calc ((1471257570193/5000000000000 : ℚ) : ℝ)
        = ((3077861/10000000 : ℚ) : ℝ) * ((478013/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((67911/250000 : ℚ) : ℝ) ≤ cos581o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 3 - ((4246/15625 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((26228518509/625000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos581o2c 3 := by
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
    calc ((26228518509/625000000000 : ℚ) : ℝ)
        = ((386219/2500000 : ℚ) : ℝ) * ((67911/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((165649/200000 : ℚ) : ℝ) ≤ cos581o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 4 - ((165669/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((78461470989/1000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos581o2c 4 := by
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
    calc ((78461470989/1000000000000 : ℚ) : ℝ)
        = ((473661/5000000 : ℚ) : ℝ) * ((165649/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-424847/500000 : ℚ) : ℝ) ≤ cos581o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 5 - ((-424797/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-111587339091/1250000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos581o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((262653/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-111587339091/1250000000000 : ℚ) : ℝ)
        = ((262653/2500000 : ℚ) : ℝ) * ((-424847/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((108333/200000 : ℚ) : ℝ) ≤ cos581o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 6 - ((108353/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((51511366503/2000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos581o2c 6 := by
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
    calc ((51511366503/2000000000000 : ℚ) : ℝ)
        = ((475491/10000000 : ℚ) : ℝ) * ((108333/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((98001/100000 : ℚ) : ℝ) ≤ cos581o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 7 - ((98011/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((286848927/8000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos581o2c 7 := by
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
    calc ((286848927/8000000000 : ℚ) : ℝ)
        = ((2927/80000 : ℚ) : ℝ) * ((98001/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((156943/250000 : ℚ) : ℝ) ≤ cos581o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 8 - ((19621/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((11440046099/625000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos581o2c 8 := by
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
    calc ((11440046099/625000000000 : ℚ) : ℝ)
        = ((72893/2500000 : ℚ) : ℝ) * ((156943/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((-852403/1000000 : ℚ) : ℝ) ≤ cos581o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 9 - ((-852303/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((-196641700473/5000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos581o2c 9 := by
    have hw : ((9:ℕ) : ℝ) ^ (-σ) ≤ ((230691/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_9_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc9).2
      (by push_cast; norm_num)
    calc ((-196641700473/5000000000000 : ℚ) : ℝ)
        = ((230691/5000000 : ℚ) : ℝ) * ((-852403/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-966931/1000000 : ℚ) : ℝ) ≤ cos581o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 10 - ((-966831/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-96235741637/2500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos581o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((99527/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-96235741637/2500000000000 : ℚ) : ℝ)
        = ((99527/2500000 : ℚ) : ℝ) * ((-966931/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos581o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum581o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((174189/5000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_14).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw500lo : ((129/5000000 : ℚ) : ℝ) ≤ ((500:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_500_17).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((143618151/500000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum581o2_500
    have hx1 : ((174189/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((129/5000000 : ℚ) : ℝ)
          * (((1113319/100000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos581o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/581 + 1/2)
      ≤ ((833/5000000 : ℚ) : ℝ) * (1000/581 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_500_14).2
    have hexp : (-((((14:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(14/10) : ℝ) := by
      norm_num
    have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (500 : ℝ) ^ (-σ - 2) ≤ ((1/10000000 : ℚ) : ℝ) := by
    have hbr := (wbr_500_34).2
    have hexp : (-((((34:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(34/10) : ℝ) := by
      norm_num
    have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (500 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((1/2500000 : ℚ) : ℝ) / (12/5) := by
    have hnum : (500 : ℝ) ^ (-σ - 1) ≤ ((1/2500000 : ℚ) : ℝ) := by
      have hbr := (wbr_500_24).2
      have hexp : (-((((24:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(24/10) : ℝ) := by
        norm_num
      have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos581o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos581o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos581o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos581o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos581o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos581o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos581o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos581o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos581o2c 10) := by
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

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
theorem seg581o2_interval_7 {σ : ℝ} (ha : (17/10:ℝ) ≤ σ) (hb : σ ≤ (2:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((581:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta581o2_lower h1 h2
  have hc2 : ((478013/500000 : ℚ) : ℝ) ≤ cos581o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 2 - ((478063/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((478013/2000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos581o2c 2 := by
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
    calc ((478013/2000000 : ℚ) : ℝ)
        = ((1/4 : ℚ) : ℝ) * ((478013/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((67911/250000 : ℚ) : ℝ) ≤ cos581o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 3 - ((4246/15625 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((75456659121/2500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos581o2c 3 := by
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
    calc ((75456659121/2500000000000 : ℚ) : ℝ)
        = ((1111111/10000000 : ℚ) : ℝ) * ((67911/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((165649/200000 : ℚ) : ℝ) ≤ cos581o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 4 - ((165669/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((165649/3200000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos581o2c 4 := by
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
    calc ((165649/3200000 : ℚ) : ℝ)
        = ((1/16 : ℚ) : ℝ) * ((165649/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-424847/500000 : ℚ) : ℝ) ≤ cos581o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 5 - ((-424797/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-275412590761/5000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos581o2c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((648263/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-275412590761/5000000000000 : ℚ) : ℝ)
        = ((648263/10000000 : ℚ) : ℝ) * ((-424847/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((108333/200000 : ℚ) : ℝ) ≤ cos581o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 6 - ((108353/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((30092415741/2000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos581o2c 6 := by
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
    calc ((30092415741/2000000000000 : ℚ) : ℝ)
        = ((277777/10000000 : ℚ) : ℝ) * ((108333/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((98001/100000 : ℚ) : ℝ) ≤ cos581o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 7 - ((98011/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((20000142081/1000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos581o2c 7 := by
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
    calc ((20000142081/1000000000000 : ℚ) : ℝ)
        = ((204081/10000000 : ℚ) : ℝ) * ((98001/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((156943/250000 : ℚ) : ℝ) ≤ cos581o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 8 - ((19621/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((156943/16000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos581o2c 8 := by
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
    calc ((156943/16000000 : ℚ) : ℝ)
        = ((1/64 : ℚ) : ℝ) * ((156943/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((-852403/1000000 : ℚ) : ℝ) ≤ cos581o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 9 - ((-852303/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((-40687752399/2000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos581o2c 9 := by
    have hw : ((9:ℕ) : ℝ) ^ (-σ) ≤ ((47733/2000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_9_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc9).2
      (by push_cast; norm_num)
    calc ((-40687752399/2000000000000 : ℚ) : ℝ)
        = ((47733/2000000 : ℚ) : ℝ) * ((-852403/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-966931/1000000 : ℚ) : ℝ) ≤ cos581o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 10 - ((-966831/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos581o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-192928841637/10000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos581o2c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((199527/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-192928841637/10000000000000 : ℚ) : ℝ)
        = ((199527/10000000 : ℚ) : ℝ) * ((-966931/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos581o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum581o2_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((169681/10000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_17).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw500lo : ((1/250000 : ℚ) : ℝ) ≤ ((500:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_500_20).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((1113319/25000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum581o2_500
    have hx1 : ((169681/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((1/250000 : ℚ) : ℝ)
          * (((1113319/100000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos581o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/581 + 1/2)
      ≤ ((259/10000000 : ℚ) : ℝ) * (1000/581 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_500_17).2
    have hexp : (-((((17:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(17/10) : ℝ) := by
      norm_num
    have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (500 : ℝ) ^ (-σ - 2) ≤ ((1/10000000 : ℚ) : ℝ) := by
    have hbr := (wbr_500_37).2
    have hexp : (-((((37:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(37/10) : ℝ) := by
      norm_num
    have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (500 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((1/10000000 : ℚ) : ℝ) / (27/10) := by
    have hnum : (500 : ℝ) ^ (-σ - 1) ≤ ((1/10000000 : ℚ) : ℝ) := by
      have hbr := (wbr_500_27).2
      have hexp : (-((((27:ℕ)) : ℝ) / ((((10:ℕ))) : ℝ))) = (-(27/10) : ℝ) := by
        norm_num
      have hbase : (((500:ℕ)) : ℝ) = (500 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos581o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos581o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos581o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos581o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos581o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos581o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos581o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos581o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos581o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos581o2c 10) := by
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

set_option maxRecDepth 16384 in
/-- **Segment positivity at the half-integer anchor 581/2.** -/
theorem segment581o2_re_pos {σ : ℝ} (h1 : (1/2:ℝ) ≤ σ) (h2 : σ ≤ 2) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((581:ℕ)):ℝ)/2) * Complex.I)).re := by
  rcases le_total σ (3/5 : ℝ) with hc | hc
  · exact seg581o2_interval_1 h1 hc
  rcases le_total σ (7/10 : ℝ) with hc2 | hc2
  · exact seg581o2_interval_2 hc hc2
  rcases le_total σ (9/10 : ℝ) with hc3 | hc3
  · exact seg581o2_interval_3 hc2 hc3
  rcases le_total σ (11/10 : ℝ) with hc4 | hc4
  · exact seg581o2_interval_4 hc3 hc4
  rcases le_total σ (7/5 : ℝ) with hc5 | hc5
  · exact seg581o2_interval_5 hc4 hc5
  rcases le_total σ (17/10 : ℝ) with hc6 | hc6
  · exact seg581o2_interval_6 hc5 hc6
  exact seg581o2_interval_7 hc6 h2

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.segment581o2_re_pos
end AxiomAudit
