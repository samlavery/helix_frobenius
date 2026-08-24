import RequestProject.DVPSegment834o2Core
import RequestProject.DVPWeights289o2
import RequestProject.DVPWeights581o2
import RequestProject.DVPWeights63
import RequestProject.DVPWeights74
import RequestProject.DVPWeights81

/-!
# Segment positivity at `t = 834/2`: rung-417 (seven σ-intervals, N = 500)
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
theorem seg834o2_interval_1 {σ : ℝ} (ha : (1/2:ℝ) ≤ σ) (hb : σ ≤ (3/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((834:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta834o2_lower h1 h2
  have hc2 : ((39991/40000 : ℚ) : ℝ) ≤ cos834o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 2 - ((7999/8000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((263842182149/400000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos834o2c 2 := by
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
    calc ((263842182149/400000000000 : ℚ) : ℝ)
        = ((6597539/10000000 : ℚ) : ℝ) * ((39991/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((851787/1000000 : ℚ) : ℝ) ≤ cos834o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 3 - ((851887/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((2203069562883/5000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos834o2c 3 := by
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
    calc ((2203069562883/5000000000000 : ℚ) : ℝ)
        = ((2586409/5000000 : ℚ) : ℝ) * ((851787/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((499699/500000 : ℚ) : ℝ) ≤ cos834o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 4 - ((499749/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((135941613853/312500000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos834o2c 4 := by
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
    calc ((135941613853/312500000000 : ℚ) : ℝ)
        = ((272047/625000 : ℚ) : ℝ) * ((499699/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((12327/31250 : ℚ) : ℝ) ≤ cos834o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 5 - ((98641/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((46932673389/312500000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos834o2c 5 := by
    have hwlo : ((3807307/10000000 : ℚ) : ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_5_6).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((5:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((3807307/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc5).1
      (by push_cast; norm_num)
    calc ((46932673389/312500000000 : ℚ) : ℝ)
        = ((3807307/10000000 : ℚ) : ℝ) * ((12327/31250 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((171997/200000 : ℚ) : ℝ) ≤ cos834o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 6 - ((172017/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((586989125639/2000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos834o2c 6 := by
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
    calc ((586989125639/2000000000000 : ℚ) : ℝ)
        = ((3412787/10000000 : ℚ) : ℝ) * ((171997/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((610777/1000000 : ℚ) : ℝ) ≤ cos834o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 7 - ((610877/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((950153407719/5000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos834o2c 7 := by
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
    calc ((950153407719/5000000000000 : ℚ) : ℝ)
        = ((1555647/5000000 : ℚ) : ℝ) * ((610777/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((99877/100000 : ℚ) : ℝ) ≤ cos834o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 8 - ((99887/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((57364255073/200000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos834o2c 8 := by
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
    calc ((57364255073/200000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((99877/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((22567/50000 : ℚ) : ℝ) ≤ cos834o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 9 - ((5643/12500 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((12076978287/100000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos834o2c 9 := by
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
    calc ((12076978287/100000000000 : ℚ) : ℝ)
        = ((535161/2000000 : ℚ) : ℝ) * ((22567/50000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((102237/250000 : ℚ) : ℝ) ≤ cos834o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 10 - ((51131/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((128403844491/1250000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos834o2c 10 := by
    have hwlo : ((1255943/5000000 : ℚ) : ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_10_6).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((10:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((1255943/5000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc10).1
      (by push_cast; norm_num)
    calc ((128403844491/1250000000000 : ℚ) : ℝ)
        = ((1255943/5000000 : ℚ) : ℝ) * ((102237/250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos834o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum834o2_floor
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
  have htail : ((5328025687/12500000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum834o2_500
    have hx1 : ((1507557/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((7507/312500 : ℚ) : ℝ)
          * (((709741/40000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos834o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/834 + 1/2)
      ≤ ((223607/5000000 : ℚ) : ℝ) * (1000/834 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos834o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos834o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos834o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos834o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos834o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos834o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos834o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos834o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos834o2c 10) := by
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
theorem seg834o2_interval_2 {σ : ℝ} (ha : (3/5:ℝ) ≤ σ) (hb : σ ≤ (7/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((834:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta834o2_lower h1 h2
  have hc2 : ((39991/40000 : ℚ) : ℝ) ≤ cos834o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 2 - ((7999/8000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((123086739251/200000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos834o2c 2 := by
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
    calc ((123086739251/200000000000 : ℚ) : ℝ)
        = ((3077861/5000000 : ℚ) : ℝ) * ((39991/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((851787/1000000 : ℚ) : ℝ) ≤ cos834o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 3 - ((851887/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((394771758381/1000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos834o2c 3 := by
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
    calc ((394771758381/1000000000000 : ℚ) : ℝ)
        = ((463463/1000000 : ℚ) : ℝ) * ((851787/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((499699/500000 : ℚ) : ℝ) ≤ cos834o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 4 - ((499749/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((1893504923409/5000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos834o2c 4 := by
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
    calc ((1893504923409/5000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((499699/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((12327/31250 : ℚ) : ℝ) ≤ cos834o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 5 - ((98641/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((39955665351/312500000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos834o2c 5 := by
    have hwlo : ((3241313/10000000 : ℚ) : ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_5_7).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((5:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((3241313/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc5).1
      (by push_cast; norm_num)
    calc ((39955665351/312500000000 : ℚ) : ℝ)
        = ((3241313/10000000 : ℚ) : ℝ) * ((12327/31250 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((171997/200000 : ℚ) : ℝ) ≤ cos834o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 6 - ((172017/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((490698669153/2000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos834o2c 6 := by
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
    calc ((490698669153/2000000000000 : ℚ) : ℝ)
        = ((2852949/10000000 : ℚ) : ℝ) * ((171997/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((610777/1000000 : ℚ) : ℝ) ≤ cos834o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 7 - ((610877/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((195534759557/1250000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos834o2c 7 := by
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
    calc ((195534759557/1250000000000 : ℚ) : ℝ)
        = ((320141/1250000 : ℚ) : ℝ) * ((610777/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((99877/100000 : ℚ) : ℝ) ≤ cos834o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 8 - ((99887/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((116485646207/500000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos834o2c 8 := by
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
    calc ((116485646207/500000000000 : ℚ) : ℝ)
        = ((1166291/5000000 : ℚ) : ℝ) * ((99877/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((22567/50000 : ℚ) : ℝ) ≤ cos834o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 9 - ((5643/12500 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((2423673233/25000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos834o2c 9 := by
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
    calc ((2423673233/25000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((22567/50000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((102237/250000 : ℚ) : ℝ) ≤ cos834o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 10 - ((51131/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((101994800547/1250000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos834o2c 10 := by
    have hwlo : ((997631/5000000 : ℚ) : ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_10_7).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((10:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((997631/5000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc10).1
      (by push_cast; norm_num)
    calc ((101994800547/1250000000000 : ℚ) : ℝ)
        = ((997631/5000000 : ℚ) : ℝ) * ((102237/250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos834o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum834o2_floor
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
  have htail : ((91584268899/400000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum834o2_500
    have hx1 : ((148267/625000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((129039/10000000 : ℚ) : ℝ)
          * (((709741/40000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos834o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/834 + 1/2)
      ≤ ((9609/400000 : ℚ) : ℝ) * (1000/834 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos834o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos834o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos834o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos834o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos834o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos834o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos834o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos834o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos834o2c 10) := by
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
theorem seg834o2_interval_3 {σ : ℝ} (ha : (7/10:ℝ) ≤ σ) (hb : σ ≤ (9/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((834:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta834o2_lower h1 h2
  have hc2 : ((39991/40000 : ℚ) : ℝ) ≤ cos834o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 2 - ((7999/8000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((214306450197/400000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos834o2c 2 := by
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
    calc ((214306450197/400000000000 : ℚ) : ℝ)
        = ((5358867/10000000 : ℚ) : ℝ) * ((39991/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((851787/1000000 : ℚ) : ℝ) ≤ cos834o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 3 - ((851887/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((316899687267/1000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos834o2c 3 := by
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
    calc ((316899687267/1000000000000 : ℚ) : ℝ)
        = ((372041/1000000 : ℚ) : ℝ) * ((851787/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((499699/500000 : ℚ) : ℝ) ≤ cos834o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 4 - ((499749/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((287001620951/1000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos834o2c 4 := by
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
    calc ((287001620951/1000000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((499699/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((12327/31250 : ℚ) : ℝ) ≤ cos834o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 5 - ((98641/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((28959044499/312500000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos834o2c 5 := by
    have hwlo : ((2349237/10000000 : ℚ) : ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_5_9).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((5:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((2349237/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc5).1
      (by push_cast; norm_num)
    calc ((28959044499/312500000000 : ℚ) : ℝ)
        = ((2349237/10000000 : ℚ) : ℝ) * ((12327/31250 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((171997/200000 : ℚ) : ℝ) ≤ cos834o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 6 - ((172017/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((171456757423/1000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos834o2c 6 := by
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
    calc ((171456757423/1000000000000 : ℚ) : ℝ)
        = ((996859/5000000 : ℚ) : ℝ) * ((171997/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((610777/1000000 : ℚ) : ℝ) ≤ cos834o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 7 - ((610877/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((132496465387/1250000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos834o2c 7 := by
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
    calc ((132496465387/1250000000000 : ℚ) : ℝ)
        = ((216931/1250000 : ℚ) : ℝ) * ((610777/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((99877/100000 : ℚ) : ℝ) ≤ cos834o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 8 - ((99887/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((15370371161/100000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos834o2c 8 := by
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
    calc ((15370371161/100000000000 : ℚ) : ℝ)
        = ((153893/1000000 : ℚ) : ℝ) * ((99877/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((22567/50000 : ℚ) : ℝ) ≤ cos834o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 9 - ((5643/12500 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((6247200043/100000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos834o2c 9 := by
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
    calc ((6247200043/100000000000 : ℚ) : ℝ)
        = ((276829/2000000 : ℚ) : ℝ) * ((22567/50000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((102237/250000 : ℚ) : ℝ) ≤ cos834o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 10 - ((51131/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((5148348609/100000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos834o2c 10 := by
    have hwlo : ((50357/400000 : ℚ) : ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_10_9).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((10:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((50357/400000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc10).1
      (by push_cast; norm_num)
    calc ((5148348609/100000000000 : ℚ) : ℝ)
        = ((50357/400000 : ℚ) : ℝ) * ((102237/250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos834o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum834o2_floor
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
  have htail : ((1651567307/25000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum834o2_500
    have hx1 : ((233311/1250000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((2327/625000 : ℚ) : ℝ)
          * (((709741/40000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos834o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/834 + 1/2)
      ≤ ((1613/125000 : ℚ) : ℝ) * (1000/834 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos834o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos834o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos834o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos834o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos834o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos834o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos834o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos834o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos834o2c 10) := by
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
theorem seg834o2_interval_4 {σ : ℝ} (ha : (9/10:ℝ) ≤ σ) (hb : σ ≤ (11/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((834:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta834o2_lower h1 h2
  have hc2 : ((39991/40000 : ℚ) : ℝ) ≤ cos834o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 2 - ((7999/8000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((46641143381/100000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos834o2c 2 := by
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
    calc ((46641143381/100000000000 : ℚ) : ℝ)
        = ((1166291/2500000 : ℚ) : ℝ) * ((39991/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((851787/1000000 : ℚ) : ℝ) ≤ cos834o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 3 - ((851887/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((79496428923/312500000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos834o2c 3 := by
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
    calc ((79496428923/312500000000 : ℚ) : ℝ)
        = ((93329/312500 : ℚ) : ℝ) * ((851787/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((499699/500000 : ℚ) : ℝ) ≤ cos834o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 4 - ((499749/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((135941613853/625000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos834o2c 4 := by
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
    calc ((135941613853/625000000000 : ℚ) : ℝ)
        = ((272047/1250000 : ℚ) : ℝ) * ((499699/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((12327/31250 : ℚ) : ℝ) ≤ cos834o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 5 - ((98641/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((20988924033/312500000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos834o2c 5 := by
    have hwlo : ((1702679/10000000 : ℚ) : ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_5_11).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((5:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((1702679/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc5).1
      (by push_cast; norm_num)
    calc ((20988924033/312500000000 : ℚ) : ℝ)
        = ((1702679/10000000 : ℚ) : ℝ) * ((12327/31250 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((171997/200000 : ℚ) : ℝ) ≤ cos834o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 6 - ((172017/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((14977326763/125000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos834o2c 6 := by
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
    calc ((14977326763/125000000000 : ℚ) : ℝ)
        = ((87079/625000 : ℚ) : ℝ) * ((171997/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((610777/1000000 : ℚ) : ℝ) ≤ cos834o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 7 - ((610877/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((359124049683/5000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos834o2c 7 := by
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
    calc ((359124049683/5000000000000 : ℚ) : ℝ)
        = ((587979/5000000 : ℚ) : ℝ) * ((610777/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((99877/100000 : ℚ) : ℝ) ≤ cos834o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 8 - ((99887/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((20281323251/200000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos834o2c 8 := by
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
    calc ((20281323251/200000000000 : ℚ) : ℝ)
        = ((203063/2000000 : ℚ) : ℝ) * ((99877/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((22567/50000 : ℚ) : ℝ) ≤ cos834o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 9 - ((5643/12500 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((4025659429/100000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos834o2c 9 := by
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
    calc ((4025659429/100000000000 : ℚ) : ℝ)
        = ((178387/2000000 : ℚ) : ℝ) * ((22567/50000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((102237/250000 : ℚ) : ℝ) ≤ cos834o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 10 - ((51131/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((10151213967/312500000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos834o2c 10 := by
    have hwlo : ((99291/1250000 : ℚ) : ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_10_11).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((10:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((99291/1250000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc10).1
      (by push_cast; norm_num)
    calc ((10151213967/312500000000 : ℚ) : ℝ)
        = ((99291/1250000 : ℚ) : ℝ) * ((102237/250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos834o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum834o2_floor
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
  have htail : ((7624747563/400000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum834o2_500
    have hx1 : ((577719/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((10743/10000000 : ℚ) : ℝ)
          * (((709741/40000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos834o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/834 + 1/2)
      ≤ ((37233/10000000 : ℚ) : ℝ) * (1000/834 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos834o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos834o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos834o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos834o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos834o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos834o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos834o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos834o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos834o2c 10) := by
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
theorem seg834o2_interval_5 {σ : ℝ} (ha : (11/10:ℝ) ≤ σ) (hb : σ ≤ (7/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((834:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta834o2_lower h1 h2
  have hc2 : ((39991/40000 : ℚ) : ℝ) ≤ cos834o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 2 - ((7999/8000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((151537536381/400000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos834o2c 2 := by
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
    calc ((151537536381/400000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((39991/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((851787/1000000 : ℚ) : ℝ) ≤ cos834o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 3 - ((851887/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((91481072013/500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos834o2c 3 := by
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
    calc ((91481072013/500000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((851787/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((499699/500000 : ℚ) : ℝ) ≤ cos834o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 4 - ((499749/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((22421993829/156250000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos834o2c 4 := by
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
    calc ((22421993829/156250000000 : ℚ) : ℝ)
        = ((44871/312500 : ℚ) : ℝ) * ((499699/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((12327/31250 : ℚ) : ℝ) ≤ cos834o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 5 - ((98641/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((12950881797/312500000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos834o2c 5 := by
    have hwlo : ((1050611/10000000 : ℚ) : ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_5_14).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((5:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((1050611/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc5).1
      (by push_cast; norm_num)
    calc ((12950881797/312500000000 : ℚ) : ℝ)
        = ((1050611/10000000 : ℚ) : ℝ) * ((12327/31250 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((171997/200000 : ℚ) : ℝ) ≤ cos834o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 6 - ((172017/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((34998465551/500000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos834o2c 6 := by
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
    calc ((34998465551/500000000000 : ℚ) : ℝ)
        = ((203483/2500000 : ℚ) : ℝ) * ((171997/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((610777/1000000 : ℚ) : ℝ) ≤ cos834o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 7 - ((610877/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((400631233049/10000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos834o2c 7 := by
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
    calc ((400631233049/10000000000000 : ℚ) : ℝ)
        = ((655937/10000000 : ℚ) : ℝ) * ((610777/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((99877/100000 : ℚ) : ℝ) ≤ cos834o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 8 - ((99887/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((27171238219/500000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos834o2c 8 := by
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
    calc ((27171238219/500000000000 : ℚ) : ℝ)
        = ((272047/5000000 : ℚ) : ℝ) * ((99877/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((22567/50000 : ℚ) : ℝ) ≤ cos834o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 9 - ((5643/12500 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((10411985027/500000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos834o2c 9 := by
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
    calc ((10411985027/500000000000 : ℚ) : ℝ)
        = ((461381/10000000 : ℚ) : ℝ) * ((22567/50000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((102237/250000 : ℚ) : ℝ) ≤ cos834o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 10 - ((51131/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((40701265359/2500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos834o2c 10 := by
    have hwlo : ((398107/10000000 : ℚ) : ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_10_14).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((10:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((398107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc10).1
      (by push_cast; norm_num)
    calc ((40701265359/2500000000000 : ℚ) : ℝ)
        = ((398107/10000000 : ℚ) : ℝ) * ((102237/250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos834o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum834o2_floor
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
  have htail : ((236343753/80000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum834o2_500
    have hx1 : ((715267/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((333/2000000 : ℚ) : ℝ)
          * (((709741/40000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos834o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/834 + 1/2)
      ≤ ((1343/1250000 : ℚ) : ℝ) * (1000/834 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos834o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos834o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos834o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos834o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos834o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos834o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos834o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos834o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos834o2c 10) := by
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
theorem seg834o2_interval_6 {σ : ℝ} (ha : (7/5:ℝ) ≤ σ) (hb : σ ≤ (17/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((834:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta834o2_lower h1 h2
  have hc2 : ((39991/40000 : ℚ) : ℝ) ≤ cos834o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 2 - ((7999/8000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((123086739251/400000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos834o2c 2 := by
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
    calc ((123086739251/400000000000 : ℚ) : ℝ)
        = ((3077861/10000000 : ℚ) : ℝ) * ((39991/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((851787/1000000 : ℚ) : ℝ) ≤ cos834o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 3 - ((851887/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((328976323353/2500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos834o2c 3 := by
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
    calc ((328976323353/2500000000000 : ℚ) : ℝ)
        = ((386219/2500000 : ℚ) : ℝ) * ((851787/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((499699/500000 : ℚ) : ℝ) ≤ cos834o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 4 - ((499749/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((236687928039/2500000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos834o2c 4 := by
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
    calc ((236687928039/2500000000000 : ℚ) : ℝ)
        = ((473661/5000000 : ℚ) : ℝ) * ((499699/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((12327/31250 : ℚ) : ℝ) ≤ cos834o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 5 - ((98641/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((3995562837/156250000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos834o2c 5 := by
    have hwlo : ((324131/5000000 : ℚ) : ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_5_17).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((5:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((324131/5000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc5).1
      (by push_cast; norm_num)
    calc ((3995562837/156250000000 : ℚ) : ℝ)
        = ((324131/5000000 : ℚ) : ℝ) * ((12327/31250 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((171997/200000 : ℚ) : ℝ) ≤ cos834o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 6 - ((172017/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((81783025527/2000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos834o2c 6 := by
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
    calc ((81783025527/2000000000000 : ℚ) : ℝ)
        = ((475491/10000000 : ℚ) : ℝ) * ((171997/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((610777/1000000 : ℚ) : ℝ) ≤ cos834o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 7 - ((610877/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((1787744279/80000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos834o2c 7 := by
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
    calc ((1787744279/80000000000 : ℚ) : ℝ)
        = ((2927/80000 : ℚ) : ℝ) * ((610777/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((99877/100000 : ℚ) : ℝ) ≤ cos834o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 8 - ((99887/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((7280334161/250000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos834o2c 8 := by
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
    calc ((7280334161/250000000000 : ℚ) : ℝ)
        = ((72893/2500000 : ℚ) : ℝ) * ((99877/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((22567/50000 : ℚ) : ℝ) ≤ cos834o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 9 - ((5643/12500 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((673241311/62500000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos834o2c 9 := by
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
    calc ((673241311/62500000000 : ℚ) : ℝ)
        = ((29833/1250000 : ℚ) : ℝ) * ((22567/50000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((102237/250000 : ℚ) : ℝ) ≤ cos834o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 10 - ((51131/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((10199469831/1250000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos834o2c 10 := by
    have hwlo : ((99763/5000000 : ℚ) : ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_10_17).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((10:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((99763/5000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc10).1
      (by push_cast; norm_num)
    calc ((10199469831/1250000000000 : ℚ) : ℝ)
        = ((99763/5000000 : ℚ) : ℝ) * ((102237/250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos834o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum834o2_floor
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
  have htail : ((91556589/200000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum834o2_500
    have hx1 : ((174189/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((129/5000000 : ℚ) : ℝ)
          * (((709741/40000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos834o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/834 + 1/2)
      ≤ ((833/5000000 : ℚ) : ℝ) * (1000/834 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos834o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos834o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos834o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos834o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos834o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos834o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos834o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos834o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos834o2c 10) := by
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
theorem seg834o2_interval_7 {σ : ℝ} (ha : (17/10:ℝ) ≤ σ) (hb : σ ≤ (2:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((834:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta834o2_lower h1 h2
  have hc2 : ((39991/40000 : ℚ) : ℝ) ≤ cos834o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 2 - ((7999/8000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((39991/160000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos834o2c 2 := by
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
    calc ((39991/160000 : ℚ) : ℝ)
        = ((1/4 : ℚ) : ℝ) * ((39991/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((851787/1000000 : ℚ) : ℝ) ≤ cos834o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 3 - ((851887/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((946429905357/10000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos834o2c 3 := by
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
    calc ((946429905357/10000000000000 : ℚ) : ℝ)
        = ((1111111/10000000 : ℚ) : ℝ) * ((851787/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((499699/500000 : ℚ) : ℝ) ≤ cos834o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 4 - ((499749/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((499699/8000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos834o2c 4 := by
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
    calc ((499699/8000000 : ℚ) : ℝ)
        = ((1/16 : ℚ) : ℝ) * ((499699/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((12327/31250 : ℚ) : ℝ) ≤ cos834o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 5 - ((98641/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((12327/781250 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos834o2c 5 := by
    have hwlo : ((1/25 : ℚ) : ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_5_20).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((5:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((1/25 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc5).1
      (by push_cast; norm_num)
    calc ((12327/781250 : ℚ) : ℝ)
        = ((1/25 : ℚ) : ℝ) * ((12327/31250 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((171997/200000 : ℚ) : ℝ) ≤ cos834o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 6 - ((172017/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((47776810669/2000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos834o2c 6 := by
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
    calc ((47776810669/2000000000000 : ℚ) : ℝ)
        = ((277777/10000000 : ℚ) : ℝ) * ((171997/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((610777/1000000 : ℚ) : ℝ) ≤ cos834o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 7 - ((610877/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((124647980937/10000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos834o2c 7 := by
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
    calc ((124647980937/10000000000000 : ℚ) : ℝ)
        = ((204081/10000000 : ℚ) : ℝ) * ((610777/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((99877/100000 : ℚ) : ℝ) ≤ cos834o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 8 - ((99887/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((99877/6400000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos834o2c 8 := by
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
    calc ((99877/6400000 : ℚ) : ℝ)
        = ((1/64 : ℚ) : ℝ) * ((99877/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((22567/50000 : ℚ) : ℝ) ≤ cos834o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 9 - ((5643/12500 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((43531743/7812500000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos834o2c 9 := by
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
    calc ((43531743/7812500000 : ℚ) : ℝ)
        = ((1929/156250 : ℚ) : ℝ) * ((22567/50000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((102237/250000 : ℚ) : ℝ) ≤ cos834o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 10 - ((51131/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos834o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((10223597763/2500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos834o2c 10 := by
    have hwlo : ((99999/10000000 : ℚ) : ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := by
      refine le_trans (wbr_10_20).1 ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hwhi : ((10:ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((99999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
    have hkey := (mul_lower_of_bracket hwlo hwhi hq0 hc10).1
      (by push_cast; norm_num)
    calc ((10223597763/2500000000000 : ℚ) : ℝ)
        = ((99999/10000000 : ℚ) : ℝ) * ((102237/250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos834o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum834o2_floor
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
  have htail : ((709741/10000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum834o2_500
    have hx1 : ((169681/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((1/250000 : ℚ) : ℝ)
          * (((709741/40000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos834o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/834 + 1/2)
      ≤ ((259/10000000 : ℚ) : ℝ) * (1000/834 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos834o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos834o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos834o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos834o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos834o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos834o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos834o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos834o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos834o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos834o2c 10) := by
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
/-- **Segment positivity at the anchor 834/2.** -/
theorem segment834o2_re_pos {σ : ℝ} (h1 : (1/2:ℝ) ≤ σ) (h2 : σ ≤ 2) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((834:ℕ)):ℝ)/2) * Complex.I)).re := by
  rcases le_total σ (3/5 : ℝ) with hc | hc
  · exact seg834o2_interval_1 h1 hc
  rcases le_total σ (7/10 : ℝ) with hc2 | hc2
  · exact seg834o2_interval_2 hc hc2
  rcases le_total σ (9/10 : ℝ) with hc3 | hc3
  · exact seg834o2_interval_3 hc2 hc3
  rcases le_total σ (11/10 : ℝ) with hc4 | hc4
  · exact seg834o2_interval_4 hc3 hc4
  rcases le_total σ (7/5 : ℝ) with hc5 | hc5
  · exact seg834o2_interval_5 hc4 hc5
  rcases le_total σ (17/10 : ℝ) with hc6 | hc6
  · exact seg834o2_interval_6 hc5 hc6
  exact seg834o2_interval_7 hc6 h2

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.segment834o2_re_pos
end AxiomAudit
