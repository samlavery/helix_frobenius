import RequestProject.DVPSegment618o2Core
import RequestProject.DVPWeights289o2
import RequestProject.DVPWeights581o2
import RequestProject.DVPWeights63
import RequestProject.DVPWeights74
import RequestProject.DVPWeights81

/-!
# Segment positivity at `t = 618/2`: rung-309 (seven σ-intervals, N = 500)
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
theorem seg618o2_interval_1 {σ : ℝ} (ha : (1/2:ℝ) ≤ σ) (hb : σ ≤ (3/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((618:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta618o2_lower h1 h2
  have hc2 : ((425119/500000 : ℚ) : ℝ) ≤ cos618o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 2 - ((425169/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((2804739182141/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos618o2c 2 := by
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
    calc ((2804739182141/5000000000000 : ℚ) : ℝ)
        = ((6597539/10000000 : ℚ) : ℝ) * ((425119/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((98389/100000 : ℚ) : ℝ) ≤ cos618o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 3 - ((98399/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((254474195101/500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos618o2c 3 := by
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
    calc ((254474195101/500000000000 : ℚ) : ℝ)
        = ((2586409/5000000 : ℚ) : ℝ) * ((98389/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((111509/250000 : ℚ) : ℝ) ≤ cos618o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 4 - ((55767/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((30335688923/156250000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos618o2c 4 := by
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
    calc ((30335688923/156250000000 : ℚ) : ℝ)
        = ((272047/625000 : ℚ) : ℝ) * ((111509/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((73237/125000 : ℚ) : ℝ) ≤ cos618o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 5 - ((146499/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((278835742759/1250000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos618o2c 5 := by
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
    calc ((278835742759/1250000000000 : ℚ) : ℝ)
        = ((3807307/10000000 : ℚ) : ℝ) * ((73237/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((742827/1000000 : ℚ) : ℝ) ≤ cos618o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 6 - ((742927/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((2535110328849/10000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos618o2c 6 := by
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
    calc ((2535110328849/10000000000000 : ℚ) : ℝ)
        = ((3412787/10000000 : ℚ) : ℝ) * ((742827/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-322967/1000000 : ℚ) : ℝ) ≤ cos618o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 7 - ((-322867/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-244140121343/2000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos618o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((755929/2000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-244140121343/2000000000000 : ℚ) : ℝ)
        = ((755929/2000000 : ℚ) : ℝ) * ((-322967/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-91713/1000000 : ℚ) : ℝ) ≤ cos618o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 8 - ((-91613/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-162127214871/5000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos618o2c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((1767767/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-162127214871/5000000000000 : ℚ) : ℝ)
        = ((1767767/5000000 : ℚ) : ℝ) * ((-91713/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((936369/1000000 : ℚ) : ℝ) ≤ cos618o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 9 - ((936469/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((501108170409/2000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos618o2c 9 := by
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
    calc ((501108170409/2000000000000 : ℚ) : ℝ)
        = ((535161/2000000 : ℚ) : ℝ) * ((936369/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((71793/1000000 : ℚ) : ℝ) ≤ cos618o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 10 - ((71893/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((90167915799/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos618o2c 10 := by
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
    calc ((90167915799/5000000000000 : ℚ) : ℝ)
        = ((1255943/5000000 : ℚ) : ℝ) * ((71793/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos618o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum618o2_floor
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
  have htail : ((1544918079/62500000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum618o2_500
    have hx1 : ((1507557/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((7507/312500 : ℚ) : ℝ)
          * (((205797/200000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos618o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/618 + 1/2)
      ≤ ((223607/5000000 : ℚ) : ℝ) * (1000/618 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos618o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos618o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos618o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos618o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos618o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos618o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos618o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos618o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos618o2c 10) := by
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
theorem seg618o2_interval_2 {σ : ℝ} (ha : (3/5:ℝ) ≤ σ) (hb : σ ≤ (7/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((618:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta618o2_lower h1 h2
  have hc2 : ((425119/500000 : ℚ) : ℝ) ≤ cos618o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 2 - ((425169/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1308457190459/2500000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos618o2c 2 := by
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
    calc ((1308457190459/2500000000000 : ℚ) : ℝ)
        = ((3077861/5000000 : ℚ) : ℝ) * ((425119/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((98389/100000 : ℚ) : ℝ) ≤ cos618o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 3 - ((98399/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((45599661107/100000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos618o2c 3 := by
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
    calc ((45599661107/100000000000 : ℚ) : ℝ)
        = ((463463/1000000 : ℚ) : ℝ) * ((98389/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((111509/250000 : ℚ) : ℝ) ≤ cos618o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 4 - ((55767/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((422540050119/2500000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos618o2c 4 := by
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
    calc ((422540050119/2500000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((111509/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((73237/125000 : ℚ) : ℝ) ≤ cos618o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 5 - ((146499/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((237384040181/1250000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos618o2c 5 := by
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
    calc ((237384040181/1250000000000 : ℚ) : ℝ)
        = ((3241313/10000000 : ℚ) : ℝ) * ((73237/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((742827/1000000 : ℚ) : ℝ) ≤ cos618o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 6 - ((742927/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((2119247546823/10000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos618o2c 6 := by
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
    calc ((2119247546823/10000000000000 : ℚ) : ℝ)
        = ((2852949/10000000 : ℚ) : ℝ) * ((742827/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-322967/1000000 : ℚ) : ℝ) ≤ cos618o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 7 - ((-322867/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-200969122453/2000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos618o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((622259/2000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_6).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-200969122453/2000000000000 : ℚ) : ℝ)
        = ((622259/2000000 : ℚ) : ℝ) * ((-322967/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-91713/1000000 : ℚ) : ℝ) ≤ cos618o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 8 - ((-91613/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-131688220449/5000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos618o2c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((1435873/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_6).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-131688220449/5000000000000 : ℚ) : ℝ)
        = ((1435873/5000000 : ℚ) : ℝ) * ((-91713/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((936369/1000000 : ℚ) : ℝ) ≤ cos618o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 9 - ((936469/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((100565094231/500000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos618o2c 9 := by
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
    calc ((100565094231/500000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((936369/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((71793/1000000 : ℚ) : ℝ) ≤ cos618o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 10 - ((71893/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((71622922383/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos618o2c 10 := by
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
    calc ((71622922383/5000000000000 : ℚ) : ℝ)
        = ((997631/5000000 : ℚ) : ℝ) * ((71793/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos618o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum618o2_floor
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
  have htail : ((26555839083/2000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum618o2_500
    have hx1 : ((148267/625000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((129039/10000000 : ℚ) : ℝ)
          * (((205797/200000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos618o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/618 + 1/2)
      ≤ ((9609/400000 : ℚ) : ℝ) * (1000/618 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos618o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos618o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos618o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos618o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos618o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos618o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos618o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos618o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos618o2c 10) := by
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
theorem seg618o2_interval_3 {σ : ℝ} (ha : (7/10:ℝ) ≤ σ) (hb : σ ≤ (9/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((618:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta618o2_lower h1 h2
  have hc2 : ((425119/500000 : ℚ) : ℝ) ≤ cos618o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 2 - ((425169/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((2278156180173/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos618o2c 2 := by
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
    calc ((2278156180173/5000000000000 : ℚ) : ℝ)
        = ((5358867/10000000 : ℚ) : ℝ) * ((425119/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((98389/100000 : ℚ) : ℝ) ≤ cos618o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 3 - ((98399/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((36604741949/100000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos618o2c 3 := by
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
    calc ((36604741949/100000000000 : ℚ) : ℝ)
        = ((372041/1000000 : ℚ) : ℝ) * ((98389/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((111509/250000 : ℚ) : ℝ) ≤ cos618o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 4 - ((55767/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((64045082641/500000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos618o2c 4 := by
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
    calc ((64045082641/500000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((111509/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((73237/125000 : ℚ) : ℝ) ≤ cos618o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 5 - ((146499/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((172051070169/1250000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos618o2c 5 := by
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
    calc ((172051070169/1250000000000 : ℚ) : ℝ)
        = ((2349237/10000000 : ℚ) : ℝ) * ((73237/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((742827/1000000 : ℚ) : ℝ) ≤ cos618o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 6 - ((742927/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((740493780393/5000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos618o2c 6 := by
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
    calc ((740493780393/5000000000000 : ℚ) : ℝ)
        = ((996859/5000000 : ℚ) : ℝ) * ((742827/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-322967/1000000 : ℚ) : ℝ) ≤ cos618o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 7 - ((-322867/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-827160149743/10000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos618o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((2561129/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-827160149743/10000000000000 : ℚ) : ℝ)
        = ((2561129/10000000 : ℚ) : ℝ) * ((-322967/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-91713/1000000 : ℚ) : ℝ) ≤ cos618o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 8 - ((-91613/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-213928184679/10000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos618o2c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((2332583/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-213928184679/10000000000000 : ℚ) : ℝ)
        = ((2332583/10000000 : ℚ) : ℝ) * ((-91713/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((936369/1000000 : ℚ) : ℝ) ≤ cos618o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 9 - ((936469/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((259214093901/2000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos618o2c 9 := by
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
    calc ((259214093901/2000000000000 : ℚ) : ℝ)
        = ((276829/2000000 : ℚ) : ℝ) * ((936369/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((71793/1000000 : ℚ) : ℝ) ≤ cos618o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 10 - ((71893/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((3615280101/400000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos618o2c 10 := by
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
    calc ((3615280101/400000000000 : ℚ) : ℝ)
        = ((50357/400000 : ℚ) : ℝ) * ((71793/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos618o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum618o2_floor
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
  have htail : ((478889619/125000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum618o2_500
    have hx1 : ((233311/1250000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((2327/625000 : ℚ) : ℝ)
          * (((205797/200000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos618o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/618 + 1/2)
      ≤ ((1613/125000 : ℚ) : ℝ) * (1000/618 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos618o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos618o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos618o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos618o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos618o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos618o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos618o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos618o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos618o2c 10) := by
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
theorem seg618o2_interval_4 {σ : ℝ} (ha : (9/10:ℝ) ≤ σ) (hb : σ ≤ (11/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((618:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta618o2_lower h1 h2
  have hc2 : ((425119/500000 : ℚ) : ℝ) ≤ cos618o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 2 - ((425169/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((495812463629/1250000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos618o2c 2 := by
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
    calc ((495812463629/1250000000000 : ℚ) : ℝ)
        = ((1166291/2500000 : ℚ) : ℝ) * ((425119/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((98389/100000 : ℚ) : ℝ) ≤ cos618o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 3 - ((98399/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((9182546981/31250000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos618o2c 3 := by
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
    calc ((9182546981/31250000000 : ℚ) : ℝ)
        = ((93329/312500 : ℚ) : ℝ) * ((98389/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((111509/250000 : ℚ) : ℝ) ≤ cos618o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 4 - ((55767/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((30335688923/312500000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos618o2c 4 := by
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
    calc ((30335688923/312500000000 : ℚ) : ℝ)
        = ((272047/1250000 : ℚ) : ℝ) * ((111509/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((73237/125000 : ℚ) : ℝ) ≤ cos618o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 5 - ((146499/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((124699101923/1250000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos618o2c 5 := by
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
    calc ((124699101923/1250000000000 : ℚ) : ℝ)
        = ((1702679/10000000 : ℚ) : ℝ) * ((73237/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((742827/1000000 : ℚ) : ℝ) ≤ cos618o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 6 - ((742927/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((64684632333/625000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos618o2c 6 := by
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
    calc ((64684632333/625000000000 : ℚ) : ℝ)
        = ((87079/625000 : ℚ) : ℝ) * ((742827/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-322967/1000000 : ℚ) : ℝ) ≤ cos618o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 7 - ((-322867/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-560492757183/10000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos618o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((1735449/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-560492757183/10000000000000 : ℚ) : ℝ)
        = ((1735449/10000000 : ℚ) : ℝ) * ((-322967/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-91713/1000000 : ℚ) : ℝ) ≤ cos618o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 8 - ((-91613/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-141139978803/10000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos618o2c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((1538931/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-141139978803/10000000000000 : ℚ) : ℝ)
        = ((1538931/10000000 : ℚ) : ℝ) * ((-91713/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((936369/1000000 : ℚ) : ℝ) ≤ cos618o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 9 - ((936469/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((167036056803/2000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos618o2c 9 := by
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
    calc ((167036056803/2000000000000 : ℚ) : ℝ)
        = ((178387/2000000 : ℚ) : ℝ) * ((936369/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((71793/1000000 : ℚ) : ℝ) ≤ cos618o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 10 - ((71893/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((7128398763/1250000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos618o2c 10 := by
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
    calc ((7128398763/1250000000000 : ℚ) : ℝ)
        = ((99291/1250000 : ℚ) : ℝ) * ((71793/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos618o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum618o2_floor
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
  have htail : ((2210877171/2000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum618o2_500
    have hx1 : ((577719/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((10743/10000000 : ℚ) : ℝ)
          * (((205797/200000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos618o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/618 + 1/2)
      ≤ ((37233/10000000 : ℚ) : ℝ) * (1000/618 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos618o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos618o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos618o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos618o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos618o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos618o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos618o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos618o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos618o2c 10) := by
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
theorem seg618o2_interval_5 {σ : ℝ} (ha : (11/10:ℝ) ≤ σ) (hb : σ ≤ (7/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((618:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta618o2_lower h1 h2
  have hc2 : ((425119/500000 : ℚ) : ℝ) ≤ cos618o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 2 - ((425169/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1610899600629/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos618o2c 2 := by
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
    calc ((1610899600629/5000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((425119/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((98389/100000 : ℚ) : ℝ) ≤ cos618o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 3 - ((98399/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((10566880211/50000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos618o2c 3 := by
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
    calc ((10566880211/50000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((98389/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((111509/250000 : ℚ) : ℝ) ≤ cos618o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 4 - ((55767/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((5003520339/78125000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos618o2c 4 := by
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
    calc ((5003520339/78125000000 : ℚ) : ℝ)
        = ((44871/312500 : ℚ) : ℝ) * ((111509/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((73237/125000 : ℚ) : ℝ) ≤ cos618o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 5 - ((146499/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((76943597807/1250000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos618o2c 5 := by
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
    calc ((76943597807/1250000000000 : ℚ) : ℝ)
        = ((1050611/10000000 : ℚ) : ℝ) * ((73237/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((742827/1000000 : ℚ) : ℝ) ≤ cos618o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 6 - ((742927/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((151152666441/2500000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos618o2c 6 := by
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
    calc ((151152666441/2500000000000 : ℚ) : ℝ)
        = ((203483/2500000 : ℚ) : ℝ) * ((742827/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-322967/1000000 : ℚ) : ℝ) ≤ cos618o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 7 - ((-322867/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-379795950353/10000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos618o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((1175959/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-379795950353/10000000000000 : ℚ) : ℝ)
        = ((1175959/10000000 : ℚ) : ℝ) * ((-322967/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-91713/1000000 : ℚ) : ℝ) ≤ cos618o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 8 - ((-91613/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-23279419077/2500000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos618o2c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((253829/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-23279419077/2500000000000 : ℚ) : ℝ)
        = ((253829/2500000 : ℚ) : ℝ) * ((-91713/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((936369/1000000 : ℚ) : ℝ) ≤ cos618o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 9 - ((936469/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((432022865589/10000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos618o2c 9 := by
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
    calc ((432022865589/10000000000000 : ℚ) : ℝ)
        = ((461381/10000000 : ℚ) : ℝ) * ((936369/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((71793/1000000 : ℚ) : ℝ) ≤ cos618o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 10 - ((71893/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((28581295851/10000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos618o2c 10 := by
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
    calc ((28581295851/10000000000000 : ℚ) : ℝ)
        = ((398107/10000000 : ℚ) : ℝ) * ((71793/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos618o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum618o2_floor
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
  have htail : ((68530401/400000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum618o2_500
    have hx1 : ((715267/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((333/2000000 : ℚ) : ℝ)
          * (((205797/200000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos618o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/618 + 1/2)
      ≤ ((1343/1250000 : ℚ) : ℝ) * (1000/618 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos618o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos618o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos618o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos618o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos618o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos618o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos618o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos618o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos618o2c 10) := by
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
theorem seg618o2_interval_6 {σ : ℝ} (ha : (7/5:ℝ) ≤ σ) (hb : σ ≤ (17/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((618:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta618o2_lower h1 h2
  have hc2 : ((425119/500000 : ℚ) : ℝ) ≤ cos618o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 2 - ((425169/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1308457190459/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos618o2c 2 := by
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
    calc ((1308457190459/5000000000000 : ℚ) : ℝ)
        = ((3077861/10000000 : ℚ) : ℝ) * ((425119/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((98389/100000 : ℚ) : ℝ) ≤ cos618o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 3 - ((98399/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((37999701191/250000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos618o2c 3 := by
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
    calc ((37999701191/250000000000 : ℚ) : ℝ)
        = ((386219/2500000 : ℚ) : ℝ) * ((98389/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((111509/250000 : ℚ) : ℝ) ≤ cos618o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 4 - ((55767/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((52817464449/1250000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos618o2c 4 := by
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
    calc ((52817464449/1250000000000 : ℚ) : ℝ)
        = ((473661/5000000 : ℚ) : ℝ) * ((111509/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((73237/125000 : ℚ) : ℝ) ≤ cos618o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 5 - ((146499/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((23738382047/625000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos618o2c 5 := by
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
    calc ((23738382047/625000000000 : ℚ) : ℝ)
        = ((324131/5000000 : ℚ) : ℝ) * ((73237/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((742827/1000000 : ℚ) : ℝ) ≤ cos618o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 6 - ((742927/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((353207553057/10000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos618o2c 6 := by
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
    calc ((353207553057/10000000000000 : ℚ) : ℝ)
        = ((475491/10000000 : ℚ) : ℝ) * ((742827/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-322967/1000000 : ℚ) : ℝ) ≤ cos618o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 7 - ((-322867/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-105923164023/5000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos618o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((327969/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-105923164023/5000000000000 : ℚ) : ℝ)
        = ((327969/5000000 : ℚ) : ℝ) * ((-322967/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-91713/1000000 : ℚ) : ℝ) ≤ cos618o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 8 - ((-91613/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-9980116947/2000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos618o2c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((108819/2000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-9980116947/2000000000000 : ℚ) : ℝ)
        = ((108819/2000000 : ℚ) : ℝ) * ((-91713/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((936369/1000000 : ℚ) : ℝ) ≤ cos618o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 9 - ((936469/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((27934696377/1250000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos618o2c 9 := by
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
    calc ((27934696377/1250000000000 : ℚ) : ℝ)
        = ((29833/1250000 : ℚ) : ℝ) * ((936369/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((71793/1000000 : ℚ) : ℝ) ≤ cos618o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 10 - ((71893/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((7162285059/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos618o2c 10 := by
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
    calc ((7162285059/5000000000000 : ℚ) : ℝ)
        = ((99763/5000000 : ℚ) : ℝ) * ((71793/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos618o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum618o2_floor
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
  have htail : ((26547813/1000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum618o2_500
    have hx1 : ((174189/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((129/5000000 : ℚ) : ℝ)
          * (((205797/200000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos618o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/618 + 1/2)
      ≤ ((833/5000000 : ℚ) : ℝ) * (1000/618 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos618o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos618o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos618o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos618o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos618o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos618o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos618o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos618o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos618o2c 10) := by
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
theorem seg618o2_interval_7 {σ : ℝ} (ha : (17/10:ℝ) ≤ σ) (hb : σ ≤ (2:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((618:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta618o2_lower h1 h2
  have hc2 : ((425119/500000 : ℚ) : ℝ) ≤ cos618o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 2 - ((425169/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((425119/2000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos618o2c 2 := by
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
    calc ((425119/2000000 : ℚ) : ℝ)
        = ((1/4 : ℚ) : ℝ) * ((425119/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((98389/100000 : ℚ) : ℝ) ≤ cos618o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 3 - ((98399/100000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((109321100179/1000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos618o2c 3 := by
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
    calc ((109321100179/1000000000000 : ℚ) : ℝ)
        = ((1111111/10000000 : ℚ) : ℝ) * ((98389/100000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((111509/250000 : ℚ) : ℝ) ≤ cos618o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 4 - ((55767/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((111509/4000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos618o2c 4 := by
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
    calc ((111509/4000000 : ℚ) : ℝ)
        = ((1/16 : ℚ) : ℝ) * ((111509/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((73237/125000 : ℚ) : ℝ) ≤ cos618o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 5 - ((146499/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((73237/3125000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos618o2c 5 := by
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
    calc ((73237/3125000 : ℚ) : ℝ)
        = ((1/25 : ℚ) : ℝ) * ((73237/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((742827/1000000 : ℚ) : ℝ) ≤ cos618o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 6 - ((742927/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((206340255579/10000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos618o2c 6 := by
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
    calc ((206340255579/10000000000000 : ℚ) : ℝ)
        = ((277777/10000000 : ℚ) : ℝ) * ((742827/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-322967/1000000 : ℚ) : ℝ) ≤ cos618o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 7 - ((-322867/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-29541468523/2500000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos618o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((91469/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-29541468523/2500000000000 : ℚ) : ℝ)
        = ((91469/2500000 : ℚ) : ℝ) * ((-322967/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-91713/1000000 : ℚ) : ℝ) ≤ cos618o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 8 - ((-91613/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-26741034549/10000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos618o2c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((291573/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-26741034549/10000000000000 : ℚ) : ℝ)
        = ((291573/10000000 : ℚ) : ℝ) * ((-91713/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((936369/1000000 : ℚ) : ℝ) ≤ cos618o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 9 - ((936469/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((1806255801/156250000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos618o2c 9 := by
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
    calc ((1806255801/156250000000 : ℚ) : ℝ)
        = ((1929/156250 : ℚ) : ℝ) * ((936369/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((71793/1000000 : ℚ) : ℝ) ≤ cos618o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 10 - ((71893/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos618o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((7179228207/10000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos618o2c 10 := by
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
    calc ((7179228207/10000000000000 : ℚ) : ℝ)
        = ((99999/10000000 : ℚ) : ℝ) * ((71793/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos618o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum618o2_floor
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
  have htail : ((205797/50000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum618o2_500
    have hx1 : ((169681/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((1/250000 : ℚ) : ℝ)
          * (((205797/200000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos618o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/618 + 1/2)
      ≤ ((259/10000000 : ℚ) : ℝ) * (1000/618 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos618o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos618o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos618o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos618o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos618o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos618o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos618o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos618o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos618o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos618o2c 10) := by
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
/-- **Segment positivity at the anchor 618/2 = 309.** -/
theorem segment618o2_re_pos {σ : ℝ} (h1 : (1/2:ℝ) ≤ σ) (h2 : σ ≤ 2) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((618:ℕ)):ℝ)/2) * Complex.I)).re := by
  rcases le_total σ (3/5 : ℝ) with hc | hc
  · exact seg618o2_interval_1 h1 hc
  rcases le_total σ (7/10 : ℝ) with hc2 | hc2
  · exact seg618o2_interval_2 hc hc2
  rcases le_total σ (9/10 : ℝ) with hc3 | hc3
  · exact seg618o2_interval_3 hc2 hc3
  rcases le_total σ (11/10 : ℝ) with hc4 | hc4
  · exact seg618o2_interval_4 hc3 hc4
  rcases le_total σ (7/5 : ℝ) with hc5 | hc5
  · exact seg618o2_interval_5 hc4 hc5
  rcases le_total σ (17/10 : ℝ) with hc6 | hc6
  · exact seg618o2_interval_6 hc5 hc6
  exact seg618o2_interval_7 hc6 h2

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.segment618o2_re_pos
end AxiomAudit
