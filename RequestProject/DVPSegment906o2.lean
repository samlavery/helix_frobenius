import RequestProject.DVPSegment906o2Core
import RequestProject.DVPWeights289o2
import RequestProject.DVPWeights581o2
import RequestProject.DVPWeights63
import RequestProject.DVPWeights74
import RequestProject.DVPWeights81

/-!
# Segment positivity at `t = 906/2`: rung-453 (seven σ-intervals, N = 500)
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
theorem seg906o2_interval_1 {σ : ℝ} (ha : (1/2:ℝ) ≤ σ) (hb : σ ≤ (3/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((906:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta906o2_lower h1 h2
  have hc2 : ((493273/500000 : ℚ) : ℝ) ≤ cos906o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 2 - ((493323/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((3254387855147/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos906o2c 2 := by
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
    calc ((3254387855147/5000000000000 : ℚ) : ℝ)
        = ((6597539/10000000 : ℚ) : ℝ) * ((493273/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((133839/500000 : ℚ) : ℝ) ≤ cos906o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 3 - ((133889/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((346162394151/2500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos906o2c 3 := by
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
    calc ((346162394151/2500000000000 : ℚ) : ℝ)
        = ((2586409/5000000 : ℚ) : ℝ) * ((133839/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((946849/1000000 : ℚ) : ℝ) ≤ cos906o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 4 - ((946949/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((257587429903/625000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos906o2c 4 := by
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
    calc ((257587429903/625000000000 : ℚ) : ℝ)
        = ((272047/625000 : ℚ) : ℝ) * ((946849/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((487247/500000 : ℚ) : ℝ) ≤ cos906o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 5 - ((487297/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((1855098913829/5000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos906o2c 5 := by
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
    calc ((1855098913829/5000000000000 : ℚ) : ℝ)
        = ((3807307/10000000 : ℚ) : ℝ) * ((487247/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((421011/1000000 : ℚ) : ℝ) ≤ cos906o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 6 - ((421111/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((1436820867657/10000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos906o2c 6 := by
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
    calc ((1436820867657/10000000000000 : ℚ) : ℝ)
        = ((3412787/10000000 : ℚ) : ℝ) * ((421011/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-4328/15625 : ℚ) : ℝ) ≤ cos906o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 7 - ((-69223/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-408957589/3906250000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos906o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((755929/2000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-408957589/3906250000 : ℚ) : ℝ)
        = ((755929/2000000 : ℚ) : ℝ) * ((-4328/15625 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((220467/250000 : ℚ) : ℝ) ≤ cos906o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 8 - ((55123/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((126625000983/500000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos906o2c 8 := by
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
    calc ((126625000983/500000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((220467/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((-856701/1000000 : ℚ) : ℝ) ≤ cos906o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 9 - ((-856601/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((-1427835285567/5000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos906o2c 9 := by
    have hw : ((9:ℕ) : ℝ) ^ (-σ) ≤ ((1666667/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_9_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc9).2
      (by push_cast; norm_num)
    calc ((-1427835285567/5000000000000 : ℚ) : ℝ)
        = ((1666667/5000000 : ℚ) : ℝ) * ((-856701/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((498981/500000 : ℚ) : ℝ) ≤ cos906o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 10 - ((499031/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((626691694083/2500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos906o2c 10 := by
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
    calc ((626691694083/2500000000000 : ℚ) : ℝ)
        = ((1255943/5000000 : ℚ) : ℝ) * ((498981/500000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos906o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum906o2_floor
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
  have htail : ((62923651479/312500000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum906o2_500
    have hx1 : ((1507557/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((7507/312500 : ℚ) : ℝ)
          * (((8381997/1000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos906o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/906 + 1/2)
      ≤ ((223607/5000000 : ℚ) : ℝ) * (1000/906 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos906o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos906o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos906o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos906o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos906o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos906o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos906o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos906o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos906o2c 10) := by
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
theorem seg906o2_interval_2 {σ : ℝ} (ha : (3/5:ℝ) ≤ σ) (hb : σ ≤ (7/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((906:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta906o2_lower h1 h2
  have hc2 : ((493273/500000 : ℚ) : ℝ) ≤ cos906o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 2 - ((493323/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1518225729053/2500000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos906o2c 2 := by
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
    calc ((1518225729053/2500000000000 : ℚ) : ℝ)
        = ((3077861/5000000 : ℚ) : ℝ) * ((493273/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((133839/500000 : ℚ) : ℝ) ≤ cos906o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 3 - ((133889/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((62029424457/500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos906o2c 3 := by
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
    calc ((62029424457/500000000000 : ℚ) : ℝ)
        = ((463463/1000000 : ℚ) : ℝ) * ((133839/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((946849/1000000 : ℚ) : ℝ) ≤ cos906o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 4 - ((946949/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((3587886394059/10000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos906o2c 4 := by
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
    calc ((3587886394059/10000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((946849/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((487247/500000 : ℚ) : ℝ) ≤ cos906o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 5 - ((487297/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((1579320035311/5000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos906o2c 5 := by
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
    calc ((1579320035311/5000000000000 : ℚ) : ℝ)
        = ((3241313/10000000 : ℚ) : ℝ) * ((487247/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((421011/1000000 : ℚ) : ℝ) ≤ cos906o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 6 - ((421111/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((1201122911439/10000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos906o2c 6 := by
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
    calc ((1201122911439/10000000000000 : ℚ) : ℝ)
        = ((2852949/10000000 : ℚ) : ℝ) * ((421011/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-4328/15625 : ℚ) : ℝ) ≤ cos906o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 7 - ((-69223/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-336642119/3906250000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos906o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((622259/2000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_6).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-336642119/3906250000 : ℚ) : ℝ)
        = ((622259/2000000 : ℚ) : ℝ) * ((-4328/15625 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((220467/250000 : ℚ) : ℝ) ≤ cos906o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 8 - ((55123/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((257128677897/1250000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos906o2c 8 := by
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
    calc ((257128677897/1250000000000 : ℚ) : ℝ)
        = ((1166291/5000000 : ℚ) : ℝ) * ((220467/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((-856701/1000000 : ℚ) : ℝ) ≤ cos906o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 9 - ((-856601/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((-1146182838003/5000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos906o2c 9 := by
    have hw : ((9:ℕ) : ℝ) ^ (-σ) ≤ ((1337903/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_9_6).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc9).2
      (by push_cast; norm_num)
    calc ((-1146182838003/5000000000000 : ℚ) : ℝ)
        = ((1337903/5000000 : ℚ) : ℝ) * ((-856701/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((498981/500000 : ℚ) : ℝ) ≤ cos906o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 10 - ((499031/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((497798914011/2500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos906o2c 10 := by
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
    calc ((497798914011/2500000000000 : ℚ) : ℝ)
        = ((997631/5000000 : ℚ) : ℝ) * ((498981/500000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos906o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum906o2_floor
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
  have htail : ((1081604510883/10000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum906o2_500
    have hx1 : ((148267/625000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((129039/10000000 : ℚ) : ℝ)
          * (((8381997/1000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos906o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/906 + 1/2)
      ≤ ((9609/400000 : ℚ) : ℝ) * (1000/906 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos906o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos906o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos906o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos906o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos906o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos906o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos906o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos906o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos906o2c 10) := by
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
theorem seg906o2_interval_3 {σ : ℝ} (ha : (7/10:ℝ) ≤ σ) (hb : σ ≤ (9/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((906:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta906o2_lower h1 h2
  have hc2 : ((493273/500000 : ℚ) : ℝ) ≤ cos906o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 2 - ((493323/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((2643384401691/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos906o2c 2 := by
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
    calc ((2643384401691/5000000000000 : ℚ) : ℝ)
        = ((5358867/10000000 : ℚ) : ℝ) * ((493273/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((133839/500000 : ℚ) : ℝ) ≤ cos906o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 3 - ((133889/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((49793595399/500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos906o2c 3 := by
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
    calc ((49793595399/500000000000 : ℚ) : ℝ)
        = ((372041/1000000 : ℚ) : ℝ) * ((133839/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((946849/1000000 : ℚ) : ℝ) ≤ cos906o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 4 - ((946949/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((543821776301/2000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos906o2c 4 := by
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
    calc ((543821776301/2000000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((946849/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((487247/500000 : ℚ) : ℝ) ≤ cos906o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 5 - ((487297/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((1144658680539/5000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos906o2c 5 := by
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
    calc ((1144658680539/5000000000000 : ℚ) : ℝ)
        = ((2349237/10000000 : ℚ) : ℝ) * ((487247/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((421011/1000000 : ℚ) : ℝ) ≤ cos906o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 6 - ((421111/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((419688604449/5000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos906o2c 6 := by
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
    calc ((419688604449/5000000000000 : ℚ) : ℝ)
        = ((996859/5000000 : ℚ) : ℝ) * ((421011/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-4328/15625 : ℚ) : ℝ) ≤ cos906o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 7 - ((-69223/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-1385570789/19531250000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos906o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((2561129/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-1385570789/19531250000 : ℚ) : ℝ)
        = ((2561129/10000000 : ℚ) : ℝ) * ((-4328/15625 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((220467/250000 : ℚ) : ℝ) ≤ cos906o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 8 - ((55123/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((33928328031/250000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos906o2c 8 := by
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
    calc ((33928328031/250000000000 : ℚ) : ℝ)
        = ((153893/1000000 : ℚ) : ℝ) * ((220467/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((-856701/1000000 : ℚ) : ℝ) ≤ cos906o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 9 - ((-856601/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((-1840177470681/10000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos906o2c 9 := by
    have hw : ((9:ℕ) : ℝ) ^ (-σ) ≤ ((2147981/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_9_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc9).2
      (by push_cast; norm_num)
    calc ((-1840177470681/10000000000000 : ℚ) : ℝ)
        = ((2147981/10000000 : ℚ) : ℝ) * ((-856701/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((498981/500000 : ℚ) : ℝ) ≤ cos906o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 10 - ((499031/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((25127186217/200000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos906o2c 10 := by
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
    calc ((25127186217/200000000000 : ℚ) : ℝ)
        = ((50357/400000 : ℚ) : ℝ) * ((498981/500000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos906o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum906o2_floor
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
  have htail : ((19504907019/625000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum906o2_500
    have hx1 : ((233311/1250000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((2327/625000 : ℚ) : ℝ)
          * (((8381997/1000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos906o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/906 + 1/2)
      ≤ ((1613/125000 : ℚ) : ℝ) * (1000/906 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos906o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos906o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos906o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos906o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos906o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos906o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos906o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos906o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos906o2c 10) := by
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
theorem seg906o2_interval_4 {σ : ℝ} (ha : (9/10:ℝ) ≤ σ) (hb : σ ≤ (11/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((906:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta906o2_lower h1 h2
  have hc2 : ((493273/500000 : ℚ) : ℝ) ≤ cos906o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 2 - ((493323/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((575299860443/1250000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos906o2c 2 := by
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
    calc ((575299860443/1250000000000 : ℚ) : ℝ)
        = ((1166291/2500000 : ℚ) : ℝ) * ((493273/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((133839/500000 : ℚ) : ℝ) ≤ cos906o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 3 - ((133889/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((12491060031/156250000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos906o2c 3 := by
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
    calc ((12491060031/156250000000 : ℚ) : ℝ)
        = ((93329/312500 : ℚ) : ℝ) * ((133839/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((946849/1000000 : ℚ) : ℝ) ≤ cos906o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 4 - ((946949/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((257587429903/1250000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos906o2c 4 := by
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
    calc ((257587429903/1250000000000 : ℚ) : ℝ)
        = ((272047/1250000 : ℚ) : ℝ) * ((946849/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((487247/500000 : ℚ) : ℝ) ≤ cos906o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 5 - ((487297/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((829625234713/5000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos906o2c 5 := by
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
    calc ((829625234713/5000000000000 : ℚ) : ℝ)
        = ((1702679/10000000 : ℚ) : ℝ) * ((487247/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((421011/1000000 : ℚ) : ℝ) ≤ cos906o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 6 - ((421111/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((36661216869/625000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos906o2c 6 := by
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
    calc ((36661216869/625000000000 : ℚ) : ℝ)
        = ((87079/625000 : ℚ) : ℝ) * ((421011/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-4328/15625 : ℚ) : ℝ) ≤ cos906o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 7 - ((-69223/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-938877909/19531250000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos906o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((1735449/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-938877909/19531250000 : ℚ) : ℝ)
        = ((1735449/10000000 : ℚ) : ℝ) * ((-4328/15625 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((220467/250000 : ℚ) : ℝ) ≤ cos906o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 8 - ((55123/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((44768690421/500000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos906o2c 8 := by
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
    calc ((44768690421/500000000000 : ℚ) : ℝ)
        = ((203063/2000000 : ℚ) : ℝ) * ((220467/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((-856701/1000000 : ℚ) : ℝ) ≤ cos906o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 9 - ((-856601/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((-592899631173/5000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos906o2c 9 := by
    have hw : ((9:ℕ) : ℝ) ^ (-σ) ≤ ((692073/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_9_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc9).2
      (by push_cast; norm_num)
    calc ((-592899631173/5000000000000 : ℚ) : ℝ)
        = ((692073/5000000 : ℚ) : ℝ) * ((-856701/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((498981/500000 : ℚ) : ℝ) ≤ cos906o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 10 - ((499031/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((49544322471/625000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos906o2c 10 := by
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
    calc ((49544322471/625000000000 : ℚ) : ℝ)
        = ((99291/1250000 : ℚ) : ℝ) * ((498981/500000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos906o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum906o2_floor
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
  have htail : ((90047793771/10000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum906o2_500
    have hx1 : ((577719/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((10743/10000000 : ℚ) : ℝ)
          * (((8381997/1000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos906o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/906 + 1/2)
      ≤ ((37233/10000000 : ℚ) : ℝ) * (1000/906 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos906o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos906o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos906o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos906o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos906o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos906o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos906o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos906o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos906o2c 10) := by
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
theorem seg906o2_interval_5 {σ : ℝ} (ha : (11/10:ℝ) ≤ σ) (hb : σ ≤ (7/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((906:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta906o2_lower h1 h2
  have hc2 : ((493273/500000 : ℚ) : ℝ) ≤ cos906o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 2 - ((493323/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1869154939443/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos906o2c 2 := by
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
    calc ((1869154939443/5000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((493273/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((133839/500000 : ℚ) : ℝ) ≤ cos906o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 3 - ((133889/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((14374174761/250000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos906o2c 3 := by
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
    calc ((14374174761/250000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((133839/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((946849/1000000 : ℚ) : ℝ) ≤ cos906o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 4 - ((946949/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((42486061479/312500000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos906o2c 4 := by
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
    calc ((42486061479/312500000000 : ℚ) : ℝ)
        = ((44871/312500 : ℚ) : ℝ) * ((946849/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((487247/500000 : ℚ) : ℝ) ≤ cos906o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 5 - ((487297/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((511907057917/5000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos906o2c 5 := by
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
    calc ((511907057917/5000000000000 : ℚ) : ℝ)
        = ((1050611/10000000 : ℚ) : ℝ) * ((487247/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((421011/1000000 : ℚ) : ℝ) ≤ cos906o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 6 - ((421111/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((85668581313/2500000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos906o2c 6 := by
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
    calc ((85668581313/2500000000000 : ℚ) : ℝ)
        = ((203483/2500000 : ℚ) : ℝ) * ((421011/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-4328/15625 : ℚ) : ℝ) ≤ cos906o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 7 - ((-69223/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-636193819/19531250000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos906o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((1175959/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-636193819/19531250000 : ℚ) : ℝ)
        = ((1175959/10000000 : ℚ) : ℝ) * ((-4328/15625 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((220467/250000 : ℚ) : ℝ) ≤ cos906o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 8 - ((55123/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((59977385949/1250000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos906o2c 8 := by
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
    calc ((59977385949/1250000000000 : ℚ) : ℝ)
        = ((272047/5000000 : ℚ) : ℝ) * ((220467/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((-856701/1000000 : ℚ) : ℝ) ≤ cos906o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 9 - ((-856601/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((-23878826973/312500000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos906o2c 9 := by
    have hw : ((9:ℕ) : ℝ) ^ (-σ) ≤ ((27873/312500 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_9_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc9).2
      (by push_cast; norm_num)
    calc ((-23878826973/312500000000 : ℚ) : ℝ)
        = ((27873/312500 : ℚ) : ℝ) * ((-856701/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((498981/500000 : ℚ) : ℝ) ≤ cos906o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 10 - ((499031/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((198647828967/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos906o2c 10 := by
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
    calc ((198647828967/5000000000000 : ℚ) : ℝ)
        = ((398107/10000000 : ℚ) : ℝ) * ((498981/500000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos906o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum906o2_floor
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
  have htail : ((2791205001/2000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum906o2_500
    have hx1 : ((715267/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((333/2000000 : ℚ) : ℝ)
          * (((8381997/1000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos906o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/906 + 1/2)
      ≤ ((1343/1250000 : ℚ) : ℝ) * (1000/906 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos906o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos906o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos906o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos906o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos906o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos906o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos906o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos906o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos906o2c 10) := by
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
theorem seg906o2_interval_6 {σ : ℝ} (ha : (7/5:ℝ) ≤ σ) (hb : σ ≤ (17/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((906:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta906o2_lower h1 h2
  have hc2 : ((493273/500000 : ℚ) : ℝ) ≤ cos906o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 2 - ((493323/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1518225729053/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos906o2c 2 := by
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
    calc ((1518225729053/5000000000000 : ℚ) : ℝ)
        = ((3077861/10000000 : ℚ) : ℝ) * ((493273/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((133839/500000 : ℚ) : ℝ) ≤ cos906o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 3 - ((133889/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((51691164741/1250000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos906o2c 3 := by
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
    calc ((51691164741/1250000000000 : ℚ) : ℝ)
        = ((386219/2500000 : ℚ) : ℝ) * ((133839/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((946849/1000000 : ℚ) : ℝ) ≤ cos906o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 4 - ((946949/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((448485444189/5000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos906o2c 4 := by
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
    calc ((448485444189/5000000000000 : ℚ) : ℝ)
        = ((473661/5000000 : ℚ) : ℝ) * ((946849/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((487247/500000 : ℚ) : ℝ) ≤ cos906o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 5 - ((487297/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((157931857357/2500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos906o2c 5 := by
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
    calc ((157931857357/2500000000000 : ℚ) : ℝ)
        = ((324131/5000000 : ℚ) : ℝ) * ((487247/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((421011/1000000 : ℚ) : ℝ) ≤ cos906o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 6 - ((421111/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((200186941401/10000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos906o2c 6 := by
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
    calc ((200186941401/10000000000000 : ℚ) : ℝ)
        = ((475491/10000000 : ℚ) : ℝ) * ((421011/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-4328/15625 : ℚ) : ℝ) ≤ cos906o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 7 - ((-69223/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-177431229/9765625000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos906o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((327969/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-177431229/9765625000 : ℚ) : ℝ)
        = ((327969/5000000 : ℚ) : ℝ) * ((-4328/15625 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((220467/250000 : ℚ) : ℝ) ≤ cos906o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 8 - ((55123/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((16070501031/625000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos906o2c 8 := by
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
    calc ((16070501031/625000000000 : ℚ) : ℝ)
        = ((72893/2500000 : ℚ) : ℝ) * ((220467/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((-856701/1000000 : ℚ) : ℝ) ≤ cos906o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 9 - ((-856601/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((-197633210391/5000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos906o2c 9 := by
    have hw : ((9:ℕ) : ℝ) ^ (-σ) ≤ ((230691/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_9_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc9).2
      (by push_cast; norm_num)
    calc ((-197633210391/5000000000000 : ℚ) : ℝ)
        = ((230691/5000000 : ℚ) : ℝ) * ((-856701/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((498981/500000 : ℚ) : ℝ) ≤ cos906o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 10 - ((499031/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((49779841503/2500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos906o2c 10 := by
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
    calc ((49779841503/2500000000000 : ℚ) : ℝ)
        = ((99763/5000000 : ℚ) : ℝ) * ((498981/500000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos906o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum906o2_floor
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
  have htail : ((1081277613/5000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum906o2_500
    have hx1 : ((174189/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((129/5000000 : ℚ) : ℝ)
          * (((8381997/1000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos906o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/906 + 1/2)
      ≤ ((833/5000000 : ℚ) : ℝ) * (1000/906 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos906o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos906o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos906o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos906o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos906o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos906o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos906o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos906o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos906o2c 10) := by
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
theorem seg906o2_interval_7 {σ : ℝ} (ha : (17/10:ℝ) ≤ σ) (hb : σ ≤ (2:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((906:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta906o2_lower h1 h2
  have hc2 : ((493273/500000 : ℚ) : ℝ) ≤ cos906o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 2 - ((493323/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((493273/2000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos906o2c 2 := by
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
    calc ((493273/2000000 : ℚ) : ℝ)
        = ((1/4 : ℚ) : ℝ) * ((493273/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((133839/500000 : ℚ) : ℝ) ≤ cos906o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 3 - ((133889/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((148709985129/5000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos906o2c 3 := by
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
    calc ((148709985129/5000000000000 : ℚ) : ℝ)
        = ((1111111/10000000 : ℚ) : ℝ) * ((133839/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((946849/1000000 : ℚ) : ℝ) ≤ cos906o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 4 - ((946949/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((946849/16000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos906o2c 4 := by
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
    calc ((946849/16000000 : ℚ) : ℝ)
        = ((1/16 : ℚ) : ℝ) * ((946849/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((487247/500000 : ℚ) : ℝ) ≤ cos906o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 5 - ((487297/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((487247/12500000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos906o2c 5 := by
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
    calc ((487247/12500000 : ℚ) : ℝ)
        = ((1/25 : ℚ) : ℝ) * ((487247/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((421011/1000000 : ℚ) : ℝ) ≤ cos906o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 6 - ((421111/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((116947172547/10000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos906o2c 6 := by
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
    calc ((116947172547/10000000000000 : ℚ) : ℝ)
        = ((277777/10000000 : ℚ) : ℝ) * ((421011/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-4328/15625 : ℚ) : ℝ) ≤ cos906o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 7 - ((-69223/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-49484729/4882812500 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos906o2c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((91469/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-49484729/4882812500 : ℚ) : ℝ)
        = ((91469/2500000 : ℚ) : ℝ) * ((-4328/15625 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((220467/250000 : ℚ) : ℝ) ≤ cos906o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 8 - ((55123/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((220467/16000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos906o2c 8 := by
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
    calc ((220467/16000000 : ℚ) : ℝ)
        = ((1/64 : ℚ) : ℝ) * ((220467/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((-856701/1000000 : ℚ) : ℝ) ≤ cos906o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 9 - ((-856601/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((-40892908833/2000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos906o2c 9 := by
    have hw : ((9:ℕ) : ℝ) ^ (-σ) ≤ ((47733/2000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_9_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((9:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc9).2
      (by push_cast; norm_num)
    calc ((-40892908833/2000000000000 : ℚ) : ℝ)
        = ((47733/2000000 : ℚ) : ℝ) * ((-856701/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((498981/500000 : ℚ) : ℝ) ≤ cos906o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 10 - ((499031/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos906o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((49897601019/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos906o2c 10 := by
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
    calc ((49897601019/5000000000000 : ℚ) : ℝ)
        = ((99999/10000000 : ℚ) : ℝ) * ((498981/500000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos906o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    500 (by norm_num) hanti hnn psum906o2_floor
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
  have htail : ((8381997/250000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n) := by
    refine le_trans ?_ habel
    have hC500 := psum906o2_500
    have hx1 : ((169681/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((1/250000 : ℚ) : ℝ)
          * (((8381997/1000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((500:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 500, cos906o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw500lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC500]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (500 : ℝ) ^ (-σ) * (1000/906 + 1/2)
      ≤ ((259/10000000 : ℚ) : ℝ) * (1000/906 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 500, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n) := by
    rw [show Finset.Icc (2:ℕ) 500
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 500 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos906o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos906o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos906o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos906o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos906o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos906o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos906o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos906o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos906o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos906o2c 10) := by
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
/-- **Segment positivity at the anchor 906/2.** -/
theorem segment906o2_re_pos {σ : ℝ} (h1 : (1/2:ℝ) ≤ σ) (h2 : σ ≤ 2) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((906:ℕ)):ℝ)/2) * Complex.I)).re := by
  rcases le_total σ (3/5 : ℝ) with hc | hc
  · exact seg906o2_interval_1 h1 hc
  rcases le_total σ (7/10 : ℝ) with hc2 | hc2
  · exact seg906o2_interval_2 hc hc2
  rcases le_total σ (9/10 : ℝ) with hc3 | hc3
  · exact seg906o2_interval_3 hc2 hc3
  rcases le_total σ (11/10 : ℝ) with hc4 | hc4
  · exact seg906o2_interval_4 hc3 hc4
  rcases le_total σ (7/5 : ℝ) with hc5 | hc5
  · exact seg906o2_interval_5 hc4 hc5
  rcases le_total σ (17/10 : ℝ) with hc6 | hc6
  · exact seg906o2_interval_6 hc5 hc6
  exact seg906o2_interval_7 hc6 h2

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.segment906o2_re_pos
end AxiomAudit
