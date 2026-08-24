import RequestProject.DVPSegment399o2Core
import RequestProject.DVPWeights289o2
import RequestProject.DVPWeights63
import RequestProject.DVPWeights74
import RequestProject.DVPWeights81

/-!
# Segment positivity at `t = 399/2`: rung-199.5 (seven σ-intervals)
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

set_option maxRecDepth 8192 in
theorem seg399o2_interval_1 {σ : ℝ} (ha : (1/2:ℝ) ≤ σ) (hb : σ ≤ (3/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((399:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta399o2_lower h1 h2
  have hc2 : ((998567/1000000 : ℚ) : ℝ) ≤ cos399o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 2 - ((998607/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((6588084726613/10000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos399o2c 2 := by
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
    calc ((6588084726613/10000000000000 : ℚ) : ℝ)
        = ((6597539/10000000 : ℚ) : ℝ) * ((998567/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((369773/500000 : ℚ) : ℝ) ≤ cos399o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 3 - ((369793/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((956384215157/2500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos399o2c 3 := by
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
    calc ((956384215157/2500000000000 : ℚ) : ℝ)
        = ((2586409/5000000 : ℚ) : ℝ) * ((369773/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((994393/1000000 : ℚ) : ℝ) ≤ cos399o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 4 - ((994433/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((270521632471/625000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos399o2c 4 := by
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
    calc ((270521632471/625000000000 : ℚ) : ℝ)
        = ((272047/625000 : ℚ) : ℝ) * ((994393/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((160361/200000 : ℚ) : ℝ) ≤ cos399o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 5 - ((160369/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((610543557827/2000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos399o2c 5 := by
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
    calc ((610543557827/2000000000000 : ℚ) : ℝ)
        = ((3807307/10000000 : ℚ) : ℝ) * ((160361/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((774029/1000000 : ℚ) : ℝ) ≤ cos399o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 6 - ((774069/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((2641596108823/10000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos399o2c 6 := by
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
    calc ((2641596108823/10000000000000 : ℚ) : ℝ)
        = ((3412787/10000000 : ℚ) : ℝ) * ((774029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((110257/500000 : ℚ) : ℝ) ≤ cos399o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 7 - ((110277/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((171520971279/2500000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos399o2c 7 := by
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
    calc ((171520971279/2500000000000 : ℚ) : ℝ)
        = ((1555647/5000000 : ℚ) : ℝ) * ((110257/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((987447/1000000 : ℚ) : ℝ) ≤ cos399o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 8 - ((987487/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((567139197003/2000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos399o2c 8 := by
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
    calc ((567139197003/2000000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((987447/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((11743/125000 : ℚ) : ℝ) ≤ cos399o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 9 - ((2937/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((6284395623/250000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos399o2c 9 := by
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
    calc ((6284395623/250000000000 : ℚ) : ℝ)
        = ((535161/2000000 : ℚ) : ℝ) * ((11743/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((192293/250000 : ℚ) : ℝ) ≤ cos399o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 10 - ((192303/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((241509047299/1250000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos399o2c 10 := by
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
    calc ((241509047299/1250000000000 : ℚ) : ℝ)
        = ((1255943/5000000 : ℚ) : ℝ) * ((192293/250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos399o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum399o2_floor
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
  have htail : ((13005466201/39062500000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum399o2_250
    have hx1 : ((1507557/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((22757/625000 : ℚ) : ℝ)
          * (((571493/62500 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos399o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/399 + 1/2)
      ≤ ((79057/1250000 : ℚ) : ℝ) * (500/399 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos399o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos399o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos399o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos399o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos399o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos399o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos399o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos399o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos399o2c 10) := by
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
theorem seg399o2_interval_2 {σ : ℝ} (ha : (3/5:ℝ) ≤ σ) (hb : σ ≤ (7/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((399:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta399o2_lower h1 h2
  have hc2 : ((998567/1000000 : ℚ) : ℝ) ≤ cos399o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 2 - ((998607/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((3073450425187/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos399o2c 2 := by
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
    calc ((3073450425187/5000000000000 : ℚ) : ℝ)
        = ((3077861/5000000 : ℚ) : ℝ) * ((998567/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((369773/500000 : ℚ) : ℝ) ≤ cos399o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 3 - ((369793/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((171376103899/500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos399o2c 3 := by
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
    calc ((171376103899/500000000000 : ℚ) : ℝ)
        = ((463463/1000000 : ℚ) : ℝ) * ((369773/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((994393/1000000 : ℚ) : ℝ) ≤ cos399o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 4 - ((994433/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((3768044445363/10000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos399o2c 4 := by
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
    calc ((3768044445363/10000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((994393/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((160361/200000 : ℚ) : ℝ) ≤ cos399o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 5 - ((160369/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((519780193993/2000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos399o2c 5 := by
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
    calc ((519780193993/2000000000000 : ℚ) : ℝ)
        = ((3241313/10000000 : ℚ) : ℝ) * ((160361/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((774029/1000000 : ℚ) : ℝ) ≤ cos399o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 6 - ((774069/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((2208265261521/10000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos399o2c 6 := by
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
    calc ((2208265261521/10000000000000 : ℚ) : ℝ)
        = ((2852949/10000000 : ℚ) : ℝ) * ((774029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((110257/500000 : ℚ) : ℝ) ≤ cos399o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 7 - ((110277/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((35297786237/625000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos399o2c 7 := by
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
    calc ((35297786237/625000000000 : ℚ) : ℝ)
        = ((320141/1250000 : ℚ) : ℝ) * ((110257/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((987447/1000000 : ℚ) : ℝ) ≤ cos399o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 8 - ((987487/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((1151650549077/5000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos399o2c 8 := by
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
    calc ((1151650549077/5000000000000 : ℚ) : ℝ)
        = ((1166291/5000000 : ℚ) : ℝ) * ((987447/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((11743/125000 : ℚ) : ℝ) ≤ cos399o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 9 - ((2937/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((1261186457/62500000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos399o2c 9 := by
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
    calc ((1261186457/62500000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((11743/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((192293/250000 : ℚ) : ℝ) ≤ cos399o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 10 - ((192303/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((191837457883/1250000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos399o2c 10 := by
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
    calc ((191837457883/1250000000000 : ℚ) : ℝ)
        = ((997631/5000000 : ℚ) : ℝ) * ((192293/250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos399o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum399o2_floor
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
  have htail : ((14974831079/78125000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum399o2_250
    have hx1 : ((148267/625000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((26203/1250000 : ℚ) : ℝ)
          * (((571493/62500 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos399o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/399 + 1/2)
      ≤ ((364113/10000000 : ℚ) : ℝ) * (500/399 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos399o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos399o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos399o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos399o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos399o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos399o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos399o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos399o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos399o2c 10) := by
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
theorem seg399o2_interval_3 {σ : ℝ} (ha : (7/10:ℝ) ≤ σ) (hb : σ ≤ (9/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((399:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta399o2_lower h1 h2
  have hc2 : ((998567/1000000 : ℚ) : ℝ) ≤ cos399o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 2 - ((998607/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((5351187743589/10000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos399o2c 2 := by
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
    calc ((5351187743589/10000000000000 : ℚ) : ℝ)
        = ((5358867/10000000 : ℚ) : ℝ) * ((998567/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((369773/500000 : ℚ) : ℝ) ≤ cos399o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 3 - ((369793/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((137570716693/500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos399o2c 3 := by
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
    calc ((137570716693/500000000000 : ℚ) : ℝ)
        = ((372041/1000000 : ℚ) : ℝ) * ((369773/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((994393/1000000 : ℚ) : ℝ) ≤ cos399o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 4 - ((994433/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((571128625157/2000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos399o2c 4 := by
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
    calc ((571128625157/2000000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((994393/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((160361/200000 : ℚ) : ℝ) ≤ cos399o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 5 - ((160369/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((376725994557/2000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos399o2c 5 := by
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
    calc ((376725994557/2000000000000 : ℚ) : ℝ)
        = ((2349237/10000000 : ℚ) : ℝ) * ((160361/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((774029/1000000 : ℚ) : ℝ) ≤ cos399o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 6 - ((774069/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((771597774911/5000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos399o2c 6 := by
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
    calc ((771597774911/5000000000000 : ℚ) : ℝ)
        = ((996859/5000000 : ℚ) : ℝ) * ((774029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((110257/500000 : ℚ) : ℝ) ≤ cos399o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 7 - ((110277/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((23918161267/625000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos399o2c 7 := by
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
    calc ((23918161267/625000000000 : ℚ) : ℝ)
        = ((216931/1250000 : ℚ) : ℝ) * ((110257/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((987447/1000000 : ℚ) : ℝ) ≤ cos399o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 8 - ((987487/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((151961181171/1000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos399o2c 8 := by
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
    calc ((151961181171/1000000000000 : ℚ) : ℝ)
        = ((153893/1000000 : ℚ) : ℝ) * ((987447/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((11743/125000 : ℚ) : ℝ) ≤ cos399o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 9 - ((2937/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((3250802947/250000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos399o2c 9 := by
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
    calc ((3250802947/250000000000 : ℚ) : ℝ)
        = ((276829/2000000 : ℚ) : ℝ) * ((11743/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((192293/250000 : ℚ) : ℝ) ≤ cos399o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 10 - ((192303/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((9683298601/100000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos399o2c 10 := by
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
    calc ((9683298601/100000000000 : ℚ) : ℝ)
        = ((50357/400000 : ℚ) : ℝ) * ((192293/250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos399o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum399o2_floor
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
  have htail : ((39706762147/625000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum399o2_250
    have hx1 : ((233311/1250000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((69479/10000000 : ℚ) : ℝ)
          * (((571493/62500 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos399o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/399 + 1/2)
      ≤ ((1677/80000 : ℚ) : ℝ) * (500/399 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos399o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos399o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos399o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos399o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos399o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos399o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos399o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos399o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos399o2c 10) := by
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
theorem seg399o2_interval_4 {σ : ℝ} (ha : (9/10:ℝ) ≤ σ) (hb : σ ≤ (11/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((399:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta399o2_lower h1 h2
  have hc2 : ((998567/1000000 : ℚ) : ℝ) ≤ cos399o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 2 - ((998607/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1164619704997/2500000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos399o2c 2 := by
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
    calc ((1164619704997/2500000000000 : ℚ) : ℝ)
        = ((1166291/2500000 : ℚ) : ℝ) * ((998567/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((369773/500000 : ℚ) : ℝ) ≤ cos399o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 3 - ((369793/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((34510544317/156250000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos399o2c 3 := by
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
    calc ((34510544317/156250000000 : ℚ) : ℝ)
        = ((93329/312500 : ℚ) : ℝ) * ((369773/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((994393/1000000 : ℚ) : ℝ) ≤ cos399o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 4 - ((994433/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((270521632471/1250000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos399o2c 4 := by
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
    calc ((270521632471/1250000000000 : ℚ) : ℝ)
        = ((272047/1250000 : ℚ) : ℝ) * ((994393/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((160361/200000 : ℚ) : ℝ) ≤ cos399o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 5 - ((160369/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((273043307119/2000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos399o2c 5 := by
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
    calc ((273043307119/2000000000000 : ℚ) : ℝ)
        = ((1702679/10000000 : ℚ) : ℝ) * ((160361/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((774029/1000000 : ℚ) : ℝ) ≤ cos399o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 6 - ((774069/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((67401671291/625000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos399o2c 6 := by
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
    calc ((67401671291/625000000000 : ℚ) : ℝ)
        = ((87079/625000 : ℚ) : ℝ) * ((774029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((110257/500000 : ℚ) : ℝ) ≤ cos399o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 7 - ((110277/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((64828800603/2500000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos399o2c 7 := by
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
    calc ((64828800603/2500000000000 : ℚ) : ℝ)
        = ((587979/5000000 : ℚ) : ℝ) * ((110257/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((987447/1000000 : ℚ) : ℝ) ≤ cos399o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 8 - ((987487/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((200513950161/2000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos399o2c 8 := by
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
    calc ((200513950161/2000000000000 : ℚ) : ℝ)
        = ((203063/2000000 : ℚ) : ℝ) * ((987447/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((11743/125000 : ℚ) : ℝ) ≤ cos399o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 9 - ((2937/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((2094798541/250000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos399o2c 9 := by
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
    calc ((2094798541/250000000000 : ℚ) : ℝ)
        = ((178387/2000000 : ℚ) : ℝ) * ((11743/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((192293/250000 : ℚ) : ℝ) ≤ cos399o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 10 - ((192303/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((19092964263/312500000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos399o2c 10 := by
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
    calc ((19092964263/312500000000 : ℚ) : ℝ)
        = ((99291/1250000 : ℚ) : ℝ) * ((192293/250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos399o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum399o2_floor
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
  have htail : ((3290085201/156250000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum399o2_250
    have hx1 : ((577719/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((5757/2500000 : ℚ) : ℝ)
          * (((571493/62500 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos399o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/399 + 1/2)
      ≤ ((1737/250000 : ℚ) : ℝ) * (500/399 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos399o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos399o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos399o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos399o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos399o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos399o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos399o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos399o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos399o2c 10) := by
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
theorem seg399o2_interval_5 {σ : ℝ} (ha : (11/10:ℝ) ≤ σ) (hb : σ ≤ (7/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((399:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta399o2_lower h1 h2
  have hc2 : ((998567/1000000 : ℚ) : ℝ) ≤ cos399o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 2 - ((998607/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((3783860945997/10000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos399o2c 2 := by
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
    calc ((3783860945997/10000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((998567/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((369773/500000 : ℚ) : ℝ) ≤ cos399o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 3 - ((369793/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((39713250427/250000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos399o2c 3 := by
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
    calc ((39713250427/250000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((369773/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((994393/1000000 : ℚ) : ℝ) ≤ cos399o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 4 - ((994433/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((44619408303/312500000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos399o2c 4 := by
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
    calc ((44619408303/312500000000 : ℚ) : ℝ)
        = ((44871/312500 : ℚ) : ℝ) * ((994393/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((160361/200000 : ℚ) : ℝ) ≤ cos399o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 5 - ((160369/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((168477030571/2000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos399o2c 5 := by
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
    calc ((168477030571/2000000000000 : ℚ) : ℝ)
        = ((1050611/10000000 : ℚ) : ℝ) * ((160361/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((774029/1000000 : ℚ) : ℝ) ≤ cos399o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 6 - ((774069/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((157501743007/2500000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos399o2c 6 := by
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
    calc ((157501743007/2500000000000 : ℚ) : ℝ)
        = ((203483/2500000 : ℚ) : ℝ) * ((774029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((110257/500000 : ℚ) : ℝ) ≤ cos399o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 7 - ((110277/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((72321645809/5000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos399o2c 7 := by
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
    calc ((72321645809/5000000000000 : ℚ) : ℝ)
        = ((655937/10000000 : ℚ) : ℝ) * ((110257/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((987447/1000000 : ℚ) : ℝ) ≤ cos399o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 8 - ((987487/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((268631994009/5000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos399o2c 8 := by
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
    calc ((268631994009/5000000000000 : ℚ) : ℝ)
        = ((272047/5000000 : ℚ) : ℝ) * ((987447/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((11743/125000 : ℚ) : ℝ) ≤ cos399o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 9 - ((2937/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((5417997083/1250000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos399o2c 9 := by
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
    calc ((5417997083/1250000000000 : ℚ) : ℝ)
        = ((461381/10000000 : ℚ) : ℝ) * ((11743/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((192293/250000 : ℚ) : ℝ) ≤ cos399o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 10 - ((192303/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((76553189351/2500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos399o2c 10 := by
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
    calc ((76553189351/2500000000000 : ℚ) : ℝ)
        = ((398107/10000000 : ℚ) : ℝ) * ((192293/250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos399o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum399o2_floor
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
  have htail : ((1255570121/312500000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum399o2_250
    have hx1 : ((715267/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((2197/5000000 : ℚ) : ℝ)
          * (((571493/62500 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos399o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/399 + 1/2)
      ≤ ((23029/10000000 : ℚ) : ℝ) * (500/399 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos399o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos399o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos399o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos399o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos399o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos399o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos399o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos399o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos399o2c 10) := by
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
theorem seg399o2_interval_6 {σ : ℝ} (ha : (7/5:ℝ) ≤ σ) (hb : σ ≤ (17/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((399:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta399o2_lower h1 h2
  have hc2 : ((998567/1000000 : ℚ) : ℝ) ≤ cos399o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 2 - ((998607/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((3073450425187/10000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos399o2c 2 := by
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
    calc ((3073450425187/10000000000000 : ℚ) : ℝ)
        = ((3077861/10000000 : ℚ) : ℝ) * ((998567/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((369773/500000 : ℚ) : ℝ) ≤ cos399o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 3 - ((369793/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((142813358287/1250000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos399o2c 3 := by
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
    calc ((142813358287/1250000000000 : ℚ) : ℝ)
        = ((386219/2500000 : ℚ) : ℝ) * ((369773/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((994393/1000000 : ℚ) : ℝ) ≤ cos399o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 4 - ((994433/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((471005182773/5000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos399o2c 4 := by
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
    calc ((471005182773/5000000000000 : ℚ) : ℝ)
        = ((473661/5000000 : ℚ) : ℝ) * ((994393/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((160361/200000 : ℚ) : ℝ) ≤ cos399o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 5 - ((160369/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((51977971291/1000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos399o2c 5 := by
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
    calc ((51977971291/1000000000000 : ℚ) : ℝ)
        = ((324131/5000000 : ℚ) : ℝ) * ((160361/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((774029/1000000 : ℚ) : ℝ) ≤ cos399o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 6 - ((774069/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((368043823239/10000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos399o2c 6 := by
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
    calc ((368043823239/10000000000000 : ℚ) : ℝ)
        = ((475491/10000000 : ℚ) : ℝ) * ((774029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((110257/500000 : ℚ) : ℝ) ≤ cos399o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 7 - ((110277/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((322722239/40000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos399o2c 7 := by
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
    calc ((322722239/40000000000 : ℚ) : ℝ)
        = ((2927/80000 : ℚ) : ℝ) * ((110257/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((987447/1000000 : ℚ) : ℝ) ≤ cos399o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 8 - ((987487/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((71977974171/2500000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos399o2c 8 := by
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
    calc ((71977974171/2500000000000 : ℚ) : ℝ)
        = ((72893/2500000 : ℚ) : ℝ) * ((987447/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((11743/125000 : ℚ) : ℝ) ≤ cos399o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 9 - ((2937/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((350328919/156250000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos399o2c 9 := by
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
    calc ((350328919/156250000000 : ℚ) : ℝ)
        = ((29833/1250000 : ℚ) : ℝ) * ((11743/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((192293/250000 : ℚ) : ℝ) ≤ cos399o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 10 - ((192303/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((19183726559/1250000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos399o2c 10 := by
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
    calc ((19183726559/1250000000000 : ℚ) : ℝ)
        = ((99763/5000000 : ℚ) : ℝ) * ((192293/250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos399o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum399o2_floor
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
  have htail : ((239455567/312500000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum399o2_250
    have hx1 : ((174189/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((419/5000000 : ℚ) : ℝ)
          * (((571493/62500 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos399o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/399 + 1/2)
      ≤ ((879/2000000 : ℚ) : ℝ) * (500/399 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos399o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos399o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos399o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos399o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos399o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos399o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos399o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos399o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos399o2c 10) := by
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
theorem seg399o2_interval_7 {σ : ℝ} (ha : (17/10:ℝ) ≤ σ) (hb : σ ≤ (2:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((399:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta399o2_lower h1 h2
  have hc2 : ((998567/1000000 : ℚ) : ℝ) ≤ cos399o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 2 - ((998607/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((998567/4000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos399o2c 2 := by
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
    calc ((998567/4000000 : ℚ) : ℝ)
        = ((1/4 : ℚ) : ℝ) * ((998567/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((369773/500000 : ℚ) : ℝ) ≤ cos399o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 3 - ((369793/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((410858847803/5000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos399o2c 3 := by
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
    calc ((410858847803/5000000000000 : ℚ) : ℝ)
        = ((1111111/10000000 : ℚ) : ℝ) * ((369773/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((994393/1000000 : ℚ) : ℝ) ≤ cos399o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 4 - ((994433/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((994393/16000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos399o2c 4 := by
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
    calc ((994393/16000000 : ℚ) : ℝ)
        = ((1/16 : ℚ) : ℝ) * ((994393/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((160361/200000 : ℚ) : ℝ) ≤ cos399o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 5 - ((160369/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((160361/5000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos399o2c 5 := by
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
    calc ((160361/5000000 : ℚ) : ℝ)
        = ((1/25 : ℚ) : ℝ) * ((160361/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((774029/1000000 : ℚ) : ℝ) ≤ cos399o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 6 - ((774069/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((215007453533/10000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos399o2c 6 := by
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
    calc ((215007453533/10000000000000 : ℚ) : ℝ)
        = ((277777/10000000 : ℚ) : ℝ) * ((774029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((110257/500000 : ℚ) : ℝ) ≤ cos399o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 7 - ((110277/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((22501358817/5000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos399o2c 7 := by
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
    calc ((22501358817/5000000000000 : ℚ) : ℝ)
        = ((204081/10000000 : ℚ) : ℝ) * ((110257/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((987447/1000000 : ℚ) : ℝ) ≤ cos399o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 8 - ((987487/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((987447/64000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos399o2c 8 := by
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
    calc ((987447/64000000 : ℚ) : ℝ)
        = ((1/64 : ℚ) : ℝ) * ((987447/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((11743/125000 : ℚ) : ℝ) ≤ cos399o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 9 - ((2937/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((22652247/19531250000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos399o2c 9 := by
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
    calc ((22652247/19531250000 : ℚ) : ℝ)
        = ((1929/156250 : ℚ) : ℝ) * ((11743/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((192293/250000 : ℚ) : ℝ) ≤ cos399o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 10 - ((192303/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos399o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((19229107707/2500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos399o2c 10 := by
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
    calc ((19229107707/2500000000000 : ℚ) : ℝ)
        = ((99999/10000000 : ℚ) : ℝ) * ((192293/250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos399o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum399o2_floor
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
  have htail : ((571493/3906250000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum399o2_250
    have hx1 : ((169681/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((1/62500 : ℚ) : ℝ)
          * (((571493/62500 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos399o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/399 + 1/2)
      ≤ ((839/10000000 : ℚ) : ℝ) * (500/399 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos399o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos399o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos399o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos399o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos399o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos399o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos399o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos399o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos399o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos399o2c 10) := by
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
/-- **Segment positivity at the half-integer anchor 399/2.** -/
theorem segment399o2_re_pos {σ : ℝ} (h1 : (1/2:ℝ) ≤ σ) (h2 : σ ≤ 2) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((399:ℕ)):ℝ)/2) * Complex.I)).re := by
  rcases le_total σ (3/5 : ℝ) with hc | hc
  · exact seg399o2_interval_1 h1 hc
  rcases le_total σ (7/10 : ℝ) with hc2 | hc2
  · exact seg399o2_interval_2 hc hc2
  rcases le_total σ (9/10 : ℝ) with hc3 | hc3
  · exact seg399o2_interval_3 hc2 hc3
  rcases le_total σ (11/10 : ℝ) with hc4 | hc4
  · exact seg399o2_interval_4 hc3 hc4
  rcases le_total σ (7/5 : ℝ) with hc5 | hc5
  · exact seg399o2_interval_5 hc4 hc5
  rcases le_total σ (17/10 : ℝ) with hc6 | hc6
  · exact seg399o2_interval_6 hc5 hc6
  exact seg399o2_interval_7 hc6 h2

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.segment399o2_re_pos
end AxiomAudit
