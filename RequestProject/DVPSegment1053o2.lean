import RequestProject.DVPSegment1053o2Core
import RequestProject.DVPWeights289o2
import RequestProject.DVPWeights581o2
import RequestProject.DVPWeights1000col
import RequestProject.DVPWeights63
import RequestProject.DVPWeights74
import RequestProject.DVPWeights81

/-!
# Segment positivity at `t = 1053/2`: rung-526.5 (seven σ-intervals, N = 1000)
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3200000 in
theorem seg1053o2_interval_1 {σ : ℝ} (ha : (1/2:ℝ) ≤ σ) (hb : σ ≤ (3/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((1053:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta1053o2_lower h1 h2
  have hc2 : ((8690939/10000000 : ℚ) : ℝ) ≤ cos1053o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 2 - ((8691939/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((57338808999121/100000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos1053o2c 2 := by
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
    calc ((57338808999121/100000000000000 : ℚ) : ℝ)
        = ((6597539/10000000 : ℚ) : ℝ) * ((8690939/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((1867117/2000000 : ℚ) : ℝ) ≤ cos1053o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 3 - ((1867317/2000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((4829128212853/10000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos1053o2c 3 := by
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
    calc ((4829128212853/10000000000000 : ℚ) : ℝ)
        = ((2586409/5000000 : ℚ) : ℝ) * ((1867117/2000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((5108733/10000000 : ℚ) : ℝ) ≤ cos1053o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 4 - ((5109733/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((1389815486451/6250000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos1053o2c 4 := by
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
    calc ((1389815486451/6250000000000 : ℚ) : ℝ)
        = ((272047/625000 : ℚ) : ℝ) * ((5108733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((162907/250000 : ℚ) : ℝ) ≤ cos1053o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 5 - ((40733/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((620236961449/2500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos1053o2c 5 := by
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
    calc ((620236961449/2500000000000 : ℚ) : ℝ)
        = ((3807307/10000000 : ℚ) : ℝ) * ((162907/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((1585769/2500000 : ℚ) : ℝ) ≤ cos1053o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 6 - ((1586019/2500000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((5411891828203/25000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos1053o2c 6 := by
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
    calc ((5411891828203/25000000000000 : ℚ) : ℝ)
        = ((3412787/10000000 : ℚ) : ℝ) * ((1585769/2500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((9349171/10000000 : ℚ) : ℝ) ≤ cos1053o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 7 - ((9350171/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((14544009818637/50000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos1053o2c 7 := by
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
    calc ((14544009818637/50000000000000 : ℚ) : ℝ)
        = ((1555647/5000000 : ℚ) : ℝ) * ((9349171/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((1517/80000 : ℚ) : ℝ) ≤ cos1053o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 8 - ((61/3200 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((871287433/160000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos1053o2c 8 := by
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
    calc ((871287433/160000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((1517/80000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((3716593/5000000 : ℚ) : ℝ) ≤ cos1053o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 9 - ((3717093/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((1988975626473/10000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos1053o2c 9 := by
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
    calc ((1988975626473/10000000000000 : ℚ) : ℝ)
        = ((535161/2000000 : ℚ) : ℝ) * ((3716593/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((1176753/1250000 : ℚ) : ℝ) ≤ cos1053o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 10 - ((588439/625000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((1477934693079/6250000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos1053o2c 10 := by
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
    calc ((1477934693079/6250000000000 : ℚ) : ℝ)
        = ((1255943/5000000 : ℚ) : ℝ) * ((1176753/1250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos1053o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum1053o2_floor
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
  have htail : ((47893686625161/200000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum1053o2_1000
    have hx1 : ((1507557/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((1584893/100000000 : ℚ) : ℝ)
          * (((30218877/2000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos1053o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/1053 + 1/2)
      ≤ ((1581139/50000000 : ℚ) : ℝ) * (2000/1053 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos1053o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos1053o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos1053o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos1053o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos1053o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos1053o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos1053o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos1053o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos1053o2c 10) := by
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
theorem seg1053o2_interval_2 {σ : ℝ} (ha : (3/5:ℝ) ≤ σ) (hb : σ ≤ (7/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((1053:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta1053o2_lower h1 h2
  have hc2 : ((8690939/10000000 : ℚ) : ℝ) ≤ cos1053o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 2 - ((8691939/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((26749502201479/50000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos1053o2c 2 := by
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
    calc ((26749502201479/50000000000000 : ℚ) : ℝ)
        = ((3077861/5000000 : ℚ) : ℝ) * ((8690939/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((1867117/2000000 : ℚ) : ℝ) ≤ cos1053o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 3 - ((1867317/2000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((865339646171/2000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos1053o2c 3 := by
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
    calc ((865339646171/2000000000000 : ℚ) : ℝ)
        = ((463463/1000000 : ℚ) : ℝ) * ((1867117/2000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((5108733/10000000 : ℚ) : ℝ) ≤ cos1053o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 4 - ((5109733/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((19358475978303/100000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos1053o2c 4 := by
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
    calc ((19358475978303/100000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((5108733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((162907/250000 : ℚ) : ℝ) ≤ cos1053o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 5 - ((40733/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((528032576891/2500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos1053o2c 5 := by
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
    calc ((528032576891/2500000000000 : ℚ) : ℝ)
        = ((3241313/10000000 : ℚ) : ℝ) * ((162907/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((1585769/2500000 : ℚ) : ℝ) ≤ cos1053o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 6 - ((1586019/2500000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((4524118082781/25000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos1053o2c 6 := by
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
    calc ((4524118082781/25000000000000 : ℚ) : ℝ)
        = ((2852949/10000000 : ℚ) : ℝ) * ((1585769/2500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((9349171/10000000 : ℚ) : ℝ) ≤ cos1053o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 7 - ((9350171/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((2993052953111/12500000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos1053o2c 7 := by
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
    calc ((2993052953111/12500000000000 : ℚ) : ℝ)
        = ((320141/1250000 : ℚ) : ℝ) * ((9349171/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((1517/80000 : ℚ) : ℝ) ≤ cos1053o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 8 - ((61/3200 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((1769263447/400000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos1053o2c 8 := by
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
    calc ((1769263447/400000000000 : ℚ) : ℝ)
        = ((1166291/5000000 : ℚ) : ℝ) * ((1517/80000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((3716593/5000000 : ℚ) : ℝ) ≤ cos1053o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 9 - ((3717093/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((399158371607/2500000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos1053o2c 9 := by
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
    calc ((399158371607/2500000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((3716593/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((1176753/1250000 : ℚ) : ℝ) ≤ cos1053o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 10 - ((588439/625000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((1173965272143/6250000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos1053o2c 10 := by
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
    calc ((1173965272143/6250000000000 : ℚ) : ℝ)
        = ((997631/5000000 : ℚ) : ℝ) * ((1176753/1250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos1053o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum1053o2_floor
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
  have htail : ((3000462516207/25000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum1053o2_1000
    have hx1 : ((148267/625000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((99291/12500000 : ℚ) : ℝ)
          * (((30218877/2000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos1053o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/1053 + 1/2)
      ≤ ((792447/50000000 : ℚ) : ℝ) * (2000/1053 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos1053o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos1053o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos1053o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos1053o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos1053o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos1053o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos1053o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos1053o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos1053o2c 10) := by
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
theorem seg1053o2_interval_3 {σ : ℝ} (ha : (7/10:ℝ) ≤ σ) (hb : σ ≤ (9/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((1053:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta1053o2_lower h1 h2
  have hc2 : ((8690939/10000000 : ℚ) : ℝ) ≤ cos1053o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 2 - ((8691939/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((46573586206113/100000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos1053o2c 2 := by
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
    calc ((46573586206113/100000000000000 : ℚ) : ℝ)
        = ((5358867/10000000 : ℚ) : ℝ) * ((8690939/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((1867117/2000000 : ℚ) : ℝ) ≤ cos1053o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 3 - ((1867317/2000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((694644075797/2000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos1053o2c 3 := by
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
    calc ((694644075797/2000000000000 : ℚ) : ℝ)
        = ((372041/1000000 : ℚ) : ℝ) * ((1867117/2000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((5108733/10000000 : ℚ) : ℝ) ≤ cos1053o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 4 - ((5109733/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((2934195689817/20000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos1053o2c 4 := by
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
    calc ((2934195689817/20000000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((5108733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((162907/250000 : ℚ) : ℝ) ≤ cos1053o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 5 - ((40733/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((382707151959/2500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos1053o2c 5 := by
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
    calc ((382707151959/2500000000000 : ℚ) : ℝ)
        = ((2349237/10000000 : ℚ) : ℝ) * ((162907/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((1585769/2500000 : ℚ) : ℝ) ≤ cos1053o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 6 - ((1586019/2500000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((1580788099571/12500000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos1053o2c 6 := by
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
    calc ((1580788099571/12500000000000 : ℚ) : ℝ)
        = ((996859/5000000 : ℚ) : ℝ) * ((1585769/2500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((9349171/10000000 : ℚ) : ℝ) ≤ cos1053o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 7 - ((9350171/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((2028125014201/12500000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos1053o2c 7 := by
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
    calc ((2028125014201/12500000000000 : ℚ) : ℝ)
        = ((216931/1250000 : ℚ) : ℝ) * ((9349171/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((1517/80000 : ℚ) : ℝ) ≤ cos1053o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 8 - ((61/3200 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((233455681/80000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos1053o2c 8 := by
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
    calc ((233455681/80000000000 : ℚ) : ℝ)
        = ((153893/1000000 : ℚ) : ℝ) * ((1517/80000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((3716593/5000000 : ℚ) : ℝ) ≤ cos1053o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 9 - ((3717093/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((1028860723597/10000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos1053o2c 9 := by
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
    calc ((1028860723597/10000000000000 : ℚ) : ℝ)
        = ((276829/2000000 : ℚ) : ℝ) * ((3716593/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((1176753/1250000 : ℚ) : ℝ) ≤ cos1053o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 10 - ((588439/625000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((59257750821/500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos1053o2c 10 := by
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
    calc ((59257750821/500000000000 : ℚ) : ℝ)
        = ((50357/400000 : ℚ) : ℝ) * ((1176753/1250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos1053o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum1053o2_floor
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
  have htail : ((3014725826151/100000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum1053o2_1000
    have hx1 : ((233311/1250000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((99763/50000000 : ℚ) : ℝ)
          * (((30218877/2000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos1053o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/1053 + 1/2)
      ≤ ((794329/100000000 : ℚ) : ℝ) * (2000/1053 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos1053o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos1053o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos1053o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos1053o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos1053o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos1053o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos1053o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos1053o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos1053o2c 10) := by
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
theorem seg1053o2_interval_4 {σ : ℝ} (ha : (9/10:ℝ) ≤ σ) (hb : σ ≤ (11/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((1053:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta1053o2_lower h1 h2
  have hc2 : ((8690939/10000000 : ℚ) : ℝ) ≤ cos1053o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 2 - ((8691939/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((10136163937249/25000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos1053o2c 2 := by
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
    calc ((10136163937249/25000000000000 : ℚ) : ℝ)
        = ((1166291/2500000 : ℚ) : ℝ) * ((8690939/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((1867117/2000000 : ℚ) : ℝ) ≤ cos1053o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 3 - ((1867317/2000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((174256162493/625000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos1053o2c 3 := by
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
    calc ((174256162493/625000000000 : ℚ) : ℝ)
        = ((93329/312500 : ℚ) : ℝ) * ((1867117/2000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((5108733/10000000 : ℚ) : ℝ) ≤ cos1053o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 4 - ((5109733/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((1389815486451/12500000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos1053o2c 4 := by
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
    calc ((1389815486451/12500000000000 : ℚ) : ℝ)
        = ((272047/1250000 : ℚ) : ℝ) * ((5108733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((162907/250000 : ℚ) : ℝ) ≤ cos1053o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 5 - ((40733/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((277378327853/2500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos1053o2c 5 := by
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
    calc ((277378327853/2500000000000 : ℚ) : ℝ)
        = ((1702679/10000000 : ℚ) : ℝ) * ((162907/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((1585769/2500000 : ℚ) : ℝ) ≤ cos1053o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 6 - ((1586019/2500000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((138087178751/1562500000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos1053o2c 6 := by
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
    calc ((138087178751/1562500000000 : ℚ) : ℝ)
        = ((87079/625000 : ℚ) : ℝ) * ((1585769/2500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((9349171/10000000 : ℚ) : ℝ) ≤ cos1053o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 7 - ((9350171/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((5497116215409/50000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos1053o2c 7 := by
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
    calc ((5497116215409/50000000000000 : ℚ) : ℝ)
        = ((587979/5000000 : ℚ) : ℝ) * ((9349171/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((1517/80000 : ℚ) : ℝ) ≤ cos1053o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 8 - ((61/3200 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((308046571/160000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos1053o2c 8 := by
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
    calc ((308046571/160000000000 : ℚ) : ℝ)
        = ((203063/2000000 : ℚ) : ℝ) * ((1517/80000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((3716593/5000000 : ℚ) : ℝ) ≤ cos1053o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 9 - ((3717093/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((662991875491/10000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos1053o2c 9 := by
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
    calc ((662991875491/10000000000000 : ℚ) : ℝ)
        = ((178387/2000000 : ℚ) : ℝ) * ((3716593/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((1176753/1250000 : ℚ) : ℝ) ≤ cos1053o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 10 - ((588439/625000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((116840982123/1562500000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos1053o2c 10 := by
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
    calc ((116840982123/1562500000000 : ℚ) : ℝ)
        = ((99291/1250000 : ℚ) : ℝ) * ((1176753/1250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos1053o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum1053o2_floor
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
  have htail : ((757254838743/100000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum1053o2_1000
    have hx1 : ((577719/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((25059/50000000 : ℚ) : ℝ)
          * (((30218877/2000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos1053o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/1053 + 1/2)
      ≤ ((199527/100000000 : ℚ) : ℝ) * (2000/1053 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos1053o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos1053o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos1053o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos1053o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos1053o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos1053o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos1053o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos1053o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos1053o2c 10) := by
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
theorem seg1053o2_interval_5 {σ : ℝ} (ha : (11/10:ℝ) ≤ σ) (hb : σ ≤ (7/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((1053:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta1053o2_lower h1 h2
  have hc2 : ((8690939/10000000 : ℚ) : ℝ) ≤ cos1053o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 2 - ((8691939/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((32932496934249/100000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos1053o2c 2 := by
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
    calc ((32932496934249/100000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((8690939/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((1867117/2000000 : ℚ) : ℝ) ≤ cos1053o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 3 - ((1867317/2000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((200526498683/1000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos1053o2c 3 := by
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
    calc ((200526498683/1000000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((1867117/2000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((5108733/10000000 : ℚ) : ℝ) ≤ cos1053o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 4 - ((5109733/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((229233958443/3125000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos1053o2c 4 := by
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
    calc ((229233958443/3125000000000 : ℚ) : ℝ)
        = ((44871/312500 : ℚ) : ℝ) * ((5108733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((162907/250000 : ℚ) : ℝ) ≤ cos1053o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 5 - ((40733/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((171151886177/2500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos1053o2c 5 := by
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
    calc ((171151886177/2500000000000 : ℚ) : ℝ)
        = ((1050611/10000000 : ℚ) : ℝ) * ((162907/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((1585769/2500000 : ℚ) : ℝ) ≤ cos1053o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 6 - ((1586019/2500000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((322677033427/6250000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos1053o2c 6 := by
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
    calc ((322677033427/6250000000000 : ℚ) : ℝ)
        = ((203483/2500000 : ℚ) : ℝ) * ((1585769/2500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((9349171/10000000 : ℚ) : ℝ) ≤ cos1053o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 7 - ((9350171/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((6132467178227/100000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos1053o2c 7 := by
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
    calc ((6132467178227/100000000000000 : ℚ) : ℝ)
        = ((655937/10000000 : ℚ) : ℝ) * ((9349171/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((1517/80000 : ℚ) : ℝ) ≤ cos1053o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 8 - ((61/3200 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((412695299/400000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos1053o2c 8 := by
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
    calc ((412695299/400000000000 : ℚ) : ℝ)
        = ((272047/5000000 : ℚ) : ℝ) * ((1517/80000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((3716593/5000000 : ℚ) : ℝ) ≤ cos1053o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 9 - ((3717093/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((1714765394933/50000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos1053o2c 9 := by
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
    calc ((1714765394933/50000000000000 : ℚ) : ℝ)
        = ((461381/10000000 : ℚ) : ℝ) * ((3716593/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((1176753/1250000 : ℚ) : ℝ) ≤ cos1053o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 10 - ((588439/625000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((468473606571/12500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos1053o2c 10 := by
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
    calc ((468473606571/12500000000000 : ℚ) : ℝ)
        = ((398107/10000000 : ℚ) : ℝ) * ((1176753/1250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos1053o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum1053o2_floor
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
  have htail : ((190650894993/200000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum1053o2_1000
    have hx1 : ((715267/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((6309/100000000 : ℚ) : ℝ)
          * (((30218877/2000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos1053o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/1053 + 1/2)
      ≤ ((50119/100000000 : ℚ) : ℝ) * (2000/1053 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos1053o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos1053o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos1053o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos1053o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos1053o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos1053o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos1053o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos1053o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos1053o2c 10) := by
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
theorem seg1053o2_interval_6 {σ : ℝ} (ha : (7/5:ℝ) ≤ σ) (hb : σ ≤ (17/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((1053:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta1053o2_lower h1 h2
  have hc2 : ((8690939/10000000 : ℚ) : ℝ) ≤ cos1053o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 2 - ((8691939/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((26749502201479/100000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos1053o2c 2 := by
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
    calc ((26749502201479/100000000000000 : ℚ) : ℝ)
        = ((3077861/10000000 : ℚ) : ℝ) * ((8690939/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((1867117/2000000 : ℚ) : ℝ) ≤ cos1053o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 3 - ((1867317/2000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((721116060623/5000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos1053o2c 3 := by
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
    calc ((721116060623/5000000000000 : ℚ) : ℝ)
        = ((386219/2500000 : ℚ) : ℝ) * ((1867117/2000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((5108733/10000000 : ℚ) : ℝ) ≤ cos1053o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 4 - ((5109733/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((2419807581513/50000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos1053o2c 4 := by
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
    calc ((2419807581513/50000000000000 : ℚ) : ℝ)
        = ((473661/5000000 : ℚ) : ℝ) * ((5108733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((162907/250000 : ℚ) : ℝ) ≤ cos1053o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 5 - ((40733/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((52803208817/1250000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos1053o2c 5 := by
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
    calc ((52803208817/1250000000000 : ℚ) : ℝ)
        = ((324131/5000000 : ℚ) : ℝ) * ((162907/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((1585769/2500000 : ℚ) : ℝ) ≤ cos1053o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 6 - ((1586019/2500000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((754018887579/25000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos1053o2c 6 := by
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
    calc ((754018887579/25000000000000 : ℚ) : ℝ)
        = ((475491/10000000 : ℚ) : ℝ) * ((1585769/2500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((9349171/10000000 : ℚ) : ℝ) ≤ cos1053o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 7 - ((9350171/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((27365023517/800000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos1053o2c 7 := by
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
    calc ((27365023517/800000000000 : ℚ) : ℝ)
        = ((2927/80000 : ℚ) : ℝ) * ((9349171/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((1517/80000 : ℚ) : ℝ) ≤ cos1053o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 8 - ((61/3200 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((110578681/200000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos1053o2c 8 := by
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
    calc ((110578681/200000000000 : ℚ) : ℝ)
        = ((72893/2500000 : ℚ) : ℝ) * ((1517/80000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((3716593/5000000 : ℚ) : ℝ) ≤ cos1053o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 9 - ((3717093/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((110877118969/6250000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos1053o2c 9 := by
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
    calc ((110877118969/6250000000000 : ℚ) : ℝ)
        = ((29833/1250000 : ℚ) : ℝ) * ((3716593/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((1176753/1250000 : ℚ) : ℝ) ≤ cos1053o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 10 - ((588439/625000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((117396409539/6250000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos1053o2c 10 := by
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
    calc ((117396409539/6250000000000 : ℚ) : ℝ)
        = ((99763/5000000 : ℚ) : ℝ) * ((1176753/1250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos1053o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum1053o2_floor
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
  have htail : ((11996894169/100000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum1053o2_1000
    have hx1 : ((174189/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((397/50000000 : ℚ) : ℝ)
          * (((30218877/2000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos1053o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/1053 + 1/2)
      ≤ ((631/10000000 : ℚ) : ℝ) * (2000/1053 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos1053o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos1053o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos1053o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos1053o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos1053o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos1053o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos1053o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos1053o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos1053o2c 10) := by
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
theorem seg1053o2_interval_7 {σ : ℝ} (ha : (17/10:ℝ) ≤ σ) (hb : σ ≤ (2:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((1053:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta1053o2_lower h1 h2
  have hc2 : ((8690939/10000000 : ℚ) : ℝ) ≤ cos1053o2c 2 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 2 - ((8691939/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((8690939/40000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos1053o2c 2 := by
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
    calc ((8690939/40000000 : ℚ) : ℝ)
        = ((1/4 : ℚ) : ℝ) * ((8690939/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((1867117/2000000 : ℚ) : ℝ) ≤ cos1053o2c 3 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 3 - ((1867317/2000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((2074574236987/20000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos1053o2c 3 := by
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
    calc ((2074574236987/20000000000000 : ℚ) : ℝ)
        = ((1111111/10000000 : ℚ) : ℝ) * ((1867117/2000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((5108733/10000000 : ℚ) : ℝ) ≤ cos1053o2c 4 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 4 - ((5109733/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((5108733/160000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos1053o2c 4 := by
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
    calc ((5108733/160000000 : ℚ) : ℝ)
        = ((1/16 : ℚ) : ℝ) * ((5108733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((162907/250000 : ℚ) : ℝ) ≤ cos1053o2c 5 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 5 - ((40733/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((162907/6250000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos1053o2c 5 := by
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
    calc ((162907/6250000 : ℚ) : ℝ)
        = ((1/25 : ℚ) : ℝ) * ((162907/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((1585769/2500000 : ℚ) : ℝ) ≤ cos1053o2c 6 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 6 - ((1586019/2500000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((440490155513/25000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos1053o2c 6 := by
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
    calc ((440490155513/25000000000000 : ℚ) : ℝ)
        = ((277777/10000000 : ℚ) : ℝ) * ((1585769/2500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((9349171/10000000 : ℚ) : ℝ) ≤ cos1053o2c 7 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 7 - ((9350171/10000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((1907988166851/100000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos1053o2c 7 := by
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
    calc ((1907988166851/100000000000000 : ℚ) : ℝ)
        = ((204081/10000000 : ℚ) : ℝ) * ((9349171/10000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((1517/80000 : ℚ) : ℝ) ≤ cos1053o2c 8 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 8 - ((61/3200 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((1517/5120000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos1053o2c 8 := by
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
    calc ((1517/5120000 : ℚ) : ℝ)
        = ((1/64 : ℚ) : ℝ) * ((1517/80000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((3716593/5000000 : ℚ) : ℝ) ≤ cos1053o2c 9 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 9 - ((3717093/5000000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((7169307897/781250000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos1053o2c 9 := by
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
    calc ((7169307897/781250000000 : ℚ) : ℝ)
        = ((1929/156250 : ℚ) : ℝ) * ((3716593/5000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((1176753/1250000 : ℚ) : ℝ) ≤ cos1053o2c 10 := by
    have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 10 - ((588439/625000 : ℚ) : ℝ) :=
      (abs_le.mp cos1053o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((117674123247/12500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos1053o2c 10 := by
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
    calc ((117674123247/12500000000000 : ℚ) : ℝ)
        = ((99999/10000000 : ℚ) : ℝ) * ((1176753/1250000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos1053o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    1000 (by norm_num) hanti hnn psum1053o2_floor
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
  have htail : ((30218877/2000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n) := by
    refine le_trans ?_ habel
    have hC1000 := psum1053o2_1000
    have hx1 : ((169681/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((1/1000000 : ℚ) : ℝ)
          * (((30218877/2000000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((1000:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 1000, cos1053o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw1000lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC1000]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (1000 : ℝ) ^ (-σ) * (2000/1053 + 1/2)
      ≤ ((159/20000000 : ℚ) : ℝ) * (2000/1053 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 1000, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n) := by
    rw [show Finset.Icc (2:ℕ) 1000
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 1000 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos1053o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos1053o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos1053o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos1053o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos1053o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos1053o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos1053o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos1053o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos1053o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos1053o2c 10) := by
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
/-- **Segment positivity at the anchor 1053/2.** -/
theorem segment1053o2_re_pos {σ : ℝ} (h1 : (1/2:ℝ) ≤ σ) (h2 : σ ≤ 2) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((1053:ℕ)):ℝ)/2) * Complex.I)).re := by
  rcases le_total σ (3/5 : ℝ) with hc | hc
  · exact seg1053o2_interval_1 h1 hc
  rcases le_total σ (7/10 : ℝ) with hc2 | hc2
  · exact seg1053o2_interval_2 hc hc2
  rcases le_total σ (9/10 : ℝ) with hc3 | hc3
  · exact seg1053o2_interval_3 hc2 hc3
  rcases le_total σ (11/10 : ℝ) with hc4 | hc4
  · exact seg1053o2_interval_4 hc3 hc4
  rcases le_total σ (7/5 : ℝ) with hc5 | hc5
  · exact seg1053o2_interval_5 hc4 hc5
  rcases le_total σ (17/10 : ℝ) with hc6 | hc6
  · exact seg1053o2_interval_6 hc5 hc6
  exact seg1053o2_interval_7 hc6 h2

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.segment1053o2_re_pos
end AxiomAudit
