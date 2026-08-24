import RequestProject.DVPSegment561o2Core
import RequestProject.DVPWeights289o2
import RequestProject.DVPWeights63
import RequestProject.DVPWeights74
import RequestProject.DVPWeights81

/-!
# Segment positivity at `t = 561/2`: rung-280.5 (seven σ-intervals)
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

set_option maxRecDepth 8192 in
theorem seg561o2_interval_1 {σ : ℝ} (ha : (1/2:ℝ) ≤ σ) (hb : σ ≤ (3/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((561:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta561o2_lower h1 h2
  have hc2 : ((939/1000 : ℚ) : ℝ) ≤ cos561o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 2 - ((5869/6250 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((6195089121/10000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos561o2c 2 := by
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
    calc ((6195089121/10000000000 : ℚ) : ℝ)
        = ((6597539/10000000 : ℚ) : ℝ) * ((939/1000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((479859/500000 : ℚ) : ℝ) ≤ cos561o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 3 - ((479879/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((1241111636331/2500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos561o2c 3 := by
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
    calc ((1241111636331/2500000000000 : ℚ) : ℝ)
        = ((2586409/5000000 : ℚ) : ℝ) * ((479859/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((763561/1000000 : ℚ) : ℝ) ≤ cos561o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 4 - ((763601/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((207724479367/625000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos561o2c 4 := by
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
    calc ((207724479367/625000000000 : ℚ) : ℝ)
        = ((272047/625000 : ℚ) : ℝ) * ((763561/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((294067/500000 : ℚ) : ℝ) ≤ cos561o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 5 - ((294087/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((1119603347569/5000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos561o2c 5 := by
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
    calc ((1119603347569/5000000000000 : ℚ) : ℝ)
        = ((3807307/10000000 : ℚ) : ℝ) * ((294067/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((997763/1000000 : ℚ) : ℝ) ≤ cos561o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 6 - ((997803/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((3405152595481/10000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos561o2c 6 := by
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
    calc ((3405152595481/10000000000000 : ℚ) : ℝ)
        = ((3412787/10000000 : ℚ) : ℝ) * ((997763/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((689947/1000000 : ℚ) : ℝ) ≤ cos561o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 7 - ((689987/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((1073313980709/5000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos561o2c 7 := by
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
    calc ((1073313980709/5000000000000 : ℚ) : ℝ)
        = ((1555647/5000000 : ℚ) : ℝ) * ((689947/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((61879/125000 : ℚ) : ℝ) ≤ cos561o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 8 - ((15471/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((35540141771/250000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos561o2c 8 := by
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
    calc ((35540141771/250000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((61879/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((52639/62500 : ℚ) : ℝ) ≤ cos561o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 9 - ((105283/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((28170339879/125000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos561o2c 9 := by
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
    calc ((28170339879/125000000000 : ℚ) : ℝ)
        = ((535161/2000000 : ℚ) : ℝ) * ((52639/62500 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((34277/125000 : ℚ) : ℝ) ≤ cos561o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 10 - ((17141/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((43049958211/625000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos561o2c 10 := by
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
    calc ((43049958211/625000000000 : ℚ) : ℝ)
        = ((1255943/5000000 : ℚ) : ℝ) * ((34277/125000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos561o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum561o2_floor
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
  have htail : ((71516626097/312500000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum561o2_250
    have hx1 : ((1507557/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((22757/625000 : ℚ) : ℝ)
          * (((3142621/500000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos561o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/561 + 1/2)
      ≤ ((79057/1250000 : ℚ) : ℝ) * (500/561 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos561o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos561o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos561o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos561o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos561o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos561o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos561o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos561o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos561o2c 10) := by
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
theorem seg561o2_interval_2 {σ : ℝ} (ha : (3/5:ℝ) ≤ σ) (hb : σ ≤ (7/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((561:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta561o2_lower h1 h2
  have hc2 : ((939/1000 : ℚ) : ℝ) ≤ cos561o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 2 - ((5869/6250 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((2890111479/5000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos561o2c 2 := by
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
    calc ((2890111479/5000000000 : ℚ) : ℝ)
        = ((3077861/5000000 : ℚ) : ℝ) * ((939/1000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((479859/500000 : ℚ) : ℝ) ≤ cos561o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 3 - ((479879/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((222396891717/500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos561o2c 3 := by
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
    calc ((222396891717/500000000000 : ℚ) : ℝ)
        = ((463463/1000000 : ℚ) : ℝ) * ((479859/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((763561/1000000 : ℚ) : ℝ) ≤ cos561o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 4 - ((763601/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((2893354825251/10000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos561o2c 4 := by
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
    calc ((2893354825251/10000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((763561/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((294067/500000 : ℚ) : ℝ) ≤ cos561o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 5 - ((294087/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((953163189971/5000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos561o2c 5 := by
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
    calc ((953163189971/5000000000000 : ℚ) : ℝ)
        = ((3241313/10000000 : ℚ) : ℝ) * ((294067/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((997763/1000000 : ℚ) : ℝ) ≤ cos561o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 6 - ((997803/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((2846566953087/10000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos561o2c 6 := by
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
    calc ((2846566953087/10000000000000 : ℚ) : ℝ)
        = ((2852949/10000000 : ℚ) : ℝ) * ((997763/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((689947/1000000 : ℚ) : ℝ) ≤ cos561o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 7 - ((689987/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((220880322527/1250000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos561o2c 7 := by
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
    calc ((220880322527/1250000000000 : ℚ) : ℝ)
        = ((320141/1250000 : ℚ) : ℝ) * ((689947/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((61879/125000 : ℚ) : ℝ) ≤ cos561o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 8 - ((15471/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((72168920789/625000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos561o2c 8 := by
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
    calc ((72168920789/625000000000 : ℚ) : ℝ)
        = ((1166291/5000000 : ℚ) : ℝ) * ((61879/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((52639/62500 : ℚ) : ℝ) ≤ cos561o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 9 - ((105283/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((5653375961/31250000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos561o2c 9 := by
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
    calc ((5653375961/31250000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((52639/62500 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((34277/125000 : ℚ) : ℝ) ≤ cos561o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 10 - ((17141/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((34195797787/625000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos561o2c 10 := by
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
    calc ((34195797787/625000000000 : ℚ) : ℝ)
        = ((997631/5000000 : ℚ) : ℝ) * ((34277/125000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos561o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum561o2_floor
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
  have htail : ((82346098063/625000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum561o2_250
    have hx1 : ((148267/625000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((26203/1250000 : ℚ) : ℝ)
          * (((3142621/500000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos561o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/561 + 1/2)
      ≤ ((364113/10000000 : ℚ) : ℝ) * (500/561 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos561o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos561o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos561o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos561o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos561o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos561o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos561o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos561o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos561o2c 10) := by
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
theorem seg561o2_interval_3 {σ : ℝ} (ha : (7/10:ℝ) ≤ σ) (hb : σ ≤ (9/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((561:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta561o2_lower h1 h2
  have hc2 : ((939/1000 : ℚ) : ℝ) ≤ cos561o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 2 - ((5869/6250 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((5031976113/10000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos561o2c 2 := by
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
    calc ((5031976113/10000000000 : ℚ) : ℝ)
        = ((5358867/10000000 : ℚ) : ℝ) * ((939/1000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((479859/500000 : ℚ) : ℝ) ≤ cos561o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 3 - ((479879/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((178527222219/500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos561o2c 3 := by
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
    calc ((178527222219/500000000000 : ℚ) : ℝ)
        = ((372041/1000000 : ℚ) : ℝ) * ((479859/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((763561/1000000 : ℚ) : ℝ) ≤ cos561o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 4 - ((763601/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((438550496789/2000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos561o2c 4 := by
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
    calc ((438550496789/2000000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((763561/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((294067/500000 : ℚ) : ℝ) ≤ cos561o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 5 - ((294087/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((690833076879/5000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos561o2c 5 := by
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
    calc ((690833076879/5000000000000 : ℚ) : ℝ)
        = ((2349237/10000000 : ℚ) : ℝ) * ((294067/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((997763/1000000 : ℚ) : ℝ) ≤ cos561o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 6 - ((997803/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((994629026417/5000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos561o2c 6 := by
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
    calc ((994629026417/5000000000000 : ℚ) : ℝ)
        = ((996859/5000000 : ℚ) : ℝ) * ((997763/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((689947/1000000 : ℚ) : ℝ) ≤ cos561o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 7 - ((689987/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((149670892657/1250000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos561o2c 7 := by
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
    calc ((149670892657/1250000000000 : ℚ) : ℝ)
        = ((216931/1250000 : ℚ) : ℝ) * ((689947/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((61879/125000 : ℚ) : ℝ) ≤ cos561o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 8 - ((15471/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((9522744947/125000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos561o2c 8 := by
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
    calc ((9522744947/125000000000 : ℚ) : ℝ)
        = ((153893/1000000 : ℚ) : ℝ) * ((61879/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((52639/62500 : ℚ) : ℝ) ≤ cos561o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 9 - ((105283/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((14572001731/125000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos561o2c 9 := by
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
    calc ((14572001731/125000000000 : ℚ) : ℝ)
        = ((276829/2000000 : ℚ) : ℝ) * ((52639/62500 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((34277/125000 : ℚ) : ℝ) ≤ cos561o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 10 - ((17141/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((1726086889/50000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos561o2c 10 := by
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
    calc ((1726086889/50000000000 : ℚ) : ℝ)
        = ((50357/400000 : ℚ) : ℝ) * ((34277/125000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos561o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum561o2_floor
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
  have htail : ((218346164459/5000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum561o2_250
    have hx1 : ((233311/1250000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((69479/10000000 : ℚ) : ℝ)
          * (((3142621/500000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos561o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/561 + 1/2)
      ≤ ((1677/80000 : ℚ) : ℝ) * (500/561 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos561o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos561o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos561o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos561o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos561o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos561o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos561o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos561o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos561o2c 10) := by
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
theorem seg561o2_interval_4 {σ : ℝ} (ha : (9/10:ℝ) ≤ σ) (hb : σ ≤ (11/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((561:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta561o2_lower h1 h2
  have hc2 : ((939/1000 : ℚ) : ℝ) ≤ cos561o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 2 - ((5869/6250 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1095147249/2500000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos561o2c 2 := by
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
    calc ((1095147249/2500000000 : ℚ) : ℝ)
        = ((1166291/2500000 : ℚ) : ℝ) * ((939/1000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((479859/500000 : ℚ) : ℝ) ≤ cos561o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 3 - ((479879/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((44784760611/156250000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos561o2c 3 := by
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
    calc ((44784760611/156250000000 : ℚ) : ℝ)
        = ((93329/312500 : ℚ) : ℝ) * ((479859/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((763561/1000000 : ℚ) : ℝ) ≤ cos561o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 4 - ((763601/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((207724479367/1250000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos561o2c 4 := by
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
    calc ((207724479367/1250000000000 : ℚ) : ℝ)
        = ((272047/1250000 : ℚ) : ℝ) * ((763561/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((294067/500000 : ℚ) : ℝ) ≤ cos561o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 5 - ((294087/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((500701705493/5000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos561o2c 5 := by
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
    calc ((500701705493/5000000000000 : ℚ) : ℝ)
        = ((1702679/10000000 : ℚ) : ℝ) * ((294067/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((997763/1000000 : ℚ) : ℝ) ≤ cos561o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 6 - ((997803/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((86884204277/625000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos561o2c 6 := by
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
    calc ((86884204277/625000000000 : ℚ) : ℝ)
        = ((87079/625000 : ℚ) : ℝ) * ((997763/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((689947/1000000 : ℚ) : ℝ) ≤ cos561o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 7 - ((689987/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((405674347113/5000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos561o2c 7 := by
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
    calc ((405674347113/5000000000000 : ℚ) : ℝ)
        = ((587979/5000000 : ℚ) : ℝ) * ((689947/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((61879/125000 : ℚ) : ℝ) ≤ cos561o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 8 - ((15471/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((12565335377/250000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos561o2c 8 := by
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
    calc ((12565335377/250000000000 : ℚ) : ℝ)
        = ((203063/2000000 : ℚ) : ℝ) * ((61879/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((52639/62500 : ℚ) : ℝ) ≤ cos561o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 9 - ((105283/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((9390113293/125000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos561o2c 9 := by
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
    calc ((9390113293/125000000000 : ℚ) : ℝ)
        = ((178387/2000000 : ℚ) : ℝ) * ((52639/62500 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((34277/125000 : ℚ) : ℝ) ≤ cos561o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 10 - ((17141/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((3403397607/156250000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos561o2c 10 := by
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
    calc ((3403397607/156250000000 : ℚ) : ℝ)
        = ((99291/1250000 : ℚ) : ℝ) * ((34277/125000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos561o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum561o2_floor
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
  have htail : ((18092069097/1250000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum561o2_250
    have hx1 : ((577719/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((5757/2500000 : ℚ) : ℝ)
          * (((3142621/500000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos561o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/561 + 1/2)
      ≤ ((1737/250000 : ℚ) : ℝ) * (500/561 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos561o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos561o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos561o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos561o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos561o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos561o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos561o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos561o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos561o2c 10) := by
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
theorem seg561o2_interval_5 {σ : ℝ} (ha : (11/10:ℝ) ≤ σ) (hb : σ ≤ (7/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((561:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta561o2_lower h1 h2
  have hc2 : ((939/1000 : ℚ) : ℝ) ≤ cos561o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 2 - ((5869/6250 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((3558144249/10000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos561o2c 2 := by
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
    calc ((3558144249/10000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((939/1000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((479859/500000 : ℚ) : ℝ) ≤ cos561o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 3 - ((479879/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((51536376741/250000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos561o2c 3 := by
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
    calc ((51536376741/250000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((479859/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((763561/1000000 : ℚ) : ℝ) ≤ cos561o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 4 - ((763601/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((34261745631/312500000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos561o2c 4 := by
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
    calc ((34261745631/312500000000 : ℚ) : ℝ)
        = ((44871/312500 : ℚ) : ℝ) * ((763561/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((294067/500000 : ℚ) : ℝ) ≤ cos561o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 5 - ((294087/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((308950024937/5000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos561o2c 5 := by
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
    calc ((308950024937/5000000000000 : ℚ) : ℝ)
        = ((1050611/10000000 : ℚ) : ℝ) * ((294067/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((997763/1000000 : ℚ) : ℝ) ≤ cos561o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 6 - ((997803/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((203027808529/2500000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos561o2c 6 := by
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
    calc ((203027808529/2500000000000 : ℚ) : ℝ)
        = ((203483/2500000 : ℚ) : ℝ) * ((997763/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((689947/1000000 : ℚ) : ℝ) ≤ cos561o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 7 - ((689987/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((452561765339/10000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos561o2c 7 := by
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
    calc ((452561765339/10000000000000 : ℚ) : ℝ)
        = ((655937/10000000 : ℚ) : ℝ) * ((689947/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((61879/125000 : ℚ) : ℝ) ≤ cos561o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 8 - ((15471/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((16833996313/625000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos561o2c 8 := by
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
    calc ((16833996313/625000000000 : ℚ) : ℝ)
        = ((272047/5000000 : ℚ) : ℝ) * ((61879/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((52639/62500 : ℚ) : ℝ) ≤ cos561o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 9 - ((105283/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((24286634459/625000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos561o2c 9 := by
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
    calc ((24286634459/625000000000 : ℚ) : ℝ)
        = ((461381/10000000 : ℚ) : ℝ) * ((52639/62500 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((34277/125000 : ℚ) : ℝ) ≤ cos561o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 10 - ((17141/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((13645913639/1250000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos561o2c 10 := by
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
    calc ((13645913639/1250000000000 : ℚ) : ℝ)
        = ((398107/10000000 : ℚ) : ℝ) * ((34277/125000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos561o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum561o2_floor
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
  have htail : ((6904338337/2500000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum561o2_250
    have hx1 : ((715267/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((2197/5000000 : ℚ) : ℝ)
          * (((3142621/500000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos561o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/561 + 1/2)
      ≤ ((23029/10000000 : ℚ) : ℝ) * (500/561 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos561o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos561o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos561o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos561o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos561o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos561o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos561o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos561o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos561o2c 10) := by
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
theorem seg561o2_interval_6 {σ : ℝ} (ha : (7/5:ℝ) ≤ σ) (hb : σ ≤ (17/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((561:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta561o2_lower h1 h2
  have hc2 : ((939/1000 : ℚ) : ℝ) ≤ cos561o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 2 - ((5869/6250 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((2890111479/10000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos561o2c 2 := by
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
    calc ((2890111479/10000000000 : ℚ) : ℝ)
        = ((3077861/10000000 : ℚ) : ℝ) * ((939/1000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((479859/500000 : ℚ) : ℝ) ≤ cos561o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 3 - ((479879/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((185330663121/1250000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos561o2c 3 := by
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
    calc ((185330663121/1250000000000 : ℚ) : ℝ)
        = ((386219/2500000 : ℚ) : ℝ) * ((479859/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((763561/1000000 : ℚ) : ℝ) ≤ cos561o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 4 - ((763601/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((361669066821/5000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos561o2c 4 := by
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
    calc ((361669066821/5000000000000 : ℚ) : ℝ)
        = ((473661/5000000 : ℚ) : ℝ) * ((763561/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((294067/500000 : ℚ) : ℝ) ≤ cos561o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 5 - ((294087/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((95316230777/2500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos561o2c 5 := by
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
    calc ((95316230777/2500000000000 : ℚ) : ℝ)
        = ((324131/5000000 : ℚ) : ℝ) * ((294067/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((997763/1000000 : ℚ) : ℝ) ≤ cos561o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 6 - ((997803/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((474427326633/10000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos561o2c 6 := by
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
    calc ((474427326633/10000000000000 : ℚ) : ℝ)
        = ((475491/10000000 : ℚ) : ℝ) * ((997763/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((689947/1000000 : ℚ) : ℝ) ≤ cos561o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 7 - ((689987/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((2019474869/80000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos561o2c 7 := by
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
    calc ((2019474869/80000000000 : ℚ) : ℝ)
        = ((2927/80000 : ℚ) : ℝ) * ((689947/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((61879/125000 : ℚ) : ℝ) ≤ cos561o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 8 - ((15471/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((4510545947/312500000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos561o2c 8 := by
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
    calc ((4510545947/312500000000 : ℚ) : ℝ)
        = ((72893/2500000 : ℚ) : ℝ) * ((61879/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((52639/62500 : ℚ) : ℝ) ≤ cos561o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 9 - ((105283/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((1570379287/78125000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos561o2c 9 := by
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
    calc ((1570379287/78125000000 : ℚ) : ℝ)
        = ((29833/1250000 : ℚ) : ℝ) * ((52639/62500 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((34277/125000 : ℚ) : ℝ) ≤ cos561o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 10 - ((17141/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((3419576351/625000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos561o2c 10 := by
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
    calc ((3419576351/625000000000 : ℚ) : ℝ)
        = ((99763/5000000 : ℚ) : ℝ) * ((34277/125000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos561o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum561o2_floor
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
  have htail : ((1316758199/2500000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum561o2_250
    have hx1 : ((174189/5000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((419/5000000 : ℚ) : ℝ)
          * (((3142621/500000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos561o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/561 + 1/2)
      ≤ ((879/2000000 : ℚ) : ℝ) * (500/561 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos561o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos561o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos561o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos561o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos561o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos561o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos561o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos561o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos561o2c 10) := by
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
theorem seg561o2_interval_7 {σ : ℝ} (ha : (17/10:ℝ) ≤ σ) (hb : σ ≤ (2:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((561:ℕ)):ℝ)/2) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta561o2_lower h1 h2
  have hc2 : ((939/1000 : ℚ) : ℝ) ≤ cos561o2c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 2 - ((5869/6250 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((939/4000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos561o2c 2 := by
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
    calc ((939/4000 : ℚ) : ℝ)
        = ((1/4 : ℚ) : ℝ) * ((939/1000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((479859/500000 : ℚ) : ℝ) ≤ cos561o2c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 3 - ((479879/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((533176613349/5000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos561o2c 3 := by
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
    calc ((533176613349/5000000000000 : ℚ) : ℝ)
        = ((1111111/10000000 : ℚ) : ℝ) * ((479859/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((763561/1000000 : ℚ) : ℝ) ≤ cos561o2c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 4 - ((763601/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((763561/16000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos561o2c 4 := by
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
    calc ((763561/16000000 : ℚ) : ℝ)
        = ((1/16 : ℚ) : ℝ) * ((763561/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((294067/500000 : ℚ) : ℝ) ≤ cos561o2c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 5 - ((294087/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((294067/12500000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos561o2c 5 := by
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
    calc ((294067/12500000 : ℚ) : ℝ)
        = ((1/25 : ℚ) : ℝ) * ((294067/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((997763/1000000 : ℚ) : ℝ) ≤ cos561o2c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 6 - ((997803/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((277155612851/10000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos561o2c 6 := by
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
    calc ((277155612851/10000000000000 : ℚ) : ℝ)
        = ((277777/10000000 : ℚ) : ℝ) * ((997763/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((689947/1000000 : ℚ) : ℝ) ≤ cos561o2c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 7 - ((689987/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((140805073707/10000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos561o2c 7 := by
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
    calc ((140805073707/10000000000000 : ℚ) : ℝ)
        = ((204081/10000000 : ℚ) : ℝ) * ((689947/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((61879/125000 : ℚ) : ℝ) ≤ cos561o2c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 8 - ((15471/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((61879/8000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos561o2c 8 := by
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
    calc ((61879/8000000 : ℚ) : ℝ)
        = ((1/64 : ℚ) : ℝ) * ((61879/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((52639/62500 : ℚ) : ℝ) ≤ cos561o2c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 9 - ((105283/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((101540631/9765625000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos561o2c 9 := by
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
    calc ((101540631/9765625000 : ℚ) : ℝ)
        = ((1929/156250 : ℚ) : ℝ) * ((52639/62500 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((34277/125000 : ℚ) : ℝ) ≤ cos561o2c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 10 - ((17141/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos561o2_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((3427665723/1250000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos561o2c 10 := by
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
    calc ((3427665723/1250000000000 : ℚ) : ℝ)
        = ((99999/10000000 : ℚ) : ℝ) * ((34277/125000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos561o2c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((0 : ℚ) : ℝ))
    250 (by norm_num) hanti hnn psum561o2_floor
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
  have htail : ((3142621/31250000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n) := by
    refine le_trans ?_ habel
    have hC250 := psum561o2_250
    have hx1 : ((169681/10000000 : ℚ) : ℝ) * ((0 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((1/62500 : ℚ) : ℝ)
          * (((3142621/500000 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))
        ≤ ((250:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 250, cos561o2c k)
            - ((0 : ℚ) : ℝ)) := by
      apply mul_le_mul hw250lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC250]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (250 : ℝ) ^ (-σ) * (500/561 + 1/2)
      ≤ ((839/10000000 : ℚ) : ℝ) * (500/561 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 250, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n) := by
    rw [show Finset.Icc (2:ℕ) 250
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 250 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos561o2c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos561o2c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos561o2c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos561o2c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos561o2c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos561o2c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos561o2c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos561o2c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos561o2c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos561o2c 10) := by
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
/-- **Segment positivity at the half-integer anchor 561/2.** -/
theorem segment561o2_re_pos {σ : ℝ} (h1 : (1/2:ℝ) ≤ σ) (h2 : σ ≤ 2) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ↑((((561:ℕ)):ℝ)/2) * Complex.I)).re := by
  rcases le_total σ (3/5 : ℝ) with hc | hc
  · exact seg561o2_interval_1 h1 hc
  rcases le_total σ (7/10 : ℝ) with hc2 | hc2
  · exact seg561o2_interval_2 hc hc2
  rcases le_total σ (9/10 : ℝ) with hc3 | hc3
  · exact seg561o2_interval_3 hc2 hc3
  rcases le_total σ (11/10 : ℝ) with hc4 | hc4
  · exact seg561o2_interval_4 hc3 hc4
  rcases le_total σ (7/5 : ℝ) with hc5 | hc5
  · exact seg561o2_interval_5 hc4 hc5
  rcases le_total σ (17/10 : ℝ) with hc6 | hc6
  · exact seg561o2_interval_6 hc5 hc6
  exact seg561o2_interval_7 hc6 h2

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.segment561o2_re_pos
end AxiomAudit
