import RequestProject.DVPSegment74Core
import RequestProject.DVPWeights63
import RequestProject.DVPWeights74

/-!
# Segment positivity at `t = 74`: rung-74
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem seg74_interval_1 {σ : ℝ} (ha : (1/2:ℝ) ≤ σ) (hb : σ ≤ (7/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((74:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta74_lower h1 h2
  have hc2 : ((516999/1000000 : ℚ) : ℝ) ≤ cos74c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 2 - ((517039/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1591251059139/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos74c 2 := by
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
    calc ((1591251059139/5000000000000 : ℚ) : ℝ)
        = ((3077861/5000000 : ℚ) : ℝ) * ((516999/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((115887/125000 : ℚ) : ℝ) ≤ cos74c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 3 - ((28973/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((53709336681/125000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos74c 3 := by
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
    calc ((53709336681/125000000000 : ℚ) : ℝ)
        = ((463463/1000000 : ℚ) : ℝ) * ((115887/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((-232691/500000 : ℚ) : ℝ) ≤ cos74c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 4 - ((-232671/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((-1163455232691/5000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos74c 4 := by
    have hw : ((4:ℕ) : ℝ) ^ (-σ) ≤ ((5000001/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_4_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((4:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc4).2
      (by push_cast; norm_num)
    calc ((-1163455232691/5000000000000 : ℚ) : ℝ)
        = ((5000001/10000000 : ℚ) : ℝ) * ((-232691/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((960429/1000000 : ℚ) : ℝ) ≤ cos74c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 5 - ((960469/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((3113051003277/10000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos74c 5 := by
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
    calc ((3113051003277/10000000000000 : ℚ) : ℝ)
        = ((3241313/10000000 : ℚ) : ℝ) * ((960429/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((32003/40000 : ℚ) : ℝ) ≤ cos74c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 6 - ((160023/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((91302926847/400000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos74c 6 := by
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
    calc ((91302926847/400000000000 : ℚ) : ℝ)
        = ((2852949/10000000 : ℚ) : ℝ) * ((32003/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((217451/250000 : ℚ) : ℝ) ≤ cos74c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 7 - ((217461/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((69614980591/312500000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos74c 7 := by
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
    calc ((69614980591/312500000000 : ℚ) : ℝ)
        = ((320141/1250000 : ℚ) : ℝ) * ((217451/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-499139/500000 : ℚ) : ℝ) ≤ cos74c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 8 - ((-499119/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-882361452613/2500000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos74c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((1767767/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-882361452613/2500000000000 : ℚ) : ℝ)
        = ((1767767/5000000 : ℚ) : ℝ) * ((-499139/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((719123/1000000 : ℚ) : ℝ) ≤ cos74c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 9 - ((719163/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((77233091077/500000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos74c 9 := by
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
    calc ((77233091077/500000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((719123/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((734849/1000000 : ℚ) : ℝ) ≤ cos74c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 10 - ((734889/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((733108142719/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos74c 10 := by
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
    calc ((733108142719/5000000000000 : ℚ) : ℝ)
        = ((997631/5000000 : ℚ) : ℝ) * ((734849/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos74c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-727/12500 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum74_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((1507557/5000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_5).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw100lo : ((398107/10000000 : ℚ) : ℝ) ≤ ((100:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_100_7).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((170094626937/2000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n) := by
    refine le_trans ?_ habel
    have hC100 := psum74_100
    have hx1 : ((1507557/5000000 : ℚ) : ℝ) * ((-727/12500 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-727/12500 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((398107/10000000 : ℚ) : ℝ)
          * (((503723/200000 : ℚ) : ℝ) - ((-727/12500 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos74c k)
            - ((-727/12500 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/74 + 1/2)
      ≤ ((1/10 : ℚ) : ℝ) * (100/74 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_100_5).2
    have hexp : (-((((5:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(1/2) : ℝ) := by
      norm_num
    have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (100 : ℝ) ^ (-σ - 2) ≤ ((1/100000 : ℚ) : ℝ) := by
    have hbr := (wbr_100_25).2
    have hexp : (-((((25:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(5/2) : ℝ) := by
      norm_num
    have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (100 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((1/1000 : ℚ) : ℝ) / (3/2) := by
    have hnum : (100 : ℝ) ^ (-σ - 1) ≤ ((1/1000 : ℚ) : ℝ) := by
      have hbr := (wbr_100_15).2
      have hexp : (-((((15:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(3/2) : ℝ) := by
        norm_num
      have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos74c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos74c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos74c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos74c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos74c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos74c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos74c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos74c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos74c 10) := by
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

theorem seg74_interval_2 {σ : ℝ} (ha : (7/10:ℝ) ≤ σ) (hb : σ ≤ (9/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((74:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta74_lower h1 h2
  have hc2 : ((516999/1000000 : ℚ) : ℝ) ≤ cos74c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 2 - ((517039/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((2770528880133/10000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos74c 2 := by
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
    calc ((2770528880133/10000000000000 : ℚ) : ℝ)
        = ((5358867/10000000 : ℚ) : ℝ) * ((516999/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((115887/125000 : ℚ) : ℝ) ≤ cos74c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 3 - ((28973/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((43114715367/125000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos74c 3 := by
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
    calc ((43114715367/125000000000 : ℚ) : ℝ)
        = ((372041/1000000 : ℚ) : ℝ) * ((115887/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((-232691/500000 : ℚ) : ℝ) ≤ cos74c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 4 - ((-232671/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((-220433536193/1250000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos74c 4 := by
    have hw : ((4:ℕ) : ℝ) ^ (-σ) ≤ ((947323/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_4_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((4:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc4).2
      (by push_cast; norm_num)
    calc ((-220433536193/1250000000000 : ℚ) : ℝ)
        = ((947323/2500000 : ℚ) : ℝ) * ((-232691/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((960429/1000000 : ℚ) : ℝ) ≤ cos74c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 5 - ((960469/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((2256275342673/10000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos74c 5 := by
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
    calc ((2256275342673/10000000000000 : ℚ) : ℝ)
        = ((2349237/10000000 : ℚ) : ℝ) * ((960429/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((32003/40000 : ℚ) : ℝ) ≤ cos74c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 6 - ((160023/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((31902478577/200000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos74c 6 := by
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
    calc ((31902478577/200000000000 : ℚ) : ℝ)
        = ((996859/5000000 : ℚ) : ℝ) * ((32003/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((217451/250000 : ℚ) : ℝ) ≤ cos74c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 7 - ((217461/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((47171862881/312500000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos74c 7 := by
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
    calc ((47171862881/312500000000 : ℚ) : ℝ)
        = ((216931/1250000 : ℚ) : ℝ) * ((217451/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-499139/500000 : ℚ) : ℝ) ≤ cos74c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 8 - ((-499119/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-1164283146037/5000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos74c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((2332583/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-1164283146037/5000000000000 : ℚ) : ℝ)
        = ((2332583/10000000 : ℚ) : ℝ) * ((-499139/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((719123/1000000 : ℚ) : ℝ) ≤ cos74c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 9 - ((719163/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((199074100967/2000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos74c 9 := by
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
    calc ((199074100967/2000000000000 : ℚ) : ℝ)
        = ((276829/2000000 : ℚ) : ℝ) * ((719123/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((734849/1000000 : ℚ) : ℝ) ≤ cos74c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 10 - ((734889/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((37004791093/400000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos74c 10 := by
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
    calc ((37004791093/400000000000 : ℚ) : ℝ)
        = ((50357/400000 : ℚ) : ℝ) * ((734849/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos74c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-727/12500 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum74_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((233311/1250000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_7).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw100lo : ((158489/10000000 : ℚ) : ℝ) ≤ ((100:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_100_9).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((59967110179/2000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n) := by
    refine le_trans ?_ habel
    have hC100 := psum74_100
    have hx1 : ((233311/1250000 : ℚ) : ℝ) * ((-727/12500 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-727/12500 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((158489/10000000 : ℚ) : ℝ)
          * (((503723/200000 : ℚ) : ℝ) - ((-727/12500 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos74c k)
            - ((-727/12500 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/74 + 1/2)
      ≤ ((99527/2500000 : ℚ) : ℝ) * (100/74 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_100_7).2
    have hexp : (-((((7:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(7/10) : ℝ) := by
      norm_num
    have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (100 : ℝ) ^ (-σ - 2) ≤ ((1/250000 : ℚ) : ℝ) := by
    have hbr := (wbr_100_27).2
    have hexp : (-((((27:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(27/10) : ℝ) := by
      norm_num
    have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (100 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((1991/5000000 : ℚ) : ℝ) / (17/10) := by
    have hnum : (100 : ℝ) ^ (-σ - 1) ≤ ((1991/5000000 : ℚ) : ℝ) := by
      have hbr := (wbr_100_17).2
      have hexp : (-((((17:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(17/10) : ℝ) := by
        norm_num
      have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos74c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos74c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos74c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos74c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos74c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos74c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos74c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos74c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos74c 10) := by
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

theorem seg74_interval_3 {σ : ℝ} (ha : (9/10:ℝ) ≤ σ) (hb : σ ≤ (11/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((74:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta74_lower h1 h2
  have hc2 : ((516999/1000000 : ℚ) : ℝ) ≤ cos74c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 2 - ((517039/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((602971280709/2500000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos74c 2 := by
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
    calc ((602971280709/2500000000000 : ℚ) : ℝ)
        = ((1166291/2500000 : ℚ) : ℝ) * ((516999/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((115887/125000 : ℚ) : ℝ) ≤ cos74c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 3 - ((28973/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((10815617823/39062500000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos74c 3 := by
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
    calc ((10815617823/39062500000 : ℚ) : ℝ)
        = ((93329/312500 : ℚ) : ℝ) * ((115887/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((-232691/500000 : ℚ) : ℝ) ≤ cos74c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 4 - ((-232671/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((-334114724243/2500000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos74c 4 := by
    have hw : ((4:ℕ) : ℝ) ^ (-σ) ≤ ((1435873/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_4_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((4:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc4).2
      (by push_cast; norm_num)
    calc ((-334114724243/2500000000000 : ℚ) : ℝ)
        = ((1435873/5000000 : ℚ) : ℝ) * ((-232691/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((960429/1000000 : ℚ) : ℝ) ≤ cos74c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 5 - ((960469/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((1635302289291/10000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos74c 5 := by
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
    calc ((1635302289291/10000000000000 : ℚ) : ℝ)
        = ((1702679/10000000 : ℚ) : ℝ) * ((960429/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((32003/40000 : ℚ) : ℝ) ≤ cos74c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 6 - ((160023/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((2786789237/25000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos74c 6 := by
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
    calc ((2786789237/25000000000 : ℚ) : ℝ)
        = ((87079/625000 : ℚ) : ℝ) * ((32003/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((217451/250000 : ℚ) : ℝ) ≤ cos74c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 7 - ((217461/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((127856621529/1250000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos74c 7 := by
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
    calc ((127856621529/1250000000000 : ℚ) : ℝ)
        = ((587979/5000000 : ℚ) : ℝ) * ((217451/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-499139/500000 : ℚ) : ℝ) ≤ cos74c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 8 - ((-499119/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-768140480409/5000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos74c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((1538931/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-768140480409/5000000000000 : ℚ) : ℝ)
        = ((1538931/10000000 : ℚ) : ℝ) * ((-499139/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((719123/1000000 : ℚ) : ℝ) ≤ cos74c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 9 - ((719163/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((128282194601/2000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos74c 9 := by
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
    calc ((128282194601/2000000000000 : ℚ) : ℝ)
        = ((178387/2000000 : ℚ) : ℝ) * ((719123/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((734849/1000000 : ℚ) : ℝ) ≤ cos74c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 10 - ((734889/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((72963892059/1250000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos74c 10 := by
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
    calc ((72963892059/1250000000000 : ℚ) : ℝ)
        = ((99291/1250000 : ℚ) : ℝ) * ((734849/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos74c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-727/12500 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum74_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((577719/5000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_9).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw100lo : ((12619/2000000 : ℚ) : ℝ) ≤ ((100:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_100_11).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((19076268909/2000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n) := by
    refine le_trans ?_ habel
    have hC100 := psum74_100
    have hx1 : ((577719/5000000 : ℚ) : ℝ) * ((-727/12500 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-727/12500 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((12619/2000000 : ℚ) : ℝ)
          * (((503723/200000 : ℚ) : ℝ) - ((-727/12500 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos74c k)
            - ((-727/12500 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/74 + 1/2)
      ≤ ((15849/1000000 : ℚ) : ℝ) * (100/74 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_100_9).2
    have hexp : (-((((9:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(9/10) : ℝ) := by
      norm_num
    have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (100 : ℝ) ^ (-σ - 2) ≤ ((1/625000 : ℚ) : ℝ) := by
    have hbr := (wbr_100_29).2
    have hexp : (-((((29:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(29/10) : ℝ) := by
      norm_num
    have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (100 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((317/2000000 : ℚ) : ℝ) / (19/10) := by
    have hnum : (100 : ℝ) ^ (-σ - 1) ≤ ((317/2000000 : ℚ) : ℝ) := by
      have hbr := (wbr_100_19).2
      have hexp : (-((((19:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(19/10) : ℝ) := by
        norm_num
      have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos74c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos74c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos74c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos74c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos74c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos74c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos74c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos74c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos74c 10) := by
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

theorem seg74_interval_4 {σ : ℝ} (ha : (11/10:ℝ) ≤ σ) (hb : σ ≤ (7/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((74:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta74_lower h1 h2
  have hc2 : ((516999/1000000 : ℚ) : ℝ) ≤ cos74c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 2 - ((517039/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1959059657709/10000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos74c 2 := by
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
    calc ((1959059657709/10000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((516999/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((115887/125000 : ℚ) : ℝ) ≤ cos74c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 3 - ((28973/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((12446147913/62500000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos74c 3 := by
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
    calc ((12446147913/62500000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((115887/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((-232691/500000 : ℚ) : ℝ) ≤ cos74c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 4 - ((-232671/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((-506423340507/5000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos74c 4 := by
    have hw : ((4:ℕ) : ℝ) ^ (-σ) ≤ ((2176377/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_4_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((4:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc4).2
      (by push_cast; norm_num)
    calc ((-506423340507/5000000000000 : ℚ) : ℝ)
        = ((2176377/10000000 : ℚ) : ℝ) * ((-232691/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((960429/1000000 : ℚ) : ℝ) ≤ cos74c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 5 - ((960469/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((1009037272119/10000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos74c 5 := by
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
    calc ((1009037272119/10000000000000 : ℚ) : ℝ)
        = ((1050611/10000000 : ℚ) : ℝ) * ((960429/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((32003/40000 : ℚ) : ℝ) ≤ cos74c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 6 - ((160023/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((6512066449/100000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos74c 6 := by
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
    calc ((6512066449/100000000000 : ℚ) : ℝ)
        = ((203483/2500000 : ℚ) : ℝ) * ((32003/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((217451/250000 : ℚ) : ℝ) ≤ cos74c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 7 - ((217461/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((142634156587/2500000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos74c 7 := by
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
    calc ((142634156587/2500000000000 : ℚ) : ℝ)
        = ((655937/10000000 : ℚ) : ℝ) * ((217451/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-499139/500000 : ℚ) : ℝ) ≤ cos74c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 8 - ((-499119/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-126695953231/1250000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos74c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((253829/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-126695953231/1250000000000 : ℚ) : ℝ)
        = ((253829/2500000 : ℚ) : ℝ) * ((-499139/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((719123/1000000 : ℚ) : ℝ) ≤ cos74c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 9 - ((719163/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((331789688863/10000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos74c 9 := by
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
    calc ((331789688863/10000000000000 : ℚ) : ℝ)
        = ((461381/10000000 : ℚ) : ℝ) * ((719123/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((734849/1000000 : ℚ) : ℝ) ≤ cos74c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 10 - ((734889/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((292548530843/10000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos74c 10 := by
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
    calc ((292548530843/10000000000000 : ℚ) : ℝ)
        = ((398107/10000000 : ℚ) : ℝ) * ((734849/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos74c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-727/12500 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum74_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((715267/10000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_11).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw100lo : ((1981/1250000 : ℚ) : ℝ) ≤ ((100:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_100_14).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((-19079963/250000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n) := by
    refine le_trans ?_ habel
    have hC100 := psum74_100
    have hx1 : ((715267/10000000 : ℚ) : ℝ) * ((-727/12500 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-727/12500 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((1981/1250000 : ℚ) : ℝ)
          * (((503723/200000 : ℚ) : ℝ) - ((-727/12500 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos74c k)
            - ((-727/12500 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/74 + 1/2)
      ≤ ((7887/1250000 : ℚ) : ℝ) * (100/74 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_100_11).2
    have hexp : (-((((11:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(11/10) : ℝ) := by
      norm_num
    have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (100 : ℝ) ^ (-σ - 2) ≤ ((7/10000000 : ℚ) : ℝ) := by
    have hbr := (wbr_100_31).2
    have hexp : (-((((31:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(31/10) : ℝ) := by
      norm_num
    have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (100 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((631/10000000 : ℚ) : ℝ) / (21/10) := by
    have hnum : (100 : ℝ) ^ (-σ - 1) ≤ ((631/10000000 : ℚ) : ℝ) := by
      have hbr := (wbr_100_21).2
      have hexp : (-((((21:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(21/10) : ℝ) := by
        norm_num
      have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos74c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos74c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos74c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos74c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos74c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos74c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos74c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos74c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos74c 10) := by
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

theorem seg74_interval_5 {σ : ℝ} (ha : (7/5:ℝ) ≤ σ) (hb : σ ≤ (17/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((74:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta74_lower h1 h2
  have hc2 : ((516999/1000000 : ℚ) : ℝ) ≤ cos74c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 2 - ((517039/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1591251059139/10000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos74c 2 := by
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
    calc ((1591251059139/10000000000000 : ℚ) : ℝ)
        = ((3077861/10000000 : ℚ) : ℝ) * ((516999/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((115887/125000 : ℚ) : ℝ) ≤ cos74c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 3 - ((28973/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((44757761253/312500000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos74c 3 := by
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
    calc ((44757761253/312500000000 : ℚ) : ℝ)
        = ((386219/2500000 : ℚ) : ℝ) * ((115887/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((-232691/500000 : ℚ) : ℝ) ≤ cos74c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 4 - ((-232671/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((-334114724243/5000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos74c 4 := by
    have hw : ((4:ℕ) : ℝ) ^ (-σ) ≤ ((1435873/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_4_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((4:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc4).2
      (by push_cast; norm_num)
    calc ((-334114724243/5000000000000 : ℚ) : ℝ)
        = ((1435873/10000000 : ℚ) : ℝ) * ((-232691/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((960429/1000000 : ℚ) : ℝ) ≤ cos74c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 5 - ((960469/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((311304812199/5000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos74c 5 := by
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
    calc ((311304812199/5000000000000 : ℚ) : ℝ)
        = ((324131/5000000 : ℚ) : ℝ) * ((960429/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((32003/40000 : ℚ) : ℝ) ≤ cos74c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 6 - ((160023/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((15217138473/400000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos74c 6 := by
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
    calc ((15217138473/400000000000 : ℚ) : ℝ)
        = ((475491/10000000 : ℚ) : ℝ) * ((32003/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((217451/250000 : ℚ) : ℝ) ≤ cos74c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 7 - ((217461/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((636479077/20000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos74c 7 := by
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
    calc ((636479077/20000000000 : ℚ) : ℝ)
        = ((2927/80000 : ℚ) : ℝ) * ((217451/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-499139/500000 : ℚ) : ℝ) ≤ cos74c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 8 - ((-499119/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-54315806841/1000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos74c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((108819/2000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-54315806841/1000000000000 : ℚ) : ℝ)
        = ((108819/2000000 : ℚ) : ℝ) * ((-499139/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((719123/1000000 : ℚ) : ℝ) ≤ cos74c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 9 - ((719163/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((21453596459/1250000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos74c 9 := by
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
    calc ((21453596459/1250000000000 : ℚ) : ℝ)
        = ((29833/1250000 : ℚ) : ℝ) * ((719123/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((734849/1000000 : ℚ) : ℝ) ≤ cos74c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 10 - ((734889/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((73310740787/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos74c 10 := by
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
    calc ((73310740787/5000000000000 : ℚ) : ℝ)
        = ((99763/5000000 : ℚ) : ℝ) * ((734849/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos74c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-727/12500 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum74_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((174189/5000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_14).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw100lo : ((3981/10000000 : ℚ) : ℝ) ≤ ((100:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_100_17).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((-2000704641/2000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n) := by
    refine le_trans ?_ habel
    have hC100 := psum74_100
    have hx1 : ((174189/5000000 : ℚ) : ℝ) * ((-727/12500 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-727/12500 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((3981/10000000 : ℚ) : ℝ)
          * (((503723/200000 : ℚ) : ℝ) - ((-727/12500 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos74c k)
            - ((-727/12500 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/74 + 1/2)
      ≤ ((15849/10000000 : ℚ) : ℝ) * (100/74 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_100_14).2
    have hexp : (-((((14:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(7/5) : ℝ) := by
      norm_num
    have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (100 : ℝ) ^ (-σ - 2) ≤ ((1/5000000 : ℚ) : ℝ) := by
    have hbr := (wbr_100_34).2
    have hexp : (-((((34:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(17/5) : ℝ) := by
      norm_num
    have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (100 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((159/10000000 : ℚ) : ℝ) / (12/5) := by
    have hnum : (100 : ℝ) ^ (-σ - 1) ≤ ((159/10000000 : ℚ) : ℝ) := by
      have hbr := (wbr_100_24).2
      have hexp : (-((((24:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(12/5) : ℝ) := by
        norm_num
      have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos74c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos74c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos74c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos74c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos74c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos74c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos74c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos74c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos74c 10) := by
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

theorem seg74_interval_6 {σ : ℝ} (ha : (17/10:ℝ) ≤ σ) (hb : σ ≤ (2:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((74:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta74_lower h1 h2
  have hc2 : ((516999/1000000 : ℚ) : ℝ) ≤ cos74c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 2 - ((517039/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((516999/4000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos74c 2 := by
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
    calc ((516999/4000000 : ℚ) : ℝ)
        = ((1/4 : ℚ) : ℝ) * ((516999/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((115887/125000 : ℚ) : ℝ) ≤ cos74c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 3 - ((28973/31250 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((128763320457/1250000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos74c 3 := by
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
    calc ((128763320457/1250000000000 : ℚ) : ℝ)
        = ((1111111/10000000 : ℚ) : ℝ) * ((115887/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((-232691/500000 : ℚ) : ℝ) ≤ cos74c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 4 - ((-232671/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((-220433536193/5000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos74c 4 := by
    have hw : ((4:ℕ) : ℝ) ^ (-σ) ≤ ((947323/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_4_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((4:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc4).2
      (by push_cast; norm_num)
    calc ((-220433536193/5000000000000 : ℚ) : ℝ)
        = ((947323/10000000 : ℚ) : ℝ) * ((-232691/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((960429/1000000 : ℚ) : ℝ) ≤ cos74c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 5 - ((960469/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((960429/25000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos74c 5 := by
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
    calc ((960429/25000000 : ℚ) : ℝ)
        = ((1/25 : ℚ) : ℝ) * ((960429/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((32003/40000 : ℚ) : ℝ) ≤ cos74c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 6 - ((160023/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((8889697331/400000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos74c 6 := by
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
    calc ((8889697331/400000000000 : ℚ) : ℝ)
        = ((277777/10000000 : ℚ) : ℝ) * ((32003/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((217451/250000 : ℚ) : ℝ) ≤ cos74c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 7 - ((217461/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((44377617531/2500000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos74c 7 := by
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
    calc ((44377617531/2500000000000 : ℚ) : ℝ)
        = ((204081/10000000 : ℚ) : ℝ) * ((217451/250000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((-499139/500000 : ℚ) : ℝ) ≤ cos74c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 8 - ((-499119/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((-145535455647/5000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos74c 8 := by
    have hw : ((8:ℕ) : ℝ) ^ (-σ) ≤ ((291573/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_8_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((8:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc8).2
      (by push_cast; norm_num)
    calc ((-145535455647/5000000000000 : ℚ) : ℝ)
        = ((291573/10000000 : ℚ) : ℝ) * ((-499139/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((719123/1000000 : ℚ) : ℝ) ≤ cos74c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 9 - ((719163/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((1387188267/156250000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos74c 9 := by
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
    calc ((1387188267/156250000000 : ℚ) : ℝ)
        = ((1929/156250 : ℚ) : ℝ) * ((719123/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((734849/1000000 : ℚ) : ℝ) ≤ cos74c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 10 - ((734889/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos74_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((73484165151/10000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos74c 10 := by
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
    calc ((73484165151/10000000000000 : ℚ) : ℝ)
        = ((99999/10000000 : ℚ) : ℝ) * ((734849/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos74c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-727/12500 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum74_floor
  have hw11 : ((11:ℕ) : ℝ) ^ (-σ) ≤ ((169681/10000000 : ℚ) : ℝ) := by
    refine le_trans ?_ (wbr_11_17).2
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hw100lo : ((999/10000000 : ℚ) : ℝ) ≤ ((100:ℕ) : ℝ) ^ (-σ) := by
    refine le_trans (wbr_100_20).1 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have htail : ((-1458889747/2000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n) := by
    refine le_trans ?_ habel
    have hC100 := psum74_100
    have hx1 : ((169681/10000000 : ℚ) : ℝ) * ((-727/12500 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-727/12500 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((999/10000000 : ℚ) : ℝ)
          * (((503723/200000 : ℚ) : ℝ) - ((-727/12500 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos74c k)
            - ((-727/12500 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/74 + 1/2)
      ≤ ((1991/5000000 : ℚ) : ℝ) * (100/74 + 1/2) := by
    apply mul_le_mul_of_nonneg_right ?_ (by norm_num)
    have hbr := (wbr_100_17).2
    have hexp : (-((((17:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(17/10) : ℝ) := by
      norm_num
    have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp2 : (100 : ℝ) ^ (-σ - 2) ≤ ((1/10000000 : ℚ) : ℝ) := by
    have hbr := (wbr_100_37).2
    have hexp : (-((((37:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(37/10) : ℝ) := by
      norm_num
    have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
    rw [hexp, hbase] at hbr
    refine le_trans ?_ hbr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hrp3 : (100 : ℝ) ^ (-σ - 1) / (σ + 1)
      ≤ ((1/250000 : ℚ) : ℝ) / (27/10) := by
    have hnum : (100 : ℝ) ^ (-σ - 1) ≤ ((1/250000 : ℚ) : ℝ) := by
      have hbr := (wbr_100_27).2
      have hexp : (-((((27:ℕ)) : ℝ) / (((10:ℕ)) : ℝ))) = (-(27/10) : ℝ) := by
        norm_num
      have hbase : (((100:ℕ)) : ℝ) = (100 : ℝ) := by norm_num
      rw [hexp, hbase] at hbr
      refine le_trans ?_ hbr
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    apply div_le_div₀ (by push_cast; norm_num) hnum (by norm_num) (by linarith)
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos74c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos74c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos74c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos74c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos74c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos74c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos74c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos74c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos74c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos74c 10) := by
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

/-- **Segment positivity at `t = 74`** (rung-74). -/
theorem segment74_re_pos {σ : ℝ} (h1 : (1/2:ℝ) ≤ σ) (h2 : σ ≤ 2) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((74:ℕ):ℝ) * Complex.I)).re := by
  rcases le_total σ (7/10 : ℝ) with hc | hc
  · exact seg74_interval_1 h1 hc
  rcases le_total σ (9/10 : ℝ) with hc2 | hc2
  · exact seg74_interval_2 hc hc2
  rcases le_total σ (11/10 : ℝ) with hc3 | hc3
  · exact seg74_interval_3 hc2 hc3
  rcases le_total σ (7/5 : ℝ) with hc4 | hc4
  · exact seg74_interval_4 hc3 hc4
  rcases le_total σ (17/10 : ℝ) with hc5 | hc5
  · exact seg74_interval_5 hc4 hc5
  exact seg74_interval_6 hc5 h2

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.segment74_re_pos
end AxiomAudit
