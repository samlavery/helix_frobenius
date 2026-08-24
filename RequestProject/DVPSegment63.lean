import RequestProject.DVPSegment63Core
import RequestProject.DVPWeights63

/-!
# Segment positivity at `t = 63`: rung-63 of the channel extension
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem seg63_interval_1 {σ : ℝ} (ha : (1/2:ℝ) ≤ σ) (hb : σ ≤ (7/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((63:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta63_lower h1 h2
  have hc2 : ((475529/500000 : ℚ) : ℝ) ≤ cos63c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 2 - ((475549/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1463612163469/2500000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos63c 2 := by
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
    calc ((1463612163469/2500000000000 : ℚ) : ℝ)
        = ((3077861/5000000 : ℚ) : ℝ) * ((475529/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((995207/1000000 : ℚ) : ℝ) ≤ cos63c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 3 - ((995247/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((461241621841/1000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos63c 3 := by
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
    calc ((461241621841/1000000000000 : ℚ) : ℝ)
        = ((463463/1000000 : ℚ) : ℝ) * ((995207/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((161827/200000 : ℚ) : ℝ) ≤ cos63c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 4 - ((32367/40000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((613209594657/2000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos63c 4 := by
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
    calc ((613209594657/2000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((161827/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((649647/1000000 : ℚ) : ℝ) ≤ cos63c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 5 - ((649687/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((2105709266511/10000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos63c 5 := by
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
    calc ((2105709266511/10000000000000 : ℚ) : ℝ)
        = ((3241313/10000000 : ℚ) : ℝ) * ((649647/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((488309/500000 : ℚ) : ℝ) ≤ cos63c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 6 - ((488329/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((1393120673241/5000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos63c 6 := by
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
    calc ((1393120673241/5000000000000 : ℚ) : ℝ)
        = ((2852949/10000000 : ℚ) : ℝ) * ((488309/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-39903/40000 : ℚ) : ℝ) ≤ cos63c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 7 - ((-199507/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-30163834887/80000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos63c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((755929/2000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-30163834887/80000000000 : ℚ) : ℝ)
        = ((755929/2000000 : ℚ) : ℝ) * ((-39903/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((73509/125000 : ℚ) : ℝ) ≤ cos63c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 8 - ((36757/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((85732885119/625000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos63c 8 := by
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
    calc ((85732885119/625000000000 : ℚ) : ℝ)
        = ((1166291/5000000 : ℚ) : ℝ) * ((73509/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((490497/500000 : ℚ) : ℝ) ≤ cos63c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 9 - ((490517/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((52678887303/250000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos63c 9 := by
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
    calc ((52678887303/250000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((490497/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((426347/500000 : ℚ) : ℝ) ≤ cos63c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 10 - ((426367/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((425336983957/2500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos63c 10 := by
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
    calc ((425336983957/2500000000000 : ℚ) : ℝ)
        = ((997631/5000000 : ℚ) : ℝ) * ((426347/500000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos63c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-39959/125000 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum63_floor
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
  have htail : ((275424933083/10000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n) := by
    refine le_trans ?_ habel
    have hC100 := psum63_100
    have hx1 : ((1507557/5000000 : ℚ) : ℝ) * ((-39959/125000 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-39959/125000 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((398107/10000000 : ℚ) : ℝ)
          * (((2793241/1000000 : ℚ) : ℝ) - ((-39959/125000 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos63c k)
            - ((-39959/125000 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/63 + 1/2)
      ≤ ((1/10 : ℚ) : ℝ) * (100/63 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos63c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos63c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos63c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos63c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos63c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos63c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos63c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos63c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos63c 10) := by
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

theorem seg63_interval_2 {σ : ℝ} (ha : (7/10:ℝ) ≤ σ) (hb : σ ≤ (9/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((63:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta63_lower h1 h2
  have hc2 : ((475529/500000 : ℚ) : ℝ) ≤ cos63c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 2 - ((475549/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((2548296665643/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos63c 2 := by
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
    calc ((2548296665643/5000000000000 : ℚ) : ℝ)
        = ((5358867/10000000 : ℚ) : ℝ) * ((475529/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((995207/1000000 : ℚ) : ℝ) ≤ cos63c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 3 - ((995247/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((370257807487/1000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos63c 3 := by
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
    calc ((370257807487/1000000000000 : ℚ) : ℝ)
        = ((372041/1000000 : ℚ) : ℝ) * ((995207/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((161827/200000 : ℚ) : ℝ) ≤ cos63c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 4 - ((32367/40000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((92945175623/400000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos63c 4 := by
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
    calc ((92945175623/400000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((161827/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((649647/1000000 : ℚ) : ℝ) ≤ cos63c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 5 - ((649687/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((1526174769339/10000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos63c 5 := by
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
    calc ((1526174769339/10000000000000 : ℚ) : ℝ)
        = ((2349237/10000000 : ℚ) : ℝ) * ((649647/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((488309/500000 : ℚ) : ℝ) ≤ cos63c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 6 - ((488329/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((486775221431/2500000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos63c 6 := by
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
    calc ((486775221431/2500000000000 : ℚ) : ℝ)
        = ((996859/5000000 : ℚ) : ℝ) * ((488309/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-39903/40000 : ℚ) : ℝ) ≤ cos63c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 7 - ((-199507/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-102196730487/400000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos63c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((2561129/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-102196730487/400000000000 : ℚ) : ℝ)
        = ((2561129/10000000 : ℚ) : ℝ) * ((-39903/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((73509/125000 : ℚ) : ℝ) ≤ cos63c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 8 - ((36757/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((11312520537/125000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos63c 8 := by
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
    calc ((11312520537/125000000000 : ℚ) : ℝ)
        = ((153893/1000000 : ℚ) : ℝ) * ((73509/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((490497/500000 : ℚ) : ℝ) ≤ cos63c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 9 - ((490517/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((135783794013/1000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos63c 9 := by
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
    calc ((135783794013/1000000000000 : ℚ) : ℝ)
        = ((276829/2000000 : ℚ) : ℝ) * ((490497/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((426347/500000 : ℚ) : ℝ) ≤ cos63c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 10 - ((426367/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((21469555879/200000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos63c 10 := by
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
    calc ((21469555879/200000000000 : ℚ) : ℝ)
        = ((50357/400000 : ℚ) : ℝ) * ((426347/500000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos63c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-39959/125000 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum63_floor
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
  have htail : ((-103301483479/10000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n) := by
    refine le_trans ?_ habel
    have hC100 := psum63_100
    have hx1 : ((233311/1250000 : ℚ) : ℝ) * ((-39959/125000 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-39959/125000 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((158489/10000000 : ℚ) : ℝ)
          * (((2793241/1000000 : ℚ) : ℝ) - ((-39959/125000 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos63c k)
            - ((-39959/125000 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/63 + 1/2)
      ≤ ((99527/2500000 : ℚ) : ℝ) * (100/63 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos63c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos63c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos63c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos63c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos63c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos63c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos63c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos63c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos63c 10) := by
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

theorem seg63_interval_3 {σ : ℝ} (ha : (9/10:ℝ) ≤ σ) (hb : σ ≤ (11/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((63:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta63_lower h1 h2
  have hc2 : ((475529/500000 : ℚ) : ℝ) ≤ cos63c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 2 - ((475549/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((554605192939/1250000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos63c 2 := by
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
    calc ((554605192939/1250000000000 : ℚ) : ℝ)
        = ((1166291/2500000 : ℚ) : ℝ) * ((475529/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((995207/1000000 : ℚ) : ℝ) ≤ cos63c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 3 - ((995247/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((92881674103/312500000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos63c 3 := by
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
    calc ((92881674103/312500000000 : ℚ) : ℝ)
        = ((93329/312500 : ℚ) : ℝ) * ((995207/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((161827/200000 : ℚ) : ℝ) ≤ cos63c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 4 - ((32367/40000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((44024549869/250000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos63c 4 := by
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
    calc ((44024549869/250000000000 : ℚ) : ℝ)
        = ((272047/1250000 : ℚ) : ℝ) * ((161827/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((649647/1000000 : ℚ) : ℝ) ≤ cos63c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 5 - ((649687/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((1106140304313/10000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos63c 5 := by
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
    calc ((1106140304313/10000000000000 : ℚ) : ℝ)
        = ((1702679/10000000 : ℚ) : ℝ) * ((649647/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((488309/500000 : ℚ) : ℝ) ≤ cos63c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 6 - ((488329/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((42521459411/312500000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos63c 6 := by
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
    calc ((42521459411/312500000000 : ℚ) : ℝ)
        = ((87079/625000 : ℚ) : ℝ) * ((488309/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-39903/40000 : ℚ) : ℝ) ≤ cos63c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 7 - ((-199507/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-69249621447/400000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos63c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((1735449/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-69249621447/400000000000 : ℚ) : ℝ)
        = ((1735449/10000000 : ℚ) : ℝ) * ((-39903/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((73509/125000 : ℚ) : ℝ) ≤ cos63c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 8 - ((36757/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((14926958067/250000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos63c 8 := by
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
    calc ((14926958067/250000000000 : ℚ) : ℝ)
        = ((203063/2000000 : ℚ) : ℝ) * ((73509/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((490497/500000 : ℚ) : ℝ) ≤ cos63c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 9 - ((490517/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((87498288339/1000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos63c 9 := by
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
    calc ((87498288339/1000000000000 : ℚ) : ℝ)
        = ((178387/2000000 : ℚ) : ℝ) * ((490497/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((426347/500000 : ℚ) : ℝ) ≤ cos63c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 10 - ((426367/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((42332419977/625000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos63c 10 := by
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
    calc ((42332419977/625000000000 : ℚ) : ℝ)
        = ((99291/1250000 : ℚ) : ℝ) * ((426347/500000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos63c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-39959/125000 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum63_floor
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
  have htail : ((-172951930601/10000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n) := by
    refine le_trans ?_ habel
    have hC100 := psum63_100
    have hx1 : ((577719/5000000 : ℚ) : ℝ) * ((-39959/125000 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-39959/125000 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((12619/2000000 : ℚ) : ℝ)
          * (((2793241/1000000 : ℚ) : ℝ) - ((-39959/125000 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos63c k)
            - ((-39959/125000 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/63 + 1/2)
      ≤ ((15849/1000000 : ℚ) : ℝ) * (100/63 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos63c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos63c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos63c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos63c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos63c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos63c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos63c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos63c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos63c 10) := by
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

theorem seg63_interval_4 {σ : ℝ} (ha : (11/10:ℝ) ≤ σ) (hb : σ ≤ (7/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((63:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta63_lower h1 h2
  have hc2 : ((475529/500000 : ℚ) : ℝ) ≤ cos63c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 2 - ((475549/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1801917759939/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos63c 2 := by
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
    calc ((1801917759939/5000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((475529/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((995207/1000000 : ℚ) : ℝ) ≤ cos63c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 3 - ((995247/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((106884236593/500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos63c 3 := by
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
    calc ((106884236593/500000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((995207/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((161827/200000 : ℚ) : ℝ) ≤ cos63c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 4 - ((32367/40000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((7261339317/62500000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos63c 4 := by
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
    calc ((7261339317/62500000000 : ℚ) : ℝ)
        = ((44871/312500 : ℚ) : ℝ) * ((161827/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((649647/1000000 : ℚ) : ℝ) ≤ cos63c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 5 - ((649687/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((682526284317/10000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos63c 5 := by
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
    calc ((682526284317/10000000000000 : ℚ) : ℝ)
        = ((1050611/10000000 : ℚ) : ℝ) * ((649647/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((488309/500000 : ℚ) : ℝ) ≤ cos63c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 6 - ((488329/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((99362580247/1250000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos63c 6 := by
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
    calc ((99362580247/1250000000000 : ℚ) : ℝ)
        = ((203483/2500000 : ℚ) : ℝ) * ((488309/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-39903/40000 : ℚ) : ℝ) ≤ cos63c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 7 - ((-199507/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-46924291977/400000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos63c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((1175959/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-46924291977/400000000000 : ℚ) : ℝ)
        = ((1175959/10000000 : ℚ) : ℝ) * ((-39903/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((73509/125000 : ℚ) : ℝ) ≤ cos63c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 8 - ((36757/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((19997902923/625000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos63c 8 := by
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
    calc ((19997902923/625000000000 : ℚ) : ℝ)
        = ((272047/5000000 : ℚ) : ℝ) * ((73509/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((490497/500000 : ℚ) : ℝ) ≤ cos63c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 9 - ((490517/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((226305996357/5000000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos63c 9 := by
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
    calc ((226305996357/5000000000000 : ℚ) : ℝ)
        = ((461381/10000000 : ℚ) : ℝ) * ((490497/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((426347/500000 : ℚ) : ℝ) ≤ cos63c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 10 - ((426367/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((169731725129/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos63c 10 := by
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
    calc ((169731725129/5000000000000 : ℚ) : ℝ)
        = ((398107/10000000 : ℚ) : ℝ) * ((426347/500000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos63c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-39959/125000 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum63_floor
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
  have htail : ((-112073367/6250000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n) := by
    refine le_trans ?_ habel
    have hC100 := psum63_100
    have hx1 : ((715267/10000000 : ℚ) : ℝ) * ((-39959/125000 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-39959/125000 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((1981/1250000 : ℚ) : ℝ)
          * (((2793241/1000000 : ℚ) : ℝ) - ((-39959/125000 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos63c k)
            - ((-39959/125000 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/63 + 1/2)
      ≤ ((7887/1250000 : ℚ) : ℝ) * (100/63 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos63c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos63c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos63c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos63c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos63c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos63c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos63c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos63c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos63c 10) := by
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

theorem seg63_interval_5 {σ : ℝ} (ha : (7/5:ℝ) ≤ σ) (hb : σ ≤ (17/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((63:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta63_lower h1 h2
  have hc2 : ((475529/500000 : ℚ) : ℝ) ≤ cos63c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 2 - ((475549/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1463612163469/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos63c 2 := by
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
    calc ((1463612163469/5000000000000 : ℚ) : ℝ)
        = ((3077861/10000000 : ℚ) : ℝ) * ((475529/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((995207/1000000 : ℚ) : ℝ) ≤ cos63c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 3 - ((995247/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((384367852333/2500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos63c 3 := by
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
    calc ((384367852333/2500000000000 : ℚ) : ℝ)
        = ((386219/2500000 : ℚ) : ℝ) * ((995207/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((161827/200000 : ℚ) : ℝ) ≤ cos63c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 4 - ((32367/40000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((76651138647/1000000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos63c 4 := by
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
    calc ((76651138647/1000000000000 : ℚ) : ℝ)
        = ((473661/5000000 : ℚ) : ℝ) * ((161827/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((649647/1000000 : ℚ) : ℝ) ≤ cos63c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 5 - ((649687/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((210570731757/5000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos63c 5 := by
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
    calc ((210570731757/5000000000000 : ℚ) : ℝ)
        = ((324131/5000000 : ℚ) : ℝ) * ((649647/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((488309/500000 : ℚ) : ℝ) ≤ cos63c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 6 - ((488329/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((232186534719/5000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos63c 6 := by
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
    calc ((232186534719/5000000000000 : ℚ) : ℝ)
        = ((475491/10000000 : ℚ) : ℝ) * ((488309/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-39903/40000 : ℚ) : ℝ) ≤ cos63c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 7 - ((-199507/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-13086947007/200000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos63c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((327969/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-13086947007/200000000000 : ℚ) : ℝ)
        = ((327969/5000000 : ℚ) : ℝ) * ((-39903/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((73509/125000 : ℚ) : ℝ) ≤ cos63c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 8 - ((36757/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((5358291537/312500000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos63c 8 := by
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
    calc ((5358291537/312500000000 : ℚ) : ℝ)
        = ((72893/2500000 : ℚ) : ℝ) * ((73509/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((490497/500000 : ℚ) : ℝ) ≤ cos63c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 9 - ((490517/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((14632997001/625000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos63c 9 := by
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
    calc ((14632997001/625000000000 : ℚ) : ℝ)
        = ((29833/1250000 : ℚ) : ℝ) * ((490497/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((426347/500000 : ℚ) : ℝ) ≤ cos63c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 10 - ((426367/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((42533655761/2500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos63c 10 := by
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
    calc ((42533655761/2500000000000 : ℚ) : ℝ)
        = ((99763/5000000 : ℚ) : ℝ) * ((426347/500000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos63c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-39959/125000 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum63_floor
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
  have htail : ((-98974185363/10000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n) := by
    refine le_trans ?_ habel
    have hC100 := psum63_100
    have hx1 : ((174189/5000000 : ℚ) : ℝ) * ((-39959/125000 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-39959/125000 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((3981/10000000 : ℚ) : ℝ)
          * (((2793241/1000000 : ℚ) : ℝ) - ((-39959/125000 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos63c k)
            - ((-39959/125000 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/63 + 1/2)
      ≤ ((15849/10000000 : ℚ) : ℝ) * (100/63 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos63c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos63c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos63c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos63c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos63c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos63c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos63c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos63c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos63c 10) := by
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

theorem seg63_interval_6 {σ : ℝ} (ha : (17/10:ℝ) ≤ σ) (hb : σ ≤ (2:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((63:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta63_lower h1 h2
  have hc2 : ((475529/500000 : ℚ) : ℝ) ≤ cos63c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 2 - ((475549/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((475529/2000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos63c 2 := by
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
    calc ((475529/2000000 : ℚ) : ℝ)
        = ((1/4 : ℚ) : ℝ) * ((475529/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((995207/1000000 : ℚ) : ℝ) ≤ cos63c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 3 - ((995247/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((1105785444977/10000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos63c 3 := by
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
    calc ((1105785444977/10000000000000 : ℚ) : ℝ)
        = ((1111111/10000000 : ℚ) : ℝ) * ((995207/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((161827/200000 : ℚ) : ℝ) ≤ cos63c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 4 - ((32367/40000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((161827/3200000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos63c 4 := by
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
    calc ((161827/3200000 : ℚ) : ℝ)
        = ((1/16 : ℚ) : ℝ) * ((161827/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((649647/1000000 : ℚ) : ℝ) ≤ cos63c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 5 - ((649687/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((649647/25000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos63c 5 := by
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
    calc ((649647/25000000 : ℚ) : ℝ)
        = ((1/25 : ℚ) : ℝ) * ((649647/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((488309/500000 : ℚ) : ℝ) ≤ cos63c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 6 - ((488329/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((135641009093/5000000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos63c 6 := by
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
    calc ((135641009093/5000000000000 : ℚ) : ℝ)
        = ((277777/10000000 : ℚ) : ℝ) * ((488309/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((-39903/40000 : ℚ) : ℝ) ≤ cos63c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 7 - ((-199507/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((-3649887507/100000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos63c 7 := by
    have hw : ((7:ℕ) : ℝ) ^ (-σ) ≤ ((91469/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_7_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((7:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc7).2
      (by push_cast; norm_num)
    calc ((-3649887507/100000000000 : ℚ) : ℝ)
        = ((91469/2500000 : ℚ) : ℝ) * ((-39903/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((73509/125000 : ℚ) : ℝ) ≤ cos63c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 8 - ((36757/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((73509/8000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos63c 8 := by
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
    calc ((73509/8000000 : ℚ) : ℝ)
        = ((1/64 : ℚ) : ℝ) * ((73509/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((490497/500000 : ℚ) : ℝ) ≤ cos63c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 9 - ((490517/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((946168713/78125000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos63c 9 := by
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
    calc ((946168713/78125000000 : ℚ) : ℝ)
        = ((1929/156250 : ℚ) : ℝ) * ((490497/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((426347/500000 : ℚ) : ℝ) ≤ cos63c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 10 - ((426367/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos63_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((42634273653/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos63c 10 := by
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
    calc ((42634273653/5000000000000 : ℚ) : ℝ)
        = ((99999/10000000 : ℚ) : ℝ) * ((426347/500000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos63c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-39959/125000 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum63_floor
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
  have htail : ((-10226492909/2000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n) := by
    refine le_trans ?_ habel
    have hC100 := psum63_100
    have hx1 : ((169681/10000000 : ℚ) : ℝ) * ((-39959/125000 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-39959/125000 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((999/10000000 : ℚ) : ℝ)
          * (((2793241/1000000 : ℚ) : ℝ) - ((-39959/125000 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos63c k)
            - ((-39959/125000 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/63 + 1/2)
      ≤ ((1991/5000000 : ℚ) : ℝ) * (100/63 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos63c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos63c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos63c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos63c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos63c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos63c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos63c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos63c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos63c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos63c 10) := by
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

/-- **Segment positivity at `t = 63`** (rung-63). -/
theorem segment63_re_pos {σ : ℝ} (h1 : (1/2:ℝ) ≤ σ) (h2 : σ ≤ 2) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((63:ℕ):ℝ) * Complex.I)).re := by
  rcases le_total σ (7/10 : ℝ) with hc | hc
  · exact seg63_interval_1 h1 hc
  rcases le_total σ (9/10 : ℝ) with hc2 | hc2
  · exact seg63_interval_2 hc hc2
  rcases le_total σ (11/10 : ℝ) with hc3 | hc3
  · exact seg63_interval_3 hc2 hc3
  rcases le_total σ (7/5 : ℝ) with hc4 | hc4
  · exact seg63_interval_4 hc3 hc4
  rcases le_total σ (17/10 : ℝ) with hc5 | hc5
  · exact seg63_interval_5 hc4 hc5
  exact seg63_interval_6 hc5 h2

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.segment63_re_pos
end AxiomAudit
