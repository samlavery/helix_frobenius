import RequestProject.DVPSegment91Core
import RequestProject.DVPWeights63
import RequestProject.DVPWeights74
import RequestProject.DVPWeights81

/-!
# Segment positivity at `t = 91`: rung-91
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem seg91_interval_1 {σ : ℝ} (ha : (1/2:ℝ) ≤ σ) (hb : σ ≤ (7/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((91:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta91_lower h1 h2
  have hc2 : ((970209/1000000 : ℚ) : ℝ) ≤ cos91c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 2 - ((970249/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((2986168442949/5000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos91c 2 := by
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
    calc ((2986168442949/5000000000000 : ℚ) : ℝ)
        = ((3077861/5000000 : ℚ) : ℝ) * ((970209/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((424337/500000 : ℚ) : ℝ) ≤ cos91c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 3 - ((424357/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((196664499031/500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos91c 3 := by
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
    calc ((196664499031/500000000000 : ℚ) : ℝ)
        = ((463463/1000000 : ℚ) : ℝ) * ((424337/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((35309/40000 : ℚ) : ℝ) ≤ cos91c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 4 - ((176553/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((133796075919/400000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos91c 4 := by
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
    calc ((133796075919/400000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((35309/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-183059/500000 : ℚ) : ℝ) ≤ cos91c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 5 - ((-183039/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-102333093003/625000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos91c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((559017/1250000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-102333093003/625000000000 : ℚ) : ℝ)
        = ((559017/1250000 : ℚ) : ℝ) * ((-183059/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((118933/125000 : ℚ) : ℝ) ≤ cos91c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 6 - ((59469/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((339309783417/1250000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos91c 6 := by
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
    calc ((339309783417/1250000000000 : ℚ) : ℝ)
        = ((2852949/10000000 : ℚ) : ℝ) * ((118933/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((409693/1000000 : ℚ) : ℝ) ≤ cos91c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 7 - ((409733/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((131159526713/1250000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos91c 7 := by
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
    calc ((131159526713/1250000000000 : ℚ) : ℝ)
        = ((320141/1250000 : ℚ) : ℝ) * ((409693/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((148543/200000 : ℚ) : ℝ) ≤ cos91c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 8 - ((148551/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((173244364013/1000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos91c 8 := by
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
    calc ((173244364013/1000000000000 : ℚ) : ℝ)
        = ((1166291/5000000 : ℚ) : ℝ) * ((148543/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((27537/62500 : ℚ) : ℝ) ≤ cos91c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 9 - ((55079/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((2957446263/31250000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos91c 9 := by
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
    calc ((2957446263/31250000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((27537/62500 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-580531/1000000 : ℚ) : ℝ) ≤ cos91c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 10 - ((-580491/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-917900204809/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos91c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((1581139/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-917900204809/5000000000000 : ℚ) : ℝ)
        = ((1581139/5000000 : ℚ) : ℝ) * ((-580531/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos91c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-211/1600 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum91_floor
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
  have htail : ((123731049903/2500000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n) := by
    refine le_trans ?_ habel
    have hC100 := psum91_100
    have hx1 : ((1507557/5000000 : ℚ) : ℝ) * ((-211/1600 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-211/1600 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((398107/10000000 : ℚ) : ℝ)
          * (((2110091/1000000 : ℚ) : ℝ) - ((-211/1600 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos91c k)
            - ((-211/1600 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/91 + 1/2)
      ≤ ((1/10 : ℚ) : ℝ) * (100/91 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos91c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos91c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos91c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos91c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos91c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos91c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos91c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos91c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos91c 10) := by
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

theorem seg91_interval_2 {σ : ℝ} (ha : (7/10:ℝ) ≤ σ) (hb : σ ≤ (9/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((91:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta91_lower h1 h2
  have hc2 : ((970209/1000000 : ℚ) : ℝ) ≤ cos91c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 2 - ((970249/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((5199220993203/10000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos91c 2 := by
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
    calc ((5199220993203/10000000000000 : ℚ) : ℝ)
        = ((5358867/10000000 : ℚ) : ℝ) * ((970209/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((424337/500000 : ℚ) : ℝ) ≤ cos91c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 3 - ((424357/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((157870761817/500000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos91c 3 := by
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
    calc ((157870761817/500000000000 : ℚ) : ℝ)
        = ((372041/1000000 : ℚ) : ℝ) * ((424337/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((35309/40000 : ℚ) : ℝ) ≤ cos91c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 4 - ((176553/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((20279688841/80000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos91c 4 := by
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
    calc ((20279688841/80000000000 : ℚ) : ℝ)
        = ((574349/2000000 : ℚ) : ℝ) * ((35309/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-183059/500000 : ℚ) : ℝ) ≤ cos91c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 5 - ((-183039/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-296675849763/2500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos91c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((1620657/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-296675849763/2500000000000 : ℚ) : ℝ)
        = ((1620657/5000000 : ℚ) : ℝ) * ((-183059/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((118933/125000 : ℚ) : ℝ) ≤ cos91c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 6 - ((59469/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((118559431447/625000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos91c 6 := by
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
    calc ((118559431447/625000000000 : ℚ) : ℝ)
        = ((996859/5000000 : ℚ) : ℝ) * ((118933/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((409693/1000000 : ℚ) : ℝ) ≤ cos91c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 7 - ((409733/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((88875112183/1250000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos91c 7 := by
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
    calc ((88875112183/1250000000000 : ℚ) : ℝ)
        = ((216931/1250000 : ℚ) : ℝ) * ((409693/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((148543/200000 : ℚ) : ℝ) ≤ cos91c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 8 - ((148551/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((22859727899/200000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos91c 8 := by
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
    calc ((22859727899/200000000000 : ℚ) : ℝ)
        = ((153893/1000000 : ℚ) : ℝ) * ((148543/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((27537/62500 : ℚ) : ℝ) ≤ cos91c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 9 - ((55079/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((7623040173/125000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos91c 9 := by
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
    calc ((7623040173/125000000000 : ℚ) : ℝ)
        = ((276829/2000000 : ℚ) : ℝ) * ((27537/62500 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-580531/1000000 : ℚ) : ℝ) ≤ cos91c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 10 - ((-580491/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-1158312024653/10000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos91c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((1995263/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_7).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-1158312024653/10000000000000 : ℚ) : ℝ)
        = ((1995263/10000000 : ℚ) : ℝ) * ((-580531/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos91c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-211/1600 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum91_floor
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
  have htail : ((54591922187/5000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n) := by
    refine le_trans ?_ habel
    have hC100 := psum91_100
    have hx1 : ((233311/1250000 : ℚ) : ℝ) * ((-211/1600 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-211/1600 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((158489/10000000 : ℚ) : ℝ)
          * (((2110091/1000000 : ℚ) : ℝ) - ((-211/1600 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos91c k)
            - ((-211/1600 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/91 + 1/2)
      ≤ ((99527/2500000 : ℚ) : ℝ) * (100/91 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos91c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos91c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos91c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos91c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos91c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos91c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos91c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos91c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos91c 10) := by
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

theorem seg91_interval_3 {σ : ℝ} (ha : (9/10:ℝ) ≤ σ) (hb : σ ≤ (11/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((91:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta91_lower h1 h2
  have hc2 : ((970209/1000000 : ℚ) : ℝ) ≤ cos91c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 2 - ((970249/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((1131546024819/2500000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos91c 2 := by
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
    calc ((1131546024819/2500000000000 : ℚ) : ℝ)
        = ((1166291/2500000 : ℚ) : ℝ) * ((970209/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((424337/500000 : ℚ) : ℝ) ≤ cos91c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 3 - ((424357/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((39602947873/156250000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos91c 3 := by
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
    calc ((39602947873/156250000000 : ℚ) : ℝ)
        = ((93329/312500 : ℚ) : ℝ) * ((424337/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((35309/40000 : ℚ) : ℝ) ≤ cos91c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 4 - ((176553/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((9605707523/50000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos91c 4 := by
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
    calc ((9605707523/50000000000 : ℚ) : ℝ)
        = ((272047/1250000 : ℚ) : ℝ) * ((35309/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-183059/500000 : ℚ) : ℝ) ≤ cos91c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 5 - ((-183039/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-215024579521/2500000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos91c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((1174619/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-215024579521/2500000000000 : ℚ) : ℝ)
        = ((1174619/5000000 : ℚ) : ℝ) * ((-183059/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((118933/125000 : ℚ) : ℝ) ≤ cos91c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 6 - ((59469/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((10356566707/78125000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos91c 6 := by
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
    calc ((10356566707/78125000000 : ℚ) : ℝ)
        = ((87079/625000 : ℚ) : ℝ) * ((118933/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((409693/1000000 : ℚ) : ℝ) ≤ cos91c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 7 - ((409733/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((240890880447/5000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos91c 7 := by
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
    calc ((240890880447/5000000000000 : ℚ) : ℝ)
        = ((587979/5000000 : ℚ) : ℝ) * ((409693/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((148543/200000 : ℚ) : ℝ) ≤ cos91c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 8 - ((148551/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((30163587209/400000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos91c 8 := by
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
    calc ((30163587209/400000000000 : ℚ) : ℝ)
        = ((203063/2000000 : ℚ) : ℝ) * ((148543/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((27537/62500 : ℚ) : ℝ) ≤ cos91c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 9 - ((55079/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((4912242819/125000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos91c 9 := by
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
    calc ((4912242819/125000000000 : ℚ) : ℝ)
        = ((178387/2000000 : ℚ) : ℝ) * ((27537/62500 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-580531/1000000 : ℚ) : ℝ) ≤ cos91c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 10 - ((-580491/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-365422784853/5000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos91c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((629463/5000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_9).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-365422784853/5000000000000 : ℚ) : ℝ)
        = ((629463/5000000 : ℚ) : ℝ) * ((-580531/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos91c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-211/1600 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum91_floor
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
  have htail : ((-272913537/250000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n) := by
    refine le_trans ?_ habel
    have hC100 := psum91_100
    have hx1 : ((577719/5000000 : ℚ) : ℝ) * ((-211/1600 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-211/1600 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((12619/2000000 : ℚ) : ℝ)
          * (((2110091/1000000 : ℚ) : ℝ) - ((-211/1600 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos91c k)
            - ((-211/1600 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/91 + 1/2)
      ≤ ((15849/1000000 : ℚ) : ℝ) * (100/91 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos91c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos91c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos91c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos91c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos91c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos91c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos91c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos91c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos91c 10) := by
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

theorem seg91_interval_4 {σ : ℝ} (ha : (11/10:ℝ) ≤ σ) (hb : σ ≤ (7/5:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((91:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta91_lower h1 h2
  have hc2 : ((970209/1000000 : ℚ) : ℝ) ≤ cos91c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 2 - ((970249/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((3676404231819/10000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos91c 2 := by
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
    calc ((3676404231819/10000000000000 : ℚ) : ℝ)
        = ((3789291/10000000 : ℚ) : ℝ) * ((970209/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((424337/500000 : ℚ) : ℝ) ≤ cos91c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 3 - ((424357/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((45573369463/250000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos91c 3 := by
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
    calc ((45573369463/250000000000 : ℚ) : ℝ)
        = ((107399/500000 : ℚ) : ℝ) * ((424337/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((35309/40000 : ℚ) : ℝ) ≤ cos91c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 4 - ((176553/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((1584350139/12500000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos91c 4 := by
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
    calc ((1584350139/12500000000 : ℚ) : ℝ)
        = ((44871/312500 : ℚ) : ℝ) * ((35309/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-183059/500000 : ℚ) : ℝ) ≤ cos91c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 5 - ((-183039/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-7792272453/125000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos91c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((42567/250000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-7792272453/125000000000 : ℚ) : ℝ)
        = ((42567/250000 : ℚ) : ℝ) * ((-183059/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((118933/125000 : ℚ) : ℝ) ≤ cos91c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 6 - ((59469/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((24200843639/312500000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos91c 6 := by
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
    calc ((24200843639/312500000000 : ℚ) : ℝ)
        = ((203483/2500000 : ℚ) : ℝ) * ((118933/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((409693/1000000 : ℚ) : ℝ) ≤ cos91c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 7 - ((409733/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((268732797341/10000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos91c 7 := by
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
    calc ((268732797341/10000000000000 : ℚ) : ℝ)
        = ((655937/10000000 : ℚ) : ℝ) * ((409693/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((148543/200000 : ℚ) : ℝ) ≤ cos91c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 8 - ((148551/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((40410677521/1000000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos91c 8 := by
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
    calc ((40410677521/1000000000000 : ℚ) : ℝ)
        = ((272047/5000000 : ℚ) : ℝ) * ((148543/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((27537/62500 : ℚ) : ℝ) ≤ cos91c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 9 - ((55079/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((12705048597/625000000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos91c 9 := by
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
    calc ((12705048597/625000000000 : ℚ) : ℝ)
        = ((461381/10000000 : ℚ) : ℝ) * ((27537/62500 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-580531/1000000 : ℚ) : ℝ) ≤ cos91c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 10 - ((-580491/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-461132608699/10000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos91c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((794329/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_11).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-461132608699/10000000000000 : ℚ) : ℝ)
        = ((794329/10000000 : ℚ) : ℝ) * ((-580531/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos91c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-211/1600 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum91_floor
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
  have htail : ((-58795158457/10000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n) := by
    refine le_trans ?_ habel
    have hC100 := psum91_100
    have hx1 : ((715267/10000000 : ℚ) : ℝ) * ((-211/1600 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-211/1600 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((1981/1250000 : ℚ) : ℝ)
          * (((2110091/1000000 : ℚ) : ℝ) - ((-211/1600 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos91c k)
            - ((-211/1600 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/91 + 1/2)
      ≤ ((7887/1250000 : ℚ) : ℝ) * (100/91 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos91c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos91c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos91c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos91c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos91c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos91c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos91c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos91c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos91c 10) := by
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

theorem seg91_interval_5 {σ : ℝ} (ha : (7/5:ℝ) ≤ σ) (hb : σ ≤ (17/10:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((91:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta91_lower h1 h2
  have hc2 : ((970209/1000000 : ℚ) : ℝ) ≤ cos91c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 2 - ((970249/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((2986168442949/10000000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos91c 2 := by
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
    calc ((2986168442949/10000000000000 : ℚ) : ℝ)
        = ((3077861/10000000 : ℚ) : ℝ) * ((970209/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((424337/500000 : ℚ) : ℝ) ≤ cos91c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 3 - ((424357/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((163887011803/1250000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos91c 3 := by
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
    calc ((163887011803/1250000000000 : ℚ) : ℝ)
        = ((386219/2500000 : ℚ) : ℝ) * ((424337/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((35309/40000 : ℚ) : ℝ) ≤ cos91c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 4 - ((176553/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((16724496249/200000000000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos91c 4 := by
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
    calc ((16724496249/200000000000 : ℚ) : ℝ)
        = ((473661/5000000 : ℚ) : ℝ) * ((35309/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-183059/500000 : ℚ) : ℝ) ≤ cos91c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 5 - ((-183039/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-48080995527/1250000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos91c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((262653/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-48080995527/1250000000000 : ℚ) : ℝ)
        = ((262653/2500000 : ℚ) : ℝ) * ((-183059/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((118933/125000 : ℚ) : ℝ) ≤ cos91c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 6 - ((59469/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((56551571103/1250000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos91c 6 := by
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
    calc ((56551571103/1250000000000 : ℚ) : ℝ)
        = ((475491/10000000 : ℚ) : ℝ) * ((118933/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((409693/1000000 : ℚ) : ℝ) ≤ cos91c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 7 - ((409733/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((1199171411/80000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos91c 7 := by
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
    calc ((1199171411/80000000000 : ℚ) : ℝ)
        = ((2927/80000 : ℚ) : ℝ) * ((409693/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((148543/200000 : ℚ) : ℝ) ≤ cos91c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 8 - ((148551/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((10827744899/500000000000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos91c 8 := by
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
    calc ((10827744899/500000000000 : ℚ) : ℝ)
        = ((72893/2500000 : ℚ) : ℝ) * ((148543/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((27537/62500 : ℚ) : ℝ) ≤ cos91c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 9 - ((55079/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((821511321/78125000000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos91c 9 := by
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
    calc ((821511321/78125000000 : ℚ) : ℝ)
        = ((29833/1250000 : ℚ) : ℝ) * ((27537/62500 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-580531/1000000 : ℚ) : ℝ) ≤ cos91c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 10 - ((-580491/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-57778508837/2500000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos91c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((99527/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_14).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-57778508837/2500000000000 : ℚ) : ℝ)
        = ((99527/2500000 : ℚ) : ℝ) * ((-580531/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos91c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-211/1600 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum91_floor
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
  have htail : ((-4627135263/1250000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n) := by
    refine le_trans ?_ habel
    have hC100 := psum91_100
    have hx1 : ((174189/5000000 : ℚ) : ℝ) * ((-211/1600 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-211/1600 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((3981/10000000 : ℚ) : ℝ)
          * (((2110091/1000000 : ℚ) : ℝ) - ((-211/1600 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos91c k)
            - ((-211/1600 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/91 + 1/2)
      ≤ ((15849/10000000 : ℚ) : ℝ) * (100/91 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos91c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos91c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos91c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos91c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos91c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos91c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos91c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos91c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos91c 10) := by
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

theorem seg91_interval_6 {σ : ℝ} (ha : (17/10:ℝ) ≤ σ) (hb : σ ≤ (2:ℝ)) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((91:ℕ):ℝ) * Complex.I)).re := by
  have h1 : (1/2 : ℝ) ≤ σ := by linarith
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta91_lower h1 h2
  have hc2 : ((970209/1000000 : ℚ) : ℝ) ≤ cos91c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 2 - ((970249/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_2).1
    push_cast at h ⊢
    linarith
  have hterm2 : ((970209/4000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos91c 2 := by
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
    calc ((970209/4000000 : ℚ) : ℝ)
        = ((1/4 : ℚ) : ℝ) * ((970209/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc3 : ((424337/500000 : ℚ) : ℝ) ≤ cos91c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 3 - ((424357/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_3).1
    push_cast at h ⊢
    linarith
  have hterm3 : ((471485508407/5000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos91c 3 := by
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
    calc ((471485508407/5000000000000 : ℚ) : ℝ)
        = ((1111111/10000000 : ℚ) : ℝ) * ((424337/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc4 : ((35309/40000 : ℚ) : ℝ) ≤ cos91c 4 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 4 - ((176553/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_4).1
    push_cast at h ⊢
    linarith
  have hterm4 : ((35309/640000 : ℚ) : ℝ)
      ≤ ((4:ℕ) : ℝ) ^ (-σ) * cos91c 4 := by
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
    calc ((35309/640000 : ℚ) : ℝ)
        = ((1/16 : ℚ) : ℝ) * ((35309/40000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc5 : ((-183059/500000 : ℚ) : ℝ) ≤ cos91c 5 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 5 - ((-183039/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_5).1
    push_cast at h ⊢
    linarith
  have hterm5 : ((-118670376517/5000000000000 : ℚ) : ℝ)
      ≤ ((5:ℕ) : ℝ) ^ (-σ) * cos91c 5 := by
    have hw : ((5:ℕ) : ℝ) ^ (-σ) ≤ ((648263/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_5_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((5:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc5).2
      (by push_cast; norm_num)
    calc ((-118670376517/5000000000000 : ℚ) : ℝ)
        = ((648263/10000000 : ℚ) : ℝ) * ((-183059/500000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc6 : ((118933/125000 : ℚ) : ℝ) ≤ cos91c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 6 - ((59469/62500 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_6).1
    push_cast at h ⊢
    linarith
  have hterm6 : ((33036851941/1250000000000 : ℚ) : ℝ)
      ≤ ((6:ℕ) : ℝ) ^ (-σ) * cos91c 6 := by
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
    calc ((33036851941/1250000000000 : ℚ) : ℝ)
        = ((277777/10000000 : ℚ) : ℝ) * ((118933/125000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc7 : ((409693/1000000 : ℚ) : ℝ) ≤ cos91c 7 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 7 - ((409733/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_7).1
    push_cast at h ⊢
    linarith
  have hterm7 : ((83610557133/10000000000000 : ℚ) : ℝ)
      ≤ ((7:ℕ) : ℝ) ^ (-σ) * cos91c 7 := by
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
    calc ((83610557133/10000000000000 : ℚ) : ℝ)
        = ((204081/10000000 : ℚ) : ℝ) * ((409693/1000000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc8 : ((148543/200000 : ℚ) : ℝ) ≤ cos91c 8 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 8 - ((148551/200000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_8).1
    push_cast at h ⊢
    linarith
  have hterm8 : ((148543/12800000 : ℚ) : ℝ)
      ≤ ((8:ℕ) : ℝ) ^ (-σ) * cos91c 8 := by
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
    calc ((148543/12800000 : ℚ) : ℝ)
        = ((1/64 : ℚ) : ℝ) * ((148543/200000 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc9 : ((27537/62500 : ℚ) : ℝ) ≤ cos91c 9 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 9 - ((55079/125000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_9).1
    push_cast at h ⊢
    linarith
  have hterm9 : ((53118873/9765625000 : ℚ) : ℝ)
      ≤ ((9:ℕ) : ℝ) ^ (-σ) * cos91c 9 := by
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
    calc ((53118873/9765625000 : ℚ) : ℝ)
        = ((1929/156250 : ℚ) : ℝ) * ((27537/62500 : ℚ) : ℝ) := by push_cast; norm_num
      _ ≤ _ := hkey
  have hc10 : ((-580531/1000000 : ℚ) : ℝ) ≤ cos91c 10 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 10 - ((-580491/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos91_br_10).1
    push_cast at h ⊢
    linarith
  have hterm10 : ((-115831608837/10000000000000 : ℚ) : ℝ)
      ≤ ((10:ℕ) : ℝ) ^ (-σ) * cos91c 10 := by
    have hw : ((10:ℕ) : ℝ) ^ (-σ) ≤ ((199527/10000000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_10_17).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((10:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc10).2
      (by push_cast; norm_num)
    calc ((-115831608837/10000000000000 : ℚ) : ℝ)
        = ((199527/10000000 : ℚ) : ℝ) * ((-580531/1000000 : ℚ) : ℝ) := by push_cast; norm_num
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
  have habel := abel_icc_lower (c := cos91c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-211/1600 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum91_floor
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
  have htail : ((-20136957841/10000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n) := by
    refine le_trans ?_ habel
    have hC100 := psum91_100
    have hx1 : ((169681/10000000 : ℚ) : ℝ) * ((-211/1600 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-211/1600 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have hx2 : ((999/10000000 : ℚ) : ℝ)
          * (((2110091/1000000 : ℚ) : ℝ) - ((-211/1600 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos91c k)
            - ((-211/1600 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at hx1 hx2 ⊢
    nlinarith [hx1, hx2]
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/91 + 1/2)
      ≤ ((1991/5000000 : ℚ) : ℝ) * (100/91 + 1/2) := by
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
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos91c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos91c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos91c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos91c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos91c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos91c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos91c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos91c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos91c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos91c 10) := by
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

/-- **Segment positivity at `t = 91`** (rung-91). -/
theorem segment91_re_pos {σ : ℝ} (h1 : (1/2:ℝ) ≤ σ) (h2 : σ ≤ 2) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + ((91:ℕ):ℝ) * Complex.I)).re := by
  rcases le_total σ (7/10 : ℝ) with hc | hc
  · exact seg91_interval_1 h1 hc
  rcases le_total σ (9/10 : ℝ) with hc2 | hc2
  · exact seg91_interval_2 hc hc2
  rcases le_total σ (11/10 : ℝ) with hc3 | hc3
  · exact seg91_interval_3 hc2 hc3
  rcases le_total σ (7/5 : ℝ) with hc4 | hc4
  · exact seg91_interval_4 hc3 hc4
  rcases le_total σ (17/10 : ℝ) with hc5 | hc5
  · exact seg91_interval_5 hc4 hc5
  exact seg91_interval_6 hc5 h2

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.segment91_re_pos
end AxiomAudit
