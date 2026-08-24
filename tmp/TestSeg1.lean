import RequestProject.DVPSegmentCore

open Complex Finset CriticalLinePhasor.DVP

noncomputable section

namespace CriticalLinePhasor.DVP

theorem seg58_interval_1 {σ : ℝ} (ha : 1/2 ≤ σ) (hb : σ ≤ 7/10) :
    (1/5 : ℝ) ≤ (riemannZeta (↑σ + 58 * Complex.I)).re := by
  have h2 : σ ≤ 2 := by linarith
  have hcore := re_zeta58_lower ha h2
  -- certified cosine floors
  have hc2 : ((-200807/250000 : ℚ) : ℝ) ≤ cos58c 2 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos58c 2 - ((-200797/250000 : ℚ) : ℝ) :=
      (abs_le.mp cos58_br_2).1
    push_cast at h ⊢
    linarith
  have hc3 : ((631189/1000000 : ℚ) : ℝ) ≤ cos58c 3 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos58c 3 - ((631229/1000000 : ℚ) : ℝ) :=
      (abs_le.mp cos58_br_3).1
    push_cast at h ⊢
    linarith
  have hc6 : ((-484539/500000 : ℚ) : ℝ) ≤ cos58c 6 := by
    have h : -((1/25000 : ℚ) : ℝ) ≤ cos58c 6 - ((-484519/500000 : ℚ) : ℝ) :=
      (abs_le.mp cos58_br_6).1
    push_cast at h ⊢
    linarith
  -- one negative head term
  have hterm2 : ((-354979987969/625000000000 : ℚ) : ℝ)
      ≤ ((2:ℕ) : ℝ) ^ (-σ) * cos58c 2 := by
    have hw : ((2:ℕ) : ℝ) ^ (-σ) ≤ ((1767767/2500000 : ℚ) : ℝ) := by
      refine le_trans ?_ (wbr_2_5).2
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have h0 : (0:ℝ) ≤ ((2:ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
    have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc2).2
      (by push_cast; norm_num)
    calc ((-354979987969/625000000000 : ℚ) : ℝ)
        = ((1767767/2500000 : ℚ) : ℝ) * ((-200807/250000 : ℚ) : ℝ) := by
          push_cast; norm_num
      _ ≤ _ := hkey
  -- one positive head term
  have hterm3 : ((292532747507/1000000000000 : ℚ) : ℝ)
      ≤ ((3:ℕ) : ℝ) ^ (-σ) * cos58c 3 := by
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
    calc ((292532747507/1000000000000 : ℚ) : ℝ)
        = ((463463/1000000 : ℚ) : ℝ) * ((631189/1000000 : ℚ) : ℝ) := by
          push_cast; norm_num
      _ ≤ _ := hkey
  -- the tail via Abel
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
  have habel := abel_icc_lower (c := cos58c)
    (w := fun n : ℕ => ((n:ℕ) : ℝ) ^ (-σ))
    (M := 11) (Cmin := ((-110481/200000 : ℚ) : ℝ))
    100 (by norm_num) hanti hnn psum58_floor
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
  have htail : ((-259502427427/2000000000000 : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos58c n) := by
    refine le_trans ?_ habel
    have hC100 := psum58_100
    have h1 : ((1507557/5000000 : ℚ) : ℝ) * ((-110481/200000 : ℚ) : ℝ)
        ≤ ((11:ℕ) : ℝ) ^ (-σ) * ((-110481/200000 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hw11 (by push_cast; norm_num)
    have h2 : ((398107/10000000 : ℚ) : ℝ)
          * (((3721/10000 : ℚ) : ℝ) - ((-110481/200000 : ℚ) : ℝ))
        ≤ ((100:ℕ) : ℝ) ^ (-σ)
          * ((∑ k ∈ Finset.Icc (11:ℕ) 100, cos58c k)
            - ((-110481/200000 : ℚ) : ℝ)) := by
      apply mul_le_mul hw100lo ?_ ?_ (Real.rpow_nonneg (by norm_num) _)
      · linarith [hC100]
      · push_cast
        norm_num
    push_cast at h1 h2 ⊢
    nlinarith [h1, h2]
  -- the costs
  have hcost1 : (100 : ℝ) ^ (-σ) * (100/58 + 1/2)
      ≤ ((1/10 : ℚ) : ℝ) * (100/58 + 1/2) := by
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
  have hrp3 : (100 : ℝ) ^ (-σ - 1) / (σ + 1) ≤ ((1/1000 : ℚ) : ℝ) / (3/2) := by
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
  -- head assembly (only three terms here; the real file carries all nine)
  have hheadsum : ((-354979987969/625000000000 : ℚ) : ℝ)
        + ((292532747507/1000000000000 : ℚ) : ℝ)
      ≤ (((2:ℕ) : ℝ) ^ (-σ) * cos58c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos58c 3) :=
    add_le_add hterm2 hterm3
  -- the sum split
  have hsplitsum : ∑ n ∈ Finset.Icc (2:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos58c n)
      = (∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos58c n))
        + ∑ n ∈ Finset.Icc (11:ℕ) 100, (((n:ℕ) : ℝ) ^ (-σ) * cos58c n) := by
    rw [show Finset.Icc (2:ℕ) 100
        = Finset.Icc (2:ℕ) 10 ∪ Finset.Icc (11:ℕ) 100 by decide]
    exact Finset.sum_union (by decide)
  -- head expansion
  have hexpand : ∑ n ∈ Finset.Icc (2:ℕ) 10, (((n:ℕ) : ℝ) ^ (-σ) * cos58c n)
      = (((2:ℕ) : ℝ) ^ (-σ) * cos58c 2) + (((3:ℕ) : ℝ) ^ (-σ) * cos58c 3)
        + (((4:ℕ) : ℝ) ^ (-σ) * cos58c 4) + (((5:ℕ) : ℝ) ^ (-σ) * cos58c 5)
        + (((6:ℕ) : ℝ) ^ (-σ) * cos58c 6) + (((7:ℕ) : ℝ) ^ (-σ) * cos58c 7)
        + (((8:ℕ) : ℝ) ^ (-σ) * cos58c 8) + (((9:ℕ) : ℝ) ^ (-σ) * cos58c 9)
        + (((10:ℕ) : ℝ) ^ (-σ) * cos58c 10) := by
    rw [show Finset.Icc (2:ℕ) 10 = {2, 3, 4, 5, 6, 7, 8, 9, 10} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ring
  sorry

end CriticalLinePhasor.DVP
