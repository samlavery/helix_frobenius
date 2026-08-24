import RequestProject.DVPSqrtTable

/-!
# Station `t = 39` of the Hardy ladder (sign -)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT39 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((39 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((721/1000000 : ℚ) : ℝ))

theorem st39_c1 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -901/5000000) (δ := 21/100000000) (ψ := 721/1000000) 39 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t1 : ((19999/20000 : ℚ) : ℝ) ≤ stT39 1 := by
  have hc : ((19999/20000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19999/20000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((19999/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c2 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-161303/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 949639/2000000) (δ := 167/50000000) (ψ := 721/1000000) 39 4
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t2 : ((-17824394661/78125000000 : ℚ) : ℝ) ≤ stT39 2 := by
  have hc : ((-10083/31250 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17824394661/78125000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-10083/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c3 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((420193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2842847/10000000) (δ := 357/100000000) (ψ := 721/1000000) 39 7
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t3 : ((1212848225393/5000000000000 : ℚ) : ℝ) ≤ stT39 3 := by
  have hc : ((420143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1212848225393/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((420143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c4 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-79141/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1552443/2500000) (δ := 57/25000000) (ψ := 721/1000000) 39 9
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t4 : ((-197865039573/500000000000 : ℚ) : ℝ) ≤ stT39 4 := by
  have hc : ((-39573/50000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-197865039573/500000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-39573/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c5 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((997921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -161239/10000000) (δ := 177/50000000) (ψ := 721/1000000) 39 10
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t5 : ((892522764917/2000000000000 : ℚ) : ℝ) ≤ stT39 5 := by
  have hc : ((997871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((892522764917/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((997871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c6 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((722863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38143/200000) (δ := 279/100000000) (ψ := 721/1000000) 39 11
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t6 : ((1475435530933/5000000000000 : ℚ) : ℝ) ≤ stT39 6 := by
  have hc : ((722813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1475435530933/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((722813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c7 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((440801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 614439/5000000) (δ := 1/500000) (ψ := 721/1000000) 39 12
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t7 : ((52061761367/156250000000 : ℚ) : ℝ) ≤ stT39 7 := by
  have hc : ((55097/62500 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52061761367/156250000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((55097/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c8 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((834313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58391/400000) (δ := 121/50000000) (ψ := 721/1000000) 39 13
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t8 : ((2949564367179/10000000000000 : ℚ) : ℝ) ≤ stT39 8 := by
  have hc : ((834263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2949564367179/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((834263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c9 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-646327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1420973/2500000) (δ := 151/50000000) (ψ := 721/1000000) 39 14
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t9 : ((-1077295215459/5000000000000 : ℚ) : ℝ) ≤ stT39 9 := by
  have hc : ((-646377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1077295215459/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-646377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c10 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-130813/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2294379/5000000) (δ := 11/3125000) (ψ := 721/1000000) 39 14
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t10 : ((-103436532241/1250000000000 : ℚ) : ℝ) ≤ stT39 10 := by
  have hc : ((-65419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103436532241/1250000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-65419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c11 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((46549/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -913231/5000000) (δ := 151/50000000) (ψ := 721/1000000) 39 15
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t11 : ((1122728582471/5000000000000 : ℚ) : ℝ) ≤ stT39 11 := by
  have hc : ((372367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1122728582471/5000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((372367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c12 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-887579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6657147/10000000) (δ := 101/50000000) (ψ := 721/1000000) 39 15
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t12 : ((-80073899719/312500000000 : ℚ) : ℝ) ≤ stT39 12 := by
  have hc : ((-887629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80073899719/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-887629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c13 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((54889/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -311663/2500000) (δ := 243/100000000) (ψ := 721/1000000) 39 16
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t13 : ((2435615589/10000000000 : ℚ) : ℝ) ≤ stT39 13 := by
  have hc : ((439087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2435615589/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((439087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c14 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-36583/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47831/80000) (δ := 27/10000000) (ψ := 721/1000000) 39 16
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t14 : ((-195557765823/1000000000000 : ℚ) : ℝ) ≤ stT39 14 := by
  have hc : ((-73171/100000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195557765823/1000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-73171/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c15 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((180753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3002283/10000000) (δ := 369/100000000) (ψ := 721/1000000) 39 17
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t15 : ((14582422727/156250000000 : ℚ) : ℝ) ≤ stT39 15 := by
  have hc : ((22591/62500 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14582422727/156250000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((22591/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c16 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((125981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1645111/5000000) (δ := 319/100000000) (ψ := 721/1000000) 39 17
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t16 : ((31489/500000 : ℚ) : ℝ) ≤ stT39 16 := by
  have hc : ((31489/125000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31489/500000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((31489/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c17 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-107287/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -162671/250000) (δ := 209/100000000) (ψ := 721/1000000) 39 18
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t17 : ((-1040897739761/5000000000000 : ℚ) : ℝ) ≤ stT39 17 := by
  have hc : ((-429173/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1040897739761/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-429173/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c18 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((186207/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -186779/2000000) (δ := 7/3125000) (ψ := 721/1000000) 39 18
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t18 : ((219435212667/1000000000000 : ℚ) : ℝ) ≤ stT39 18 := by
  have hc : ((186197/200000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219435212667/1000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((186197/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c19 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-16353/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4337659/10000000) (δ := 19/6250000) (ψ := 721/1000000) 39 18
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t19 : ((-9381959141/250000000000 : ℚ) : ℝ) ≤ stT39 19 := by
  have hc : ((-8179/50000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9381959141/250000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-8179/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c20 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-828759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -796151/1250000) (δ := 57/20000000) (ψ := 721/1000000) 39 19
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t20 : ((-463318320753/2500000000000 : ℚ) : ℝ) ≤ stT39 20 := by
  have hc : ((-828809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-463318320753/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-828809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c21 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((39959/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1612167/10000000) (δ := 31/12500000) (ψ := 721/1000000) 39 19
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t21 : ((87192195257/500000000000 : ℚ) : ℝ) ≤ stT39 21 := by
  have hc : ((79913/100000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87192195257/500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((79913/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c22 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((390691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 584707/2000000) (δ := 9/4000000) (ψ := 721/1000000) 39 19
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t22 : ((832849346487/10000000000000 : ℚ) : ℝ) ≤ stT39 22 := by
  have hc : ((390641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((832849346487/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((390641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c23 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-971679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7257581/10000000) (δ := 87/25000000) (ψ := 721/1000000) 39 19
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t23 : ((-405239173141/2000000000000 : ℚ) : ℝ) ≤ stT39 23 := by
  have hc : ((-971729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-405239173141/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-971729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c24 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-5959/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4300819/10000000) (δ := 257/100000000) (ψ := 721/1000000) 39 20
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t24 : ((-6083921781/200000000000 : ℚ) : ℝ) ≤ stT39 24 := by
  have hc : ((-5961/40000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6083921781/200000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-5961/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c25 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((198357/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12827/400000) (δ := 297/100000000) (ψ := 721/1000000) 39 20
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t25 : ((198347/1000000 : ℚ) : ℝ) ≤ stT39 25 := by
  have hc : ((198347/200000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198347/1000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((198347/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c26 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((21081/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 700669/2000000) (δ := 227/100000000) (ψ := 721/1000000) 39 20
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t26 : ((165323911139/5000000000000 : ℚ) : ℝ) ≤ stT39 26 := by
  have hc : ((84299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165323911139/5000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((84299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c27 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-964201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7183027/10000000) (δ := 69/25000000) (ψ := 721/1000000) 39 20
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t27 : ((-1855702013751/10000000000000 : ℚ) : ℝ) ≤ stT39 27 := by
  have hc : ((-964251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1855702013751/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-964251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c28 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-408527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4979091/10000000) (δ := 21/6250000) (ψ := 721/1000000) 39 21
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t28 : ((-772138211871/10000000000000 : ℚ) : ℝ) ≤ stT39 28 := by
  have hc : ((-408577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-772138211871/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-408577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c29 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((101511/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -194711/1250000) (δ := 143/50000000) (ψ := 721/1000000) 39 21
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t29 : ((753958200107/5000000000000 : ℚ) : ℝ) ≤ stT39 29 := by
  have hc : ((406019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((753958200107/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((406019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c30 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((765431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 873857/5000000) (δ := 337/100000000) (ψ := 721/1000000) 39 21
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t30 : ((1397387472321/10000000000000 : ℚ) : ℝ) ≤ stT39 30 := by
  have hc : ((765381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1397387472321/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((765381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c31 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-395941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4944721/10000000) (δ := 193/50000000) (ψ := 721/1000000) 39 21
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t31 : ((-355610609757/5000000000000 : ℚ) : ℝ) ≤ stT39 31 := by
  have hc : ((-395991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-355610609757/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-395991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c32 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-997227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -239617/312500) (δ := 193/50000000) (ψ := 721/1000000) 39 22
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t32 : ((-1762953370459/10000000000000 : ℚ) : ℝ) ≤ stT39 32 := by
  have hc : ((-997277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1762953370459/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-997277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c33 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-145947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4667507/10000000) (δ := 247/100000000) (ψ := 721/1000000) 39 22
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t33 : ((-63526175061/1250000000000 : ℚ) : ℝ) ≤ stT39 33 := by
  have hc : ((-36493/125000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63526175061/1250000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-36493/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c34 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((190769/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1756843/10000000) (δ := 143/50000000) (ψ := 721/1000000) 39 22
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t34 : ((130857814461/1000000000000 : ℚ) : ℝ) ≤ stT39 34 := by
  have hc : ((381513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130857814461/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((381513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c35 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((90989/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 534721/5000000) (δ := 257/100000000) (ψ := 721/1000000) 39 22
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t35 : ((4805968221/31250000000 : ℚ) : ℝ) ≤ stT39 35 := by
  have hc : ((11373/12500 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4805968221/31250000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((11373/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c36 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((44341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1908051/5000000) (δ := 123/50000000) (ψ := 721/1000000) 39 22
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t36 : ((36909151903/5000000000000 : ℚ) : ℝ) ≤ stT39 36 := by
  have hc : ((44291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36909151903/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((44291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c37 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-854301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3243751/5000000) (δ := 173/50000000) (ψ := 721/1000000) 39 22
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t37 : ((-140454450049/1000000000000 : ℚ) : ℝ) ≤ stT39 37 := by
  have hc : ((-854351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140454450049/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-854351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c38 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-176139/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6620307/10000000) (δ := 119/50000000) (ψ := 721/1000000) 39 23
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t38 : ((-57150310007/400000000000 : ℚ) : ℝ) ≤ stT39 38 := by
  have hc : ((-176149/200000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57150310007/400000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-176149/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c39 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-32119/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4087697/10000000) (δ := 41/20000000) (ψ := 721/1000000) 39 23
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t39 : ((-1608487769/156250000000 : ℚ) : ℝ) ≤ stT39 39 := by
  have hc : ((-2009/31250 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1608487769/156250000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-2009/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c40 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((797483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1619211/10000000) (δ := 13/6250000) (ψ := 721/1000000) 39 23
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t40 : ((630425809377/5000000000000 : ℚ) : ℝ) ≤ stT39 40 := by
  have hc : ((797433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((630425809377/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((797433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c41 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((190139/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 788319/10000000) (δ := 67/25000000) (ψ := 721/1000000) 39 23
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t41 : ((296931494073/2000000000000 : ℚ) : ℝ) ≤ stT39 41 := by
  have hc : ((190129/200000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((296931494073/2000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((190129/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c42 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((19403/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 313783/1000000) (δ := 13/4000000) (ψ := 721/1000000) 39 23
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t42 : ((239477178567/5000000000000 : ℚ) : ℝ) ≤ stT39 42 := by
  have hc : ((155199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((239477178567/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((155199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c43 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-566313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2716027/5000000) (δ := 63/20000000) (ψ := 721/1000000) 39 23
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t43 : ((-431847822959/5000000000000 : ℚ) : ℝ) ≤ stT39 43 := by
  have hc : ((-566363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-431847822959/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-566363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c44 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-249349/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1918383/2500000) (δ := 49/20000000) (ψ := 721/1000000) 39 23
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t44 : ((-751853349711/5000000000000 : ℚ) : ℝ) ≤ stT39 44 := by
  have hc : ((-498723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-751853349711/5000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-498723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c45 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-693643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -45651/78125) (δ := 359/100000000) (ψ := 721/1000000) 39 24
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t45 : ((-129262059927/1250000000000 : ℚ) : ℝ) ≤ stT39 45 := by
  have hc : ((-693693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129262059927/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-693693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c46 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((45259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -740077/2000000) (δ := 369/100000000) (ψ := 721/1000000) 39 24
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t46 : ((33346934523/2500000000000 : ℚ) : ℝ) ≤ stT39 46 := by
  have hc : ((22617/250000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33346934523/2500000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((22617/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c47 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((200313/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -160353/1000000) (δ := 197/50000000) (ψ := 721/1000000) 39 24
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t47 : ((584336248049/5000000000000 : ℚ) : ℝ) ≤ stT39 47 := by
  have hc : ((400601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((584336248049/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((400601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c48 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((983903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 224589/5000000) (δ := 167/50000000) (ψ := 721/1000000) 39 24
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t48 : ((11360550591/80000000000 : ℚ) : ℝ) ≤ stT39 48 := by
  have hc : ((983853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11360550591/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((983853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c49 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((553843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1229779/5000000) (δ := 379/100000000) (ψ := 721/1000000) 39 24
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t49 : ((791132619803/10000000000000 : ℚ) : ℝ) ≤ stT39 49 := by
  have hc : ((553793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((791132619803/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((553793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c50 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-199583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2214661/5000000) (δ := 187/50000000) (ψ := 721/1000000) 39 24
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t50 : ((-141161891731/5000000000000 : ℚ) : ℝ) ≤ stT39 50 := by
  have hc : ((-199633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141161891731/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-199633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c51 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-82671/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3180039/5000000) (δ := 137/50000000) (ψ := 721/1000000) 39 24
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t51 : ((-28942407989/250000000000 : ℚ) : ℝ) ≤ stT39 51 := by
  have hc : ((-20669/25000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28942407989/250000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-20669/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c52 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-246817/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3727311/5000000) (δ := 167/50000000) (ψ := 721/1000000) 39 25
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t52 : ((-684582111909/5000000000000 : ℚ) : ℝ) ≤ stT39 52 := by
  have hc : ((-493659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-684582111909/5000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-493659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c53 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-619553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5597423/10000000) (δ := 177/50000000) (ψ := 721/1000000) 39 25
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t53 : ((-425545199209/5000000000000 : ℚ) : ℝ) ≤ stT39 53 := by
  have hc : ((-619603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-425545199209/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-619603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c54 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((60783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -188747/500000) (δ := 7/3125000) (ψ := 721/1000000) 39 25
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t54 : ((82647106191/10000000000000 : ℚ) : ℝ) ≤ stT39 54 := by
  have hc : ((60733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82647106191/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((60733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c55 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((350371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1985899/10000000) (δ := 319/100000000) (ψ := 721/1000000) 39 25
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t55 : ((236203098027/2500000000000 : ℚ) : ℝ) ≤ stT39 55 := by
  have hc : ((175173/250000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((236203098027/2500000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((175173/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c56 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((248951/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -114547/5000000) (δ := 369/100000000) (ψ := 721/1000000) 39 25
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t56 : ((332658011181/2500000000000 : ℚ) : ℝ) ≤ stT39 56 := by
  have hc : ((497877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((332658011181/2500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((497877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c57 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((8261/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 748307/5000000) (δ := 249/100000000) (ψ := 721/1000000) 39 25
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t57 : ((5470648293/50000000000 : ℚ) : ℝ) ≤ stT39 57 := by
  have hc : ((16521/20000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5470648293/50000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((16521/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c58 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((289661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3192309/10000000) (δ := 91/25000000) (ψ := 721/1000000) 39 25
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t58 : ((47534722263/1250000000000 : ℚ) : ℝ) ≤ stT39 58 := by
  have hc : ((289611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47534722263/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((289611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c59 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-182117/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4859017/10000000) (δ := 51/25000000) (ψ := 721/1000000) 39 25
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t59 : ((-11856442419/250000000000 : ℚ) : ℝ) ≤ stT39 59 := by
  have hc : ((-91071/250000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11856442419/250000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-91071/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c60 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-26763/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6497711/10000000) (δ := 259/100000000) (ψ := 721/1000000) 39 25
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t60 : ((-110569332367/1000000000000 : ℚ) : ℝ) ≤ stT39 60 := by
  have hc : ((-428233/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110569332367/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-428233/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c61 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-994789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3799323/5000000) (δ := 3/1250000) (ψ := 721/1000000) 39 26
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t61 : ((-1273761015591/10000000000000 : ℚ) : ℝ) ≤ stT39 61 := by
  have hc : ((-994839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1273761015591/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-994839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c62 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-370481/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1202649/2000000) (δ := 33/10000000) (ψ := 721/1000000) 39 26
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t62 : ((-117635840253/1250000000000 : ℚ) : ℝ) ≤ stT39 62 := by
  have hc : ((-185253/250000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117635840253/1250000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-185253/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c63 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-104469/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1113303/2500000) (δ := 303/100000000) (ψ := 721/1000000) 39 26
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t63 : ((-32912527427/1250000000000 : ℚ) : ℝ) ≤ stT39 63 := by
  have hc : ((-52247/250000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32912527427/1250000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-52247/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c64 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((392821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2917747/10000000) (δ := 1/312500) (ψ := 721/1000000) 39 26
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t64 : ((392771/8000000 : ℚ) : ℝ) ≤ stT39 64 := by
  have hc : ((392771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((392771/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((392771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c65 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((845959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1406089/10000000) (δ := 13/5000000) (ψ := 721/1000000) 39 26
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t65 : ((1049220690423/10000000000000 : ℚ) : ℝ) ≤ stT39 65 := by
  have hc : ((845909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1049220690423/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((845909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c66 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((31233/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8249/1000000) (δ := 223/100000000) (ψ := 721/1000000) 39 26
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t66 : ((307545709271/2500000000000 : ℚ) : ℝ) ≤ stT39 66 := by
  have hc : ((499703/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((307545709271/2500000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((499703/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c67 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((101773/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1548683/10000000) (δ := 313/100000000) (ψ := 721/1000000) 39 26
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t67 : ((248655655749/2500000000000 : ℚ) : ℝ) ≤ stT39 67 := by
  have hc : ((407067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((248655655749/2500000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((407067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c68 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((364909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1496577/5000000) (δ := 363/100000000) (ψ := 721/1000000) 39 26
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t68 : ((221228241201/5000000000000 : ℚ) : ℝ) ≤ stT39 68 := by
  have hc : ((364859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((221228241201/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((364859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c69 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-194569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4416537/10000000) (δ := 363/100000000) (ψ := 721/1000000) 39 26
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t69 : ((-234293834721/10000000000000 : ℚ) : ℝ) ≤ stT39 69 := by
  have hc : ((-194619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234293834721/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-194619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c70 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-686729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5819439/10000000) (δ := 213/100000000) (ψ := 721/1000000) 39 26
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t70 : ((-820858177391/10000000000000 : ℚ) : ℝ) ≤ stT39 70 := by
  have hc : ((-686779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-820858177391/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-686779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c71 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-966231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7202441/10000000) (δ := 1/312500) (ψ := 721/1000000) 39 26
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t71 : ((-573382448871/5000000000000 : ℚ) : ℝ) ≤ stT39 71 := by
  have hc : ((-966281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-573382448871/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-966281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c72 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-191941/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -892733/1250000) (δ := 39/12500000) (ψ := 721/1000000) 39 27
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t72 : ((-14138534807/125000000000 : ℚ) : ℝ) ≤ stT39 72 := by
  have hc : ((-191951/200000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14138534807/125000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-191951/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c73 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-680181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1159403/2000000) (δ := 111/50000000) (ψ := 721/1000000) 39 27
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t73 : ((-199037631293/2500000000000 : ℚ) : ℝ) ≤ stT39 73 := by
  have hc : ((-680231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199037631293/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-680231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c74 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-215681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -69851/156250) (δ := 371/100000000) (ψ := 721/1000000) 39 27
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t74 : ((-250782325687/10000000000000 : ℚ) : ℝ) ≤ stT39 74 := by
  have hc : ((-215731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250782325687/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-215731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c75 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((6027/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -79043/250000) (δ := 11/3125000) (ψ := 721/1000000) 39 27
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t75 : ((34791111/1000000000 : ℚ) : ℝ) ≤ stT39 75 := by
  have hc : ((3013/10000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34791111/1000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((3013/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c76 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((366483/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -187031/1000000) (δ := 29/12500000) (ψ := 721/1000000) 39 27
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t76 : ((105088977431/1250000000000 : ℚ) : ℝ) ≤ stT39 76 := by
  have hc : ((183229/250000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105088977431/1250000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((183229/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c77 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((485869/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -297891/5000000) (δ := 151/50000000) (ψ := 721/1000000) 39 27
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t77 : ((27683512581/250000000000 : ℚ) : ℝ) ≤ stT39 77 := by
  have hc : ((121461/125000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27683512581/250000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((121461/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c78 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((965113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6623/100000) (δ := 141/50000000) (ψ := 721/1000000) 39 27
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t78 : ((1092718638451/10000000000000 : ℚ) : ℝ) ≤ stT39 78 := by
  have hc : ((965063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1092718638451/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((965063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c79 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((144727/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 380871/2000000) (δ := 211/100000000) (ψ := 721/1000000) 39 27
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t79 : ((162819215379/2000000000000 : ℚ) : ℝ) ≤ stT39 79 := by
  have hc : ((144717/200000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162819215379/2000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((144717/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c80 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((501/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1565393/5000000) (δ := 131/50000000) (ψ := 721/1000000) 39 27
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t80 : ((14001127259/400000000000 : ℚ) : ℝ) ≤ stT39 80 := by
  have hc : ((12523/40000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14001127259/400000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((12523/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c81 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-33047/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2170991/5000000) (δ := 221/100000000) (ψ := 721/1000000) 39 27
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t81 : ((-4591253673/250000000000 : ℚ) : ℝ) ≤ stT39 81 := by
  have hc : ((-33057/200000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4591253673/250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-33057/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c82 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-600823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1384579/2500000) (δ := 101/50000000) (ψ := 721/1000000) 39 27
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t82 : ((-165888416967/2500000000000 : ℚ) : ℝ) ≤ stT39 82 := by
  have hc : ((-600873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165888416967/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-600873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c83 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-179781/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6720149/10000000) (δ := 171/50000000) (ψ := 721/1000000) 39 27
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t83 : ((-197346332613/2000000000000 : ℚ) : ℝ) ≤ stT39 83 := by
  have hc : ((-179791/200000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-197346332613/2000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-179791/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c84 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-249977/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -977517/1250000) (δ := 49/12500000) (ψ := 721/1000000) 39 28
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t84 : ((-54552208711/500000000000 : ℚ) : ℝ) ≤ stT39 84 := by
  have hc : ((-499979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54552208711/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-499979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c85 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-177851/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1666569/2500000) (δ := 121/50000000) (ψ := 721/1000000) 39 28
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t85 : ((-192917467233/2000000000000 : ℚ) : ℝ) ≤ stT39 85 := by
  have hc : ((-177861/200000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192917467233/2000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-177861/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c86 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-11937/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5525913/10000000) (δ := 181/50000000) (ψ := 721/1000000) 39 28
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t86 : ((-804567479/12500000000 : ℚ) : ℝ) ≤ stT39 86 := by
  have hc : ((-5969/10000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-804567479/12500000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-5969/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c87 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-187579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1099683/2500000) (δ := 301/100000000) (ψ := 721/1000000) 39 28
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t87 : ((-201159490077/10000000000000 : ℚ) : ℝ) ≤ stT39 87 := by
  have hc : ((-187629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-201159490077/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-187629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c88 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((127101/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -656887/2000000) (δ := 351/100000000) (ψ := 721/1000000) 39 28
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t88 : ((33865849307/1250000000000 : ℚ) : ℝ) ≤ stT39 88 := by
  have hc : ((31769/125000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33865849307/1250000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((31769/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c89 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((642461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -272841/1250000) (δ := 17/6250000) (ψ := 721/1000000) 39 28
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t89 : ((680953732767/10000000000000 : ℚ) : ℝ) ≤ stT39 89 := by
  have hc : ((642411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((680953732767/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((642411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c90 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((181177/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1093331/10000000) (δ := 141/50000000) (ψ := 721/1000000) 39 28
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t90 : ((47741671341/500000000000 : ℚ) : ℝ) ≤ stT39 90 := by
  have hc : ((181167/200000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47741671341/500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((181167/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c91 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((49999/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3993/2500000) (δ := 211/50000000) (ψ := 721/1000000) 39 28
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t91 : ((26205265503/250000000000 : ℚ) : ℝ) ≤ stT39 91 := by
  have hc : ((99993/100000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26205265503/250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((99993/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c92 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((14268/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 262403/2500000) (δ := 73/25000000) (ψ := 721/1000000) 39 28
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t92 : ((118996822293/1250000000000 : ℚ) : ℝ) ≤ stT39 92 := by
  have hc : ((456551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118996822293/1250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((456551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c93 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((666367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2103677/10000000) (δ := 191/50000000) (ψ := 721/1000000) 39 28
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t93 : ((690938079467/10000000000000 : ℚ) : ℝ) ≤ stT39 93 := by
  have hc : ((666317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((690938079467/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((666317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c94 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((153581/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3146467/10000000) (δ := 39/12500000) (ψ := 721/1000000) 39 28
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t94 : ((39595220769/1250000000000 : ℚ) : ℝ) ≤ stT39 94 := by
  have hc : ((38389/125000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39595220769/1250000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((38389/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c95 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-25081/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4178223/10000000) (δ := 181/50000000) (ψ := 721/1000000) 39 28
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t95 : ((-51490808073/5000000000000 : ℚ) : ℝ) ≤ stT39 95 := by
  have hc : ((-50187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51490808073/5000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-50187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c96 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-243597/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 207967/400000) (δ := 93/25000000) (ψ := 721/1000000) 39 28
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t96 : ((-124322864631/2500000000000 : ℚ) : ℝ) ≤ stT39 96 := by
  have hc : ((-121811/250000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124322864631/2500000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-121811/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c97 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-158271/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3104773/5000000) (δ := 73/25000000) (ψ := 721/1000000) 39 28
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t97 : ((-160710138507/2000000000000 : ℚ) : ℝ) ≤ stT39 97 := by
  have hc : ((-158281/200000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160710138507/2000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-158281/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c98 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-966961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1441911/2000000) (δ := 151/50000000) (ψ := 721/1000000) 39 28
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t98 : ((-976829062683/10000000000000 : ℚ) : ℝ) ≤ stT39 98 := by
  have hc : ((-967011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-976829062683/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-967011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c99 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-990469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -938569/1250000) (δ := 201/100000000) (ψ := 721/1000000) 39 29
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t99 : ((-497754617361/5000000000000 : ℚ) : ℝ) ≤ stT39 99 := by
  have hc : ((-990519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-497754617361/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-990519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_c100 :
    |Real.cos (((39 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((721/1000000 : ℚ) : ℝ))
      - ((-862739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1632161/2500000) (δ := 171/50000000) (ψ := 721/1000000) 39 29
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st39_t100 : ((-862789/10000000 : ℚ) : ℝ) ≤ stT39 100 := by
  have hc : ((-862789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((39 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((721/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st39_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-862789/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-862789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st39_p1 : ((19999/20000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT39 (i+1) := by
  rw [Finset.sum_range_one]
  exact st39_t1

theorem st39_p2 : ((60296699089/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT39 (i+1))
      = (∑ i ∈ Finset.range 1, stT39 (i+1)) + stT39 2 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 1
    simpa using h
  have hprev := st39_p1
  have hstep := st39_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p3 : ((5071836967089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT39 (i+1))
      = (∑ i ∈ Finset.range 2, stT39 (i+1)) + stT39 3 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 2
    simpa using h
  have hprev := st39_p2
  have hstep := st39_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p4 : ((3093186571359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT39 (i+1))
      = (∑ i ∈ Finset.range 3, stT39 (i+1)) + stT39 4 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 3
    simpa using h
  have hprev := st39_p3
  have hstep := st39_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p5 : ((10648986967303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT39 (i+1))
      = (∑ i ∈ Finset.range 4, stT39 (i+1)) + stT39 5 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 4
    simpa using h
  have hprev := st39_p4
  have hstep := st39_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p6 : ((13599858029169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT39 (i+1))
      = (∑ i ∈ Finset.range 5, stT39 (i+1)) + stT39 6 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 5
    simpa using h
  have hprev := st39_p5
  have hstep := st39_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p7 : ((16931810756657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT39 (i+1))
      = (∑ i ∈ Finset.range 6, stT39 (i+1)) + stT39 7 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 6
    simpa using h
  have hprev := st39_p6
  have hstep := st39_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p8 : ((4970343780959/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT39 (i+1))
      = (∑ i ∈ Finset.range 7, stT39 (i+1)) + stT39 8 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 7
    simpa using h
  have hprev := st39_p7
  have hstep := st39_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p9 : ((8863392346459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT39 (i+1))
      = (∑ i ∈ Finset.range 8, stT39 (i+1)) + stT39 9 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 8
    simpa using h
  have hprev := st39_p8
  have hstep := st39_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p10 : ((1689929243499/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT39 (i+1))
      = (∑ i ∈ Finset.range 9, stT39 (i+1)) + stT39 10 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 9
    simpa using h
  have hprev := st39_p9
  have hstep := st39_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p11 : ((4786187399983/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT39 (i+1))
      = (∑ i ∈ Finset.range 10, stT39 (i+1)) + stT39 11 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 10
    simpa using h
  have hprev := st39_p10
  have hstep := st39_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p12 : ((4145596202231/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT39 (i+1))
      = (∑ i ∈ Finset.range 11, stT39 (i+1)) + stT39 12 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 11
    simpa using h
  have hprev := st39_p11
  have hstep := st39_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p13 : ((4754500099481/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT39 (i+1))
      = (∑ i ∈ Finset.range 12, stT39 (i+1)) + stT39 13 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 12
    simpa using h
  have hprev := st39_p12
  have hstep := st39_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p14 : ((8531211369847/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT39 (i+1))
      = (∑ i ∈ Finset.range 13, stT39 (i+1)) + stT39 14 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 13
    simpa using h
  have hprev := st39_p13
  have hstep := st39_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p15 : ((8997848897111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT39 (i+1))
      = (∑ i ∈ Finset.range 14, stT39 (i+1)) + stT39 15 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 14
    simpa using h
  have hprev := st39_p14
  have hstep := st39_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p16 : ((9312738897111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT39 (i+1))
      = (∑ i ∈ Finset.range 15, stT39 (i+1)) + stT39 16 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 15
    simpa using h
  have hprev := st39_p15
  have hstep := st39_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p17 : ((165436823147/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT39 (i+1))
      = (∑ i ∈ Finset.range 16, stT39 (i+1)) + stT39 17 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 16
    simpa using h
  have hprev := st39_p16
  have hstep := st39_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p18 : ((1873803444137/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT39 (i+1))
      = (∑ i ∈ Finset.range 17, stT39 (i+1)) + stT39 18 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 17
    simpa using h
  have hprev := st39_p17
  have hstep := st39_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p19 : ((1836275607573/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT39 (i+1))
      = (∑ i ∈ Finset.range 18, stT39 (i+1)) + stT39 19 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 18
    simpa using h
  have hprev := st39_p18
  have hstep := st39_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p20 : ((8254741396359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT39 (i+1))
      = (∑ i ∈ Finset.range 19, stT39 (i+1)) + stT39 20 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 19
    simpa using h
  have hprev := st39_p19
  have hstep := st39_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p21 : ((9126663348929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT39 (i+1))
      = (∑ i ∈ Finset.range 20, stT39 (i+1)) + stT39 21 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 20
    simpa using h
  have hprev := st39_p20
  have hstep := st39_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p22 : ((3817235208869/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT39 (i+1))
      = (∑ i ∈ Finset.range 21, stT39 (i+1)) + stT39 22 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 21
    simpa using h
  have hprev := st39_p21
  have hstep := st39_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p23 : ((213249752233/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT39 (i+1))
      = (∑ i ∈ Finset.range 22, stT39 (i+1)) + stT39 23 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 22
    simpa using h
  have hprev := st39_p22
  have hstep := st39_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p24 : ((1675578408959/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT39 (i+1))
      = (∑ i ∈ Finset.range 23, stT39 (i+1)) + stT39 24 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 23
    simpa using h
  have hprev := st39_p23
  have hstep := st39_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p25 : ((1873925408959/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT39 (i+1))
      = (∑ i ∈ Finset.range 24, stT39 (i+1)) + stT39 25 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 24
    simpa using h
  have hprev := st39_p24
  have hstep := st39_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p26 : ((4767475477967/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT39 (i+1))
      = (∑ i ∈ Finset.range 25, stT39 (i+1)) + stT39 26 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 25
    simpa using h
  have hprev := st39_p25
  have hstep := st39_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p27 : ((17214199898117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT39 (i+1))
      = (∑ i ∈ Finset.range 26, stT39 (i+1)) + stT39 27 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 26
    simpa using h
  have hprev := st39_p26
  have hstep := st39_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p28 : ((8221030843123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT39 (i+1))
      = (∑ i ∈ Finset.range 27, stT39 (i+1)) + stT39 28 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 27
    simpa using h
  have hprev := st39_p27
  have hstep := st39_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p29 : ((897498904323/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT39 (i+1))
      = (∑ i ∈ Finset.range 28, stT39 (i+1)) + stT39 29 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 28
    simpa using h
  have hprev := st39_p28
  have hstep := st39_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p30 : ((19347365558781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT39 (i+1))
      = (∑ i ∈ Finset.range 29, stT39 (i+1)) + stT39 30 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 29
    simpa using h
  have hprev := st39_p29
  have hstep := st39_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p31 : ((18636144339267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT39 (i+1))
      = (∑ i ∈ Finset.range 30, stT39 (i+1)) + stT39 31 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 30
    simpa using h
  have hprev := st39_p30
  have hstep := st39_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p32 : ((2109148871101/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT39 (i+1))
      = (∑ i ∈ Finset.range 31, stT39 (i+1)) + stT39 32 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 31
    simpa using h
  have hprev := st39_p31
  have hstep := st39_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p33 : ((51140567401/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT39 (i+1))
      = (∑ i ∈ Finset.range 32, stT39 (i+1)) + stT39 33 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 32
    simpa using h
  have hprev := st39_p32
  have hstep := st39_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p34 : ((1767355971293/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT39 (i+1))
      = (∑ i ∈ Finset.range 33, stT39 (i+1)) + stT39 34 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 33
    simpa using h
  have hprev := st39_p33
  have hstep := st39_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p35 : ((384229390873/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT39 (i+1))
      = (∑ i ∈ Finset.range 34, stT39 (i+1)) + stT39 35 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 34
    simpa using h
  have hprev := st39_p34
  have hstep := st39_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p36 : ((602665245233/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT39 (i+1))
      = (∑ i ∈ Finset.range 35, stT39 (i+1)) + stT39 36 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 35
    simpa using h
  have hprev := st39_p35
  have hstep := st39_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p37 : ((8940371673483/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT39 (i+1))
      = (∑ i ∈ Finset.range 36, stT39 (i+1)) + stT39 37 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 36
    simpa using h
  have hprev := st39_p36
  have hstep := st39_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p38 : ((16451985596791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT39 (i+1))
      = (∑ i ∈ Finset.range 37, stT39 (i+1)) + stT39 38 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 37
    simpa using h
  have hprev := st39_p37
  have hstep := st39_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p39 : ((653961695183/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT39 (i+1))
      = (∑ i ∈ Finset.range 38, stT39 (i+1)) + stT39 39 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 38
    simpa using h
  have hprev := st39_p38
  have hstep := st39_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p40 : ((17609893998329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT39 (i+1))
      = (∑ i ∈ Finset.range 39, stT39 (i+1)) + stT39 40 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 39
    simpa using h
  have hprev := st39_p39
  have hstep := st39_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p41 : ((9547275734347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT39 (i+1))
      = (∑ i ∈ Finset.range 40, stT39 (i+1)) + stT39 41 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 40
    simpa using h
  have hprev := st39_p40
  have hstep := st39_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p42 : ((4893376456457/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT39 (i+1))
      = (∑ i ∈ Finset.range 41, stT39 (i+1)) + stT39 42 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 41
    simpa using h
  have hprev := st39_p41
  have hstep := st39_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p43 : ((1870981017991/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT39 (i+1))
      = (∑ i ∈ Finset.range 42, stT39 (i+1)) + stT39 43 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 42
    simpa using h
  have hprev := st39_p42
  have hstep := st39_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p44 : ((2150762935061/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT39 (i+1))
      = (∑ i ∈ Finset.range 43, stT39 (i+1)) + stT39 44 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 43
    simpa using h
  have hprev := st39_p43
  have hstep := st39_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p45 : ((1010750437567/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT39 (i+1))
      = (∑ i ∈ Finset.range 44, stT39 (i+1)) + stT39 45 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 44
    simpa using h
  have hprev := st39_p44
  have hstep := st39_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p46 : ((4076348684791/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT39 (i+1))
      = (∑ i ∈ Finset.range 45, stT39 (i+1)) + stT39 46 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 45
    simpa using h
  have hprev := st39_p45
  have hstep := st39_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p47 : ((8737033617631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT39 (i+1))
      = (∑ i ∈ Finset.range 46, stT39 (i+1)) + stT39 47 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 46
    simpa using h
  have hprev := st39_p46
  have hstep := st39_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p48 : ((18894136059137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT39 (i+1))
      = (∑ i ∈ Finset.range 47, stT39 (i+1)) + stT39 48 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 47
    simpa using h
  have hprev := st39_p47
  have hstep := st39_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p49 : ((984263433947/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT39 (i+1))
      = (∑ i ∈ Finset.range 48, stT39 (i+1)) + stT39 49 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 48
    simpa using h
  have hprev := st39_p48
  have hstep := st39_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p50 : ((9701472447739/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT39 (i+1))
      = (∑ i ∈ Finset.range 49, stT39 (i+1)) + stT39 50 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 49
    simpa using h
  have hprev := st39_p49
  have hstep := st39_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p51 : ((9122624287959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT39 (i+1))
      = (∑ i ∈ Finset.range 50, stT39 (i+1)) + stT39 51 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 50
    simpa using h
  have hprev := st39_p50
  have hstep := st39_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p52 : ((168760843521/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT39 (i+1))
      = (∑ i ∈ Finset.range 51, stT39 (i+1)) + stT39 52 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 51
    simpa using h
  have hprev := st39_p51
  have hstep := st39_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p53 : ((8012496976841/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT39 (i+1))
      = (∑ i ∈ Finset.range 52, stT39 (i+1)) + stT39 53 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 52
    simpa using h
  have hprev := st39_p52
  have hstep := st39_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p54 : ((16107641059873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT39 (i+1))
      = (∑ i ∈ Finset.range 53, stT39 (i+1)) + stT39 54 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 53
    simpa using h
  have hprev := st39_p53
  have hstep := st39_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p55 : ((17052453451981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT39 (i+1))
      = (∑ i ∈ Finset.range 54, stT39 (i+1)) + stT39 55 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 54
    simpa using h
  have hprev := st39_p54
  have hstep := st39_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p56 : ((3676617099341/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT39 (i+1))
      = (∑ i ∈ Finset.range 55, stT39 (i+1)) + stT39 56 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 55
    simpa using h
  have hprev := st39_p55
  have hstep := st39_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p57 : ((3895443031061/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT39 (i+1))
      = (∑ i ∈ Finset.range 56, stT39 (i+1)) + stT39 57 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 56
    simpa using h
  have hprev := st39_p56
  have hstep := st39_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p58 : ((19857492933409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT39 (i+1))
      = (∑ i ∈ Finset.range 57, stT39 (i+1)) + stT39 58 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 57
    simpa using h
  have hprev := st39_p57
  have hstep := st39_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p59 : ((19383235236649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT39 (i+1))
      = (∑ i ∈ Finset.range 58, stT39 (i+1)) + stT39 59 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 58
    simpa using h
  have hprev := st39_p58
  have hstep := st39_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p60 : ((18277541912979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT39 (i+1))
      = (∑ i ∈ Finset.range 59, stT39 (i+1)) + stT39 60 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 59
    simpa using h
  have hprev := st39_p59
  have hstep := st39_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p61 : ((4250945224347/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT39 (i+1))
      = (∑ i ∈ Finset.range 60, stT39 (i+1)) + stT39 61 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 60
    simpa using h
  have hprev := st39_p60
  have hstep := st39_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p62 : ((4015673543841/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT39 (i+1))
      = (∑ i ∈ Finset.range 61, stT39 (i+1)) + stT39 62 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 61
    simpa using h
  have hprev := st39_p61
  have hstep := st39_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p63 : ((3949848488987/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT39 (i+1))
      = (∑ i ∈ Finset.range 62, stT39 (i+1)) + stT39 63 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 62
    simpa using h
  have hprev := st39_p62
  have hstep := st39_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p64 : ((4072589426487/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT39 (i+1))
      = (∑ i ∈ Finset.range 63, stT39 (i+1)) + stT39 64 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 63
    simpa using h
  have hprev := st39_p63
  have hstep := st39_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p65 : ((17339578396371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT39 (i+1))
      = (∑ i ∈ Finset.range 64, stT39 (i+1)) + stT39 65 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 64
    simpa using h
  have hprev := st39_p64
  have hstep := st39_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p66 : ((3713952246691/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT39 (i+1))
      = (∑ i ∈ Finset.range 65, stT39 (i+1)) + stT39 66 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 65
    simpa using h
  have hprev := st39_p65
  have hstep := st39_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p67 : ((19564383856451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT39 (i+1))
      = (∑ i ∈ Finset.range 66, stT39 (i+1)) + stT39 67 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 66
    simpa using h
  have hprev := st39_p66
  have hstep := st39_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p68 : ((20006840338853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT39 (i+1))
      = (∑ i ∈ Finset.range 67, stT39 (i+1)) + stT39 68 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 67
    simpa using h
  have hprev := st39_p67
  have hstep := st39_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p69 : ((4943136626033/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT39 (i+1))
      = (∑ i ∈ Finset.range 68, stT39 (i+1)) + stT39 69 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 68
    simpa using h
  have hprev := st39_p68
  have hstep := st39_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p70 : ((18951688326741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT39 (i+1))
      = (∑ i ∈ Finset.range 69, stT39 (i+1)) + stT39 70 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 69
    simpa using h
  have hprev := st39_p69
  have hstep := st39_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p71 : ((17804923428999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT39 (i+1))
      = (∑ i ∈ Finset.range 70, stT39 (i+1)) + stT39 71 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 70
    simpa using h
  have hprev := st39_p70
  have hstep := st39_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p72 : ((16673840644439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT39 (i+1))
      = (∑ i ∈ Finset.range 71, stT39 (i+1)) + stT39 72 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 71
    simpa using h
  have hprev := st39_p71
  have hstep := st39_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p73 : ((15877690119267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT39 (i+1))
      = (∑ i ∈ Finset.range 72, stT39 (i+1)) + stT39 73 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 72
    simpa using h
  have hprev := st39_p72
  have hstep := st39_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p74 : ((781345389679/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT39 (i+1))
      = (∑ i ∈ Finset.range 73, stT39 (i+1)) + stT39 74 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 73
    simpa using h
  have hprev := st39_p73
  have hstep := st39_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p75 : ((798740945179/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT39 (i+1))
      = (∑ i ∈ Finset.range 74, stT39 (i+1)) + stT39 75 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 74
    simpa using h
  have hprev := st39_p74
  have hstep := st39_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p76 : ((4203882680757/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT39 (i+1))
      = (∑ i ∈ Finset.range 75, stT39 (i+1)) + stT39 76 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 75
    simpa using h
  have hprev := st39_p75
  have hstep := st39_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p77 : ((4480717806567/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT39 (i+1))
      = (∑ i ∈ Finset.range 76, stT39 (i+1)) + stT39 77 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 76
    simpa using h
  have hprev := st39_p76
  have hstep := st39_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p78 : ((19015589864719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT39 (i+1))
      = (∑ i ∈ Finset.range 77, stT39 (i+1)) + stT39 78 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 77
    simpa using h
  have hprev := st39_p77
  have hstep := st39_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p79 : ((9914842970807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT39 (i+1))
      = (∑ i ∈ Finset.range 78, stT39 (i+1)) + stT39 79 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 78
    simpa using h
  have hprev := st39_p78
  have hstep := st39_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p80 : ((20179714123089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT39 (i+1))
      = (∑ i ∈ Finset.range 79, stT39 (i+1)) + stT39 80 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 79
    simpa using h
  have hprev := st39_p79
  have hstep := st39_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p81 : ((19996063976169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT39 (i+1))
      = (∑ i ∈ Finset.range 80, stT39 (i+1)) + stT39 81 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 80
    simpa using h
  have hprev := st39_p80
  have hstep := st39_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p82 : ((19332510308301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT39 (i+1))
      = (∑ i ∈ Finset.range 81, stT39 (i+1)) + stT39 82 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 81
    simpa using h
  have hprev := st39_p81
  have hstep := st39_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p83 : ((4586444661309/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT39 (i+1))
      = (∑ i ∈ Finset.range 82, stT39 (i+1)) + stT39 83 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 82
    simpa using h
  have hprev := st39_p82
  have hstep := st39_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p84 : ((2156841808877/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT39 (i+1))
      = (∑ i ∈ Finset.range 83, stT39 (i+1)) + stT39 84 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 83
    simpa using h
  have hprev := st39_p83
  have hstep := st39_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p85 : ((16290147134851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT39 (i+1))
      = (∑ i ∈ Finset.range 84, stT39 (i+1)) + stT39 85 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 84
    simpa using h
  have hprev := st39_p84
  have hstep := st39_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p86 : ((15646493151651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT39 (i+1))
      = (∑ i ∈ Finset.range 85, stT39 (i+1)) + stT39 86 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 85
    simpa using h
  have hprev := st39_p85
  have hstep := st39_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p87 : ((7722666830787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT39 (i+1))
      = (∑ i ∈ Finset.range 86, stT39 (i+1)) + stT39 87 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 86
    simpa using h
  have hprev := st39_p86
  have hstep := st39_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p88 : ((1571626045603/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT39 (i+1))
      = (∑ i ∈ Finset.range 87, stT39 (i+1)) + stT39 88 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 87
    simpa using h
  have hprev := st39_p87
  have hstep := st39_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p89 : ((16397214188797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT39 (i+1))
      = (∑ i ∈ Finset.range 88, stT39 (i+1)) + stT39 89 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 88
    simpa using h
  have hprev := st39_p88
  have hstep := st39_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p90 : ((17352047615617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT39 (i+1))
      = (∑ i ∈ Finset.range 89, stT39 (i+1)) + stT39 90 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 89
    simpa using h
  have hprev := st39_p89
  have hstep := st39_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p91 : ((18400258235737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT39 (i+1))
      = (∑ i ∈ Finset.range 90, stT39 (i+1)) + stT39 91 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 90
    simpa using h
  have hprev := st39_p90
  have hstep := st39_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p92 : ((19352232814081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT39 (i+1))
      = (∑ i ∈ Finset.range 91, stT39 (i+1)) + stT39 92 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 91
    simpa using h
  have hprev := st39_p91
  have hstep := st39_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p93 : ((5010792723387/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT39 (i+1))
      = (∑ i ∈ Finset.range 92, stT39 (i+1)) + stT39 93 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 92
    simpa using h
  have hprev := st39_p92
  have hstep := st39_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p94 : ((203599326597/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT39 (i+1))
      = (∑ i ∈ Finset.range 93, stT39 (i+1)) + stT39 94 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 93
    simpa using h
  have hprev := st39_p93
  have hstep := st39_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p95 : ((10128475521777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT39 (i+1))
      = (∑ i ∈ Finset.range 94, stT39 (i+1)) + stT39 95 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 94
    simpa using h
  have hprev := st39_p94
  have hstep := st39_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p96 : ((1975965958503/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT39 (i+1))
      = (∑ i ∈ Finset.range 95, stT39 (i+1)) + stT39 96 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 95
    simpa using h
  have hprev := st39_p95
  have hstep := st39_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p97 : ((3791221778499/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT39 (i+1))
      = (∑ i ∈ Finset.range 96, stT39 (i+1)) + stT39 97 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 96
    simpa using h
  have hprev := st39_p96
  have hstep := st39_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p98 : ((4494819957453/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT39 (i+1))
      = (∑ i ∈ Finset.range 97, stT39 (i+1)) + stT39 98 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 97
    simpa using h
  have hprev := st39_p97
  have hstep := st39_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p99 : ((1698377059509/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT39 (i+1))
      = (∑ i ∈ Finset.range 98, stT39 (i+1)) + stT39 99 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 98
    simpa using h
  have hprev := st39_p98
  have hstep := st39_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st39_p100 : ((1612098159509/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT39 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT39 (i+1))
      = (∑ i ∈ Finset.range 99, stT39 (i+1)) + stT39 100 := by
    have h := Finset.sum_range_succ (fun i => stT39 (i+1)) 99
    simpa using h
  have hprev := st39_p99
  have hstep := st39_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 39`.** -/
theorem station_39_sign : hardyG (((39:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 39 100 (by norm_num) (by norm_num)
    ((721/1000000 : ℚ) : ℝ)
  have hchain := st39_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT39 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((39:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((721/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((39:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((39:ℕ)):ℝ)+1) * ((((39:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((115733/260000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1612098159509/1000000000000 : ℚ) : ℝ) - ((115733/260000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((721/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((39:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((721/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((39:ℕ)):ℝ))).re
      - Real.sin ((721/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((39:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((39:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((39:ℕ)):ℝ)
      = ((((39:ℕ)):ℝ) * (Real.log (((39:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((39:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_39
  have hl30 : ((34011973/10000000 : ℚ) : ℝ) ≤ Real.log (30:ℝ)
      ∧ Real.log (30:ℝ) ≤ ((17005987/5000000 : ℚ) : ℝ) := by
    have h := log_br_30
    norm_num at h ⊢
    exact h
  have hl2 : ((6931471/10000000 : ℚ) : ℝ) ≤ Real.log (2:ℝ)
      ∧ Real.log (2:ℝ) ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := log_br_2
    norm_num at h ⊢
    exact h
  have hlπ := log_pi_enclosure
  have hπ6l := Real.pi_gt_d6
  have hπ6u := Real.pi_lt_d6
  have hθb := abs_le.mp hθ30
  have hincb := abs_le.mp hinc
  have hθwin : |(((721/1000000 : ℚ) : ℝ) + ((3:ℤ)) * (2*Real.pi) - Real.pi) - theta (((39:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((39:ℕ)):ℝ))
    (φ := ((721/1000000 : ℚ) : ℝ) + ((3:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((721/1000000 : ℚ) : ℝ) + ((3:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((721/1000000 : ℚ)) : ℝ) - Real.pi) + ((3:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((721/1000000 : ℚ)) : ℝ) - Real.pi) 3).1,
    (cos_sin_shift ((((721/1000000 : ℚ)) : ℝ) - Real.pi) 3).2]
  exact cos_sin_flip ((721/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_39_sign
end AxiomAudit
