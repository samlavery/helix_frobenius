import RequestProject.DVPSqrtTable

/-!
# Station `t = 46` of the Hardy ladder (sign -)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT46 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((46 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((80837/200000 : ℚ) : ℝ))

theorem st46_c1 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((919423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -505231/5000000) (δ := 21/100000000) (ψ := 80837/200000) 46 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t1 : ((919373/1000000 : ℚ) : ℝ) ≤ stT46 1 := by
  have hc : ((919373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((919373/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((919373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c2 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((99791/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 161647/10000000) (δ := 3/800000) (ψ := 80837/200000) 46 5
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t2 : ((352796745831/500000000000 : ℚ) : ℝ) ≤ stT46 2 := by
  have hc : ((49893/50000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352796745831/500000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((49893/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c3 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((495551/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -66751/2000000) (δ := 427/100000000) (ψ := 80837/200000) 46 8
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t3 : ((715230088013/1250000000000 : ℚ) : ℝ) ≤ stT46 3 := by
  have hc : ((247763/250000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((715230088013/1250000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((247763/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c4 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((861031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 333439/2500000) (δ := 269/100000000) (ψ := 80837/200000) 46 10
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t4 : ((860981/2000000 : ℚ) : ℝ) ≤ stT46 4 := by
  have hc : ((860981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((860981/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((860981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c5 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-49047/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2210331/5000000) (δ := 413/100000000) (ψ := 80837/200000) 46 12
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t5 : ((-54850189023/625000000000 : ℚ) : ℝ) ≤ stT46 5 := by
  have hc : ((-98119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54850189023/625000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-98119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c6 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((472149/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 419177/5000000) (δ := 321/100000000) (ψ := 80837/200000) 46 13
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t6 : ((240929716471/625000000000 : ℚ) : ℝ) ≤ stT46 6 := by
  have hc : ((118031/125000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((240929716471/625000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((118031/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c7 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((414787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2857719/10000000) (δ := 29/12500000) (ψ := 80837/200000) 46 14
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t7 : ((391889553407/2500000000000 : ℚ) : ℝ) ≤ stT46 7 := by
  have hc : ((414737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((391889553407/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((414737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c8 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((269163/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1252933/5000000) (δ := 261/100000000) (ψ := 80837/200000) 46 15
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t8 : ((475773140277/2500000000000 : ℚ) : ℝ) ≤ stT46 8 := by
  have hc : ((134569/250000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((475773140277/2500000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((134569/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c9 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((198121/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42869/1250000) (δ := 373/100000000) (ψ := 80837/200000) 46 16
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t9 : ((660369933963/2000000000000 : ℚ) : ℝ) ≤ stT46 9 := by
  have hc : ((198111/200000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((660369933963/2000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((198111/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c10 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((268057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -406069/1250000) (δ := 111/25000000) (ψ := 80837/200000) 46 17
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t10 : ((847512371939/10000000000000 : ℚ) : ℝ) ≤ stT46 10 := by
  have hc : ((268007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((847512371939/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((268007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c11 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-99839/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3856059/5000000) (δ := 81/25000000) (ψ := 80837/200000) 46 17
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t11 : ((-37630130277/125000000000 : ℚ) : ℝ) ≤ stT46 11 := by
  have hc : ((-24961/25000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37630130277/125000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-24961/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c12 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((346849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2010463/10000000) (δ := 249/100000000) (ψ := 80837/200000) 46 18
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t12 : ((125149316103/625000000000 : ℚ) : ℝ) ≤ stT46 12 := by
  have hc : ((43353/62500 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125149316103/625000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((43353/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c13 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-112157/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1123147/2500000) (δ := 57/20000000) (ψ := 80837/200000) 46 19
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t13 : ((-155568444591/2500000000000 : ℚ) : ℝ) ≤ stT46 13 := by
  have hc : ((-56091/250000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155568444591/2500000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-56091/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c14 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-41123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1007457/2500000) (δ := 169/50000000) (ψ := 80837/200000) 46 19
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t14 : ((-110039495049/10000000000000 : ℚ) : ℝ) ≤ stT46 14 := by
  have hc : ((-41173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110039495049/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-41173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c15 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((73149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -748791/2000000) (δ := 467/100000000) (ψ := 80837/200000) 46 20
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t15 : ((47185185203/2500000000000 : ℚ) : ℝ) ≤ stT46 15 := by
  have hc : ((73099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47185185203/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((73099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c16 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((49721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 147119/400000) (δ := 367/100000000) (ψ := 80837/200000) 46 20
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t16 : ((1553/62500 : ℚ) : ℝ) ≤ stT46 16 := by
  have hc : ((1553/15625 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1553/62500 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((1553/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c17 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-87437/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5058157/10000000) (δ := 69/25000000) (ψ := 80837/200000) 46 21
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t17 : ((-212090193579/2000000000000 : ℚ) : ℝ) ≤ stT46 17 := by
  have hc : ((-87447/200000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-212090193579/2000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-87447/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c18 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((821919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1515061/10000000) (δ := 267/100000000) (ψ := 80837/200000) 46 21
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t18 : ((968581657059/5000000000000 : ℚ) : ℝ) ≤ stT46 18 := by
  have hc : ((821869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((968581657059/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((821869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c19 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-39953/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7732791/10000000) (δ := 347/100000000) (ψ := 80837/200000) 46 21
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t19 : ((-9166308289/40000000000 : ℚ) : ℝ) ≤ stT46 19 := by
  have hc : ((-7991/8000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9166308289/40000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-7991/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c20 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((13489/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2076443/10000000) (δ := 337/100000000) (ψ := 80837/200000) 46 22
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t20 : ((1885004481/12500000000 : ℚ) : ℝ) ≤ stT46 20 := by
  have hc : ((843/1250 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1885004481/12500000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((843/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c21 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((156381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1767213/5000000) (δ := 143/50000000) (ψ := 80837/200000) 46 22
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t21 : ((170571034459/5000000000000 : ℚ) : ℝ) ≤ stT46 21 := by
  have hc : ((156331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170571034459/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((156331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c22 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-458141/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -852967/1250000) (δ := 47/20000000) (ψ := 80837/200000) 46 23
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t22 : ((-61050848583/312500000000 : ℚ) : ℝ) ≤ stT46 22 := by
  have hc : ((-229083/250000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61050848583/312500000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-229083/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c23 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((3873/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1711783/10000000) (δ := 79/20000000) (ψ := 80837/200000) 46 23
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t23 : ((4037620713/25000000000 : ℚ) : ℝ) ≤ stT46 23 := by
  have hc : ((15491/20000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4037620713/25000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((15491/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c24 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((146693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3182573/10000000) (δ := 63/20000000) (ψ := 80837/200000) 46 23
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t24 : ((74846183747/1250000000000 : ℚ) : ℝ) ≤ stT46 24 := by
  have hc : ((36667/125000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74846183747/1250000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((36667/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c25 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-999957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7830861/10000000) (δ := 43/12500000) (ψ := 80837/200000) 46 24
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t25 : ((-2000015000007/10000000000000 : ℚ) : ℝ) ≤ stT46 25 := by
  have hc : ((-1000007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2000015000007/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-1000007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c26 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((30029/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3320479/10000000) (δ := 71/25000000) (ψ := 80837/200000) 46 24
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t26 : ((235517785651/5000000000000 : ℚ) : ℝ) ≤ stT46 26 := by
  have hc : ((120091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235517785651/5000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((120091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c27 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((91797/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1019659/10000000) (δ := 319/100000000) (ψ := 80837/200000) 46 24
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t27 : ((22081713/125000000 : ℚ) : ℝ) ≤ stT46 27 := by
  have hc : ((5737/6250 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22081713/125000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((5737/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c28 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-488159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2600969/5000000) (δ := 101/25000000) (ψ := 80837/200000) 46 24
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t28 : ((-922628597007/10000000000000 : ℚ) : ℝ) ≤ stT46 28 := by
  have hc : ((-488209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-922628597007/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-488209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c29 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-850751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1617631/2500000) (δ := 167/50000000) (ψ := 80837/200000) 46 25
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t29 : ((-789949160077/5000000000000 : ℚ) : ℝ) ≤ stT46 29 := by
  have hc : ((-850801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-789949160077/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-850801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c30 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((5159/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -514369/2000000) (δ := 389/100000000) (ψ := 80837/200000) 46 25
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t30 : ((18836169897/200000000000 : ℚ) : ℝ) ≤ stT46 30 := by
  have hc : ((10317/20000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18836169897/200000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((10317/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c31 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((887183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 149873/1250000) (δ := 227/50000000) (ψ := 80837/200000) 46 25
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t31 : ((1593337886049/10000000000000 : ℚ) : ℝ) ≤ stT46 31 := by
  have hc : ((887133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1593337886049/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((887133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c32 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-72181/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 970017/2000000) (δ := 217/50000000) (ψ := 80837/200000) 46 25
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t32 : ((-127616867497/2000000000000 : ℚ) : ℝ) ≤ stT46 32 := by
  have hc : ((-72191/200000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127616867497/2000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-72191/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c33 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-977203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3659569/5000000) (δ := 7/2500000) (ψ := 80837/200000) 46 26
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t33 : ((-1701179545581/10000000000000 : ℚ) : ℝ) ≤ stT46 33 := by
  have hc : ((-977253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1701179545581/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-977253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c34 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((16377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3886047/10000000) (δ := 343/100000000) (ψ := 80837/200000) 46 26
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t34 : ((5600112019/2000000000000 : ℚ) : ℝ) ≤ stT46 34 := by
  have hc : ((16327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5600112019/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((16327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c35 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((3049/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3453/62500) (δ := 3/1000000) (ψ := 80837/200000) 46 26
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t35 : ((41227879851/250000000000 : ℚ) : ℝ) ≤ stT46 35 := by
  have hc : ((97563/100000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41227879851/250000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((97563/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c36 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((59481/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 268717/1000000) (δ := 303/100000000) (ψ := 80837/200000) 46 26
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t36 : ((198249087367/2500000000000 : ℚ) : ℝ) ≤ stT46 36 := by
  have hc : ((237899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198249087367/2500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((237899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c37 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-346061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1459513/2500000) (δ := 423/100000000) (ψ := 80837/200000) 46 26
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t37 : ((-28448096157/250000000000 : ℚ) : ℝ) ≤ stT46 37 := by
  have hc : ((-173043/250000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28448096157/250000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-173043/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c38 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-912939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3401531/5000000) (δ := 291/100000000) (ψ := 80837/200000) 46 27
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t38 : ((-296212890127/2000000000000 : ℚ) : ℝ) ≤ stT46 38 := by
  have hc : ((-912989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-296212890127/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-912989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c39 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((44429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3815881/10000000) (δ := 29/12500000) (ψ := 80837/200000) 46 27
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t39 : ((71063249499/10000000000000 : ℚ) : ℝ) ≤ stT46 39 := by
  have hc : ((44379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71063249499/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((44379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c40 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((187057/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -452167/5000000) (δ := 29/12500000) (ψ := 80837/200000) 46 27
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t40 : ((147873559743/1000000000000 : ℚ) : ℝ) ≤ stT46 40 := by
  have hc : ((187047/200000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147873559743/1000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((187047/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c41 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((89379/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1935317/10000000) (δ := 311/100000000) (ψ := 80837/200000) 46 27
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t41 : ((558306921867/5000000000000 : ℚ) : ℝ) ≤ stT46 41 := by
  have hc : ((357491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((558306921867/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((357491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c42 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-306789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 941307/2000000) (δ := 49/12500000) (ψ := 80837/200000) 46 27
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t42 : ((-236731504763/5000000000000 : ℚ) : ℝ) ≤ stT46 42 := by
  have hc : ((-306839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236731504763/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-306839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c43 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-984451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7412543/10000000) (δ := 93/25000000) (ψ := 80837/200000) 46 27
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t43 : ((-750675120993/5000000000000 : ℚ) : ℝ) ≤ stT46 43 := by
  have hc : ((-984501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-750675120993/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-984501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c44 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-25457/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2825813/5000000) (δ := 301/100000000) (ψ := 80837/200000) 46 28
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t44 : ((-38380893663/400000000000 : ℚ) : ℝ) ≤ stT46 44 := by
  have hc : ((-25459/40000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38380893663/400000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-25459/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c45 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((337159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -191703/625000) (δ := 201/50000000) (ψ := 80837/200000) 46 28
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t45 : ((502532094499/10000000000000 : ℚ) : ℝ) ≤ stT46 45 := by
  have hc : ((337109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((502532094499/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((337109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c46 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((976791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -539673/10000000) (δ := 231/50000000) (ψ := 80837/200000) 46 28
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t46 : ((1440125488479/10000000000000 : ℚ) : ℝ) ≤ stT46 46 := by
  have hc : ((976741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1440125488479/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((976741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c47 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((89441/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 96677/500000) (δ := 461/100000000) (ψ := 80837/200000) 46 28
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t47 : ((521815634611/5000000000000 : ℚ) : ℝ) ≤ stT46 47 := by
  have hc : ((357739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((521815634611/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((357739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c48 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-170243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2177341/5000000) (δ := 421/100000000) (ψ := 80837/200000) 46 28
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t48 : ((-15362301823/625000000000 : ℚ) : ℝ) ≤ stT46 48 := by
  have hc : ((-170293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15362301823/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-170293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c49 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-89991/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 67259/100000) (δ := 221/50000000) (ψ := 80837/200000) 46 28
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t49 : ((-8035360357/62500000000 : ℚ) : ℝ) ≤ stT46 49 := by
  have hc : ((-22499/25000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8035360357/62500000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-22499/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c50 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-443937/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -104043/156250) (δ := 451/100000000) (ψ := 80837/200000) 46 29
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t50 : ((-156964318967/1250000000000 : ℚ) : ℝ) ≤ stT46 50 := by
  have hc : ((-221981/250000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156964318967/1250000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-221981/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c51 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-11299/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87629/200000) (δ := 331/100000000) (ψ := 80837/200000) 46 29
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t51 : ((-126609207177/5000000000000 : ℚ) : ℝ) ≤ stT46 51 := by
  have hc : ((-90417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126609207177/5000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-90417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c52 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((652931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -214837/1000000) (δ := 391/100000000) (ψ := 80837/200000) 46 29
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t52 : ((3621530907/40000000000 : ℚ) : ℝ) ≤ stT46 52 := by
  have hc : ((652881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3621530907/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((652881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c53 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((499929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42173/10000000) (δ := 391/100000000) (ψ := 80837/200000) 46 29
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t53 : ((2145845731/15625000000 : ℚ) : ℝ) ≤ stT46 53 := by
  have hc : ((15622/15625 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2145845731/15625000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((15622/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c54 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((319843/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 273971/1250000) (δ := 251/100000000) (ψ := 80837/200000) 46 29
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t54 : ((217608484743/2500000000000 : ℚ) : ℝ) ≤ stT46 54 := by
  have hc : ((159909/250000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217608484743/2500000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((159909/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c55 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-14941/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4301919/10000000) (δ := 49/12500000) (ψ := 80837/200000) 46 29
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t55 : ((-25191483/1250000000 : ℚ) : ℝ) ≤ stT46 55 := by
  have hc : ((-7473/50000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25191483/1250000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-7473/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c56 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-829841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6374047/10000000) (δ := 103/25000000) (ψ := 80837/200000) 46 29
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t56 : ((-1108989152537/10000000000000 : ℚ) : ℝ) ≤ stT46 56 := by
  have hc : ((-829891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1108989152537/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-829891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c57 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-487707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1459693/2000000) (δ := 303/100000000) (ψ := 80837/200000) 46 30
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t57 : ((-161504282289/1250000000000 : ℚ) : ℝ) ≤ stT46 57 := by
  have hc : ((-121933/125000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161504282289/1250000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-121933/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c58 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-521467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2649207/5000000) (δ := 1/250000) (ψ := 80837/200000) 46 30
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t58 : ((-136957143921/2000000000000 : ℚ) : ℝ) ≤ stT46 58 := by
  have hc : ((-521517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136957143921/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-521517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c59 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((235541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1666277/5000000) (δ := 3/1250000) (ψ := 80837/200000) 46 30
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t59 : ((306583142499/10000000000000 : ℚ) : ℝ) ≤ stT46 59 := by
  have hc : ((235491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((306583142499/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((235491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c60 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((847311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -174967/1250000) (δ := 283/100000000) (ψ := 80837/200000) 46 30
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t60 : ((546904433717/5000000000000 : ℚ) : ℝ) ≤ stT46 60 := by
  have hc : ((847261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((546904433717/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((847261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c61 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((122497/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 250567/5000000) (δ := 303/100000000) (ψ := 80837/200000) 46 30
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t61 : ((39208309149/312500000000 : ℚ) : ℝ) ≤ stT46 61 := by
  have hc : ((489963/500000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39208309149/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((489963/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c62 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((582953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1185547/5000000) (δ := 403/100000000) (ψ := 80837/200000) 46 30
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t62 : ((740287392903/10000000000000 : ℚ) : ℝ) ≤ stT46 62 := by
  have hc : ((582903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((740287392903/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((582903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c63 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-28353/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4211133/10000000) (δ := 17/5000000) (ψ := 80837/200000) 46 30
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t63 : ((-35737182871/2500000000000 : ℚ) : ℝ) ≤ stT46 63 := by
  have hc : ((-56731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35737182871/2500000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-56731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c64 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-743361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3011097/5000000) (δ := 383/100000000) (ψ := 80837/200000) 46 30
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t64 : ((-929264493411/10000000000000 : ℚ) : ℝ) ≤ stT46 64 := by
  have hc : ((-743411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-929264493411/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-743411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c65 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-999809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 312207/400000) (δ := 303/100000000) (ψ := 80837/200000) 46 30
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t65 : ((-310043277733/2500000000000 : ℚ) : ℝ) ≤ stT46 65 := by
  have hc : ((-999859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-310043277733/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-999859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c66 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-775821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1536757/2500000) (δ := 249/100000000) (ψ := 80837/200000) 46 31
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t66 : ((-191006250393/2000000000000 : ℚ) : ℝ) ≤ stT46 66 := by
  have hc : ((-775871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191006250393/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-775871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c67 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-39003/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4417673/10000000) (δ := 389/100000000) (ψ := 80837/200000) 46 31
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t67 : ((-9532397407/400000000000 : ℚ) : ℝ) ≤ stT46 67 := by
  have hc : ((-39013/200000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9532397407/400000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-39013/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c68 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((116601/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1356969/5000000) (δ := 449/100000000) (ψ := 80837/200000) 46 31
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t68 : ((141384309003/2500000000000 : ℚ) : ℝ) ≤ stT46 68 := by
  have hc : ((233177/500000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141384309003/2500000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((233177/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c69 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((915507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -258769/2500000) (δ := 449/100000000) (ψ := 80837/200000) 46 31
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t69 : ((551040116553/5000000000000 : ℚ) : ℝ) ≤ stT46 69 := by
  have hc : ((915457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((551040116553/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((915457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c70 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((484721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 619629/10000000) (δ := 269/100000000) (ψ := 80837/200000) 46 31
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t70 : ((18103819709/156250000000 : ℚ) : ℝ) ≤ stT46 70 := by
  have hc : ((60587/62500 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18103819709/156250000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((60587/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c71 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((31067/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1125431/5000000) (δ := 177/50000000) (ψ := 80837/200000) 46 31
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t71 : ((73733516749/1000000000000 : ℚ) : ℝ) ≤ stT46 71 := by
  have hc : ((62129/100000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73733516749/1000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((62129/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c72 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((27081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 48241/125000) (δ := 369/100000000) (ψ := 80837/200000) 46 31
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t72 : ((31856330841/10000000000000 : ℚ) : ℝ) ≤ stT46 72 := by
  have hc : ((27031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31856330841/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((27031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c73 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-570741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 680689/1250000) (δ := 269/100000000) (ψ := 80837/200000) 46 31
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t73 : ((-167015158973/2500000000000 : ℚ) : ℝ) ≤ stT46 73 := by
  have hc : ((-570791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167015158973/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-570791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c74 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-117947/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3505081/5000000) (δ := 217/50000000) (ψ := 80837/200000) 46 31
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t74 : ((-548471760801/5000000000000 : ℚ) : ℝ) ≤ stT46 74 := by
  have hc : ((-471813/500000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-548471760801/5000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-471813/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c75 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-480537/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3577077/5000000) (δ := 399/100000000) (ψ := 80837/200000) 46 32
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t75 : ((-277452710981/2500000000000 : ℚ) : ℝ) ≤ stT46 75 := by
  have hc : ((-240281/250000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277452710981/2500000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-240281/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c76 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-25201/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5630953/10000000) (δ := 279/100000000) (ψ := 80837/200000) 46 32
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t76 : ((-28909832037/400000000000 : ℚ) : ℝ) ≤ stT46 76 := by
  have hc : ((-25203/40000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28909832037/400000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-25203/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c77 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-80183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -257979/625000) (δ := 379/100000000) (ψ := 80837/200000) 46 32
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t77 : ((-45717004099/5000000000000 : ℚ) : ℝ) ≤ stT46 77 := by
  have hc : ((-80233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45717004099/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-80233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c78 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((122761/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -660943/2500000) (δ := 339/100000000) (ψ := 80837/200000) 46 32
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t78 : ((277970606669/5000000000000 : ℚ) : ℝ) ≤ stT46 78 := by
  have hc : ((245497/500000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((277970606669/5000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((245497/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c79 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((445441/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -36837/312500) (δ := 61/25000000) (ψ := 80837/200000) 46 32
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t79 : ((62641468899/625000000000 : ℚ) : ℝ) ≤ stT46 79 := by
  have hc : ((55677/62500 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62641468899/625000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((55677/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c80 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((994269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2092/78125) (δ := 299/100000000) (ψ := 80837/200000) 46 32
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t80 : ((1111569651227/10000000000000 : ℚ) : ℝ) ≤ stT46 80 := by
  have hc : ((994219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1111569651227/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((994219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c81 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((389243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 848183/5000000) (δ := 33/12500000) (ψ := 80837/200000) 46 32
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t81 : ((216232200599/2500000000000 : ℚ) : ℝ) ≤ stT46 81 := by
  have hc : ((194609/250000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216232200599/2500000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((194609/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c82 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((64397/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1553713/5000000) (δ := 259/100000000) (ψ := 80837/200000) 46 32
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t82 : ((14220705981/400000000000 : ℚ) : ℝ) ≤ stT46 82 := by
  have hc : ((64387/200000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14220705981/400000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((64387/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c83 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-227741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4501383/10000000) (δ := 419/100000000) (ψ := 80837/200000) 46 32
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t83 : ((-250033196613/10000000000000 : ℚ) : ℝ) ≤ stT46 83 := by
  have hc : ((-227791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250033196613/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-227791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c84 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-563/800 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1175729/2000000) (δ := 29/6250000) (ψ := 80837/200000) 46 32
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t84 : ((-383954571/5000000000 : ℚ) : ℝ) ≤ stT46 84 := by
  have hc : ((-3519/5000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-383954571/5000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-3519/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c85 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-193991/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7239607/10000000) (δ := 61/25000000) (ψ := 80837/200000) 46 32
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t85 : ((-210423766653/2000000000000 : ℚ) : ℝ) ≤ stT46 85 := by
  have hc : ((-194001/200000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-210423766653/2000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-194001/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c86 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-957593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7123311/10000000) (δ := 91/20000000) (ψ := 80837/200000) 46 33
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t86 : ((-129081657613/1250000000000 : ℚ) : ℝ) ≤ stT46 86 := by
  have hc : ((-957643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129081657613/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-957643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c87 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-679243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5793817/10000000) (δ := 97/25000000) (ψ := 80837/200000) 46 33
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t87 : ((-728278856109/10000000000000 : ℚ) : ℝ) ≤ stT46 87 := by
  have hc : ((-679293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-728278856109/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-679293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c88 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-13701/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4479517/10000000) (δ := 51/12500000) (ψ := 80837/200000) 46 33
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t88 : ((-29217304133/1250000000000 : ℚ) : ℝ) ≤ stT46 88 := by
  have hc : ((-109633/500000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29217304133/1250000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-109633/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c89 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((36793/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -795017/2500000) (δ := 63/20000000) (ψ := 80837/200000) 46 33
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t89 : ((155975378559/5000000000000 : ℚ) : ℝ) ≤ stT46 89 := by
  have hc : ((147147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155975378559/5000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((147147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c90 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((363087/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -947569/5000000) (δ := 67/20000000) (ψ := 80837/200000) 46 33
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t90 : ((47837593713/625000000000 : ℚ) : ℝ) ≤ stT46 90 := by
  have hc : ((181531/250000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47837593713/625000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((181531/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c91 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((968971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -624407/10000000) (δ := 99/20000000) (ψ := 80837/200000) 46 33
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t91 : ((253926095391/2500000000000 : ℚ) : ℝ) ≤ stT46 91 := by
  have hc : ((968921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((253926095391/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((968921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c92 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((242043/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 158109/2500000) (δ := 71/20000000) (ψ := 80837/200000) 46 33
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t92 : ((126167111223/1250000000000 : ℚ) : ℝ) ≤ stT46 92 := by
  have hc : ((484061/500000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126167111223/1250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((484061/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c93 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((1463/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1875691/10000000) (δ := 83/20000000) (ψ := 80837/200000) 46 33
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t93 : ((15169556179/200000000000 : ℚ) : ℝ) ≤ stT46 93 := by
  have hc : ((14629/20000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15169556179/200000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((14629/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c94 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((161329/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 62113/200000) (δ := 79/20000000) (ψ := 80837/200000) 46 33
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t94 : ((20796541623/625000000000 : ℚ) : ℝ) ≤ stT46 94 := by
  have hc : ((20163/62500 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20796541623/625000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((20163/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c95 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-157581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 135081/312500) (δ := 83/20000000) (ψ := 80837/200000) 46 33
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t95 : ((-161726095749/10000000000000 : ℚ) : ℝ) ≤ stT46 95 := by
  have hc : ((-157631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161726095749/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-157631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c96 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-149283/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 690849/1250000) (δ := 87/20000000) (ψ := 80837/200000) 46 33
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t96 : ((-304748245011/5000000000000 : ℚ) : ℝ) ≤ stT46 96 := by
  have hc : ((-298591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-304748245011/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-298591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c97 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-449309/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 419907/625000) (δ := 71/20000000) (ψ := 80837/200000) 46 33
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t97 : ((-228114964449/2500000000000 : ℚ) : ℝ) ≤ stT46 97 := by
  have hc : ((-224667/250000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228114964449/2500000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-224667/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c98 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-199969/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3904977/5000000) (δ := 173/50000000) (ψ := 80837/200000) 46 34
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t98 : ((-202009386787/2000000000000 : ℚ) : ℝ) ≤ stT46 98 := by
  have hc : ((-199979/200000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202009386787/2000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-199979/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c99 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-221213/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6642431/10000000) (δ := 237/100000000) (ψ := 80837/200000) 46 34
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t99 : ((-222340034069/2500000000000 : ℚ) : ℝ) ≤ stT46 99 := by
  have hc : ((-442451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222340034069/2500000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-442451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_c100 :
    |Real.cos (((46 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((80837/200000 : ℚ) : ℝ))
      - ((-584173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2743321/5000000) (δ := 203/50000000) (ψ := 80837/200000) 46 34
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st46_t100 : ((-584223/10000000 : ℚ) : ℝ) ≤ stT46 100 := by
  have hc : ((-584223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((46 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((80837/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st46_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-584223/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-584223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st46_p1 : ((919373/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT46 (i+1) := by
  rw [Finset.sum_range_one]
  exact st46_t1

theorem st46_p2 : ((812483245831/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT46 (i+1))
      = (∑ i ∈ Finset.range 1, stT46 (i+1)) + stT46 2 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 1
    simpa using h
  have hprev := st46_p1
  have hstep := st46_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p3 : ((5492876405181/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT46 (i+1))
      = (∑ i ∈ Finset.range 2, stT46 (i+1)) + stT46 3 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 2
    simpa using h
  have hprev := st46_p2
  have hstep := st46_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p4 : ((6569102655181/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT46 (i+1))
      = (∑ i ∈ Finset.range 3, stT46 (i+1)) + stT46 4 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 3
    simpa using h
  have hprev := st46_p3
  have hstep := st46_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p5 : ((6349701899089/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT46 (i+1))
      = (∑ i ∈ Finset.range 4, stT46 (i+1)) + stT46 5 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 4
    simpa using h
  have hprev := st46_p4
  have hstep := st46_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p6 : ((7313420764973/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT46 (i+1))
      = (∑ i ∈ Finset.range 5, stT46 (i+1)) + stT46 6 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 5
    simpa using h
  have hprev := st46_p5
  have hstep := st46_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p7 : ((385265515919/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT46 (i+1))
      = (∑ i ∈ Finset.range 6, stT46 (i+1)) + stT46 7 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 6
    simpa using h
  have hprev := st46_p6
  have hstep := st46_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p8 : ((8181083458657/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT46 (i+1))
      = (∑ i ∈ Finset.range 7, stT46 (i+1)) + stT46 8 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 7
    simpa using h
  have hprev := st46_p7
  have hstep := st46_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p9 : ((36026183504443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT46 (i+1))
      = (∑ i ∈ Finset.range 8, stT46 (i+1)) + stT46 9 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 8
    simpa using h
  have hprev := st46_p8
  have hstep := st46_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p10 : ((18436847938191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT46 (i+1))
      = (∑ i ∈ Finset.range 9, stT46 (i+1)) + stT46 10 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 9
    simpa using h
  have hprev := st46_p9
  have hstep := st46_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p11 : ((16931642727111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT46 (i+1))
      = (∑ i ∈ Finset.range 10, stT46 (i+1)) + stT46 11 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 10
    simpa using h
  have hprev := st46_p10
  have hstep := st46_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p12 : ((3586567451187/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT46 (i+1))
      = (∑ i ∈ Finset.range 11, stT46 (i+1)) + stT46 12 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 11
    simpa using h
  have hprev := st46_p11
  have hstep := st46_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p13 : ((17621700366753/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT46 (i+1))
      = (∑ i ∈ Finset.range 12, stT46 (i+1)) + stT46 13 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 12
    simpa using h
  have hprev := st46_p12
  have hstep := st46_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p14 : ((35133361238457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT46 (i+1))
      = (∑ i ∈ Finset.range 13, stT46 (i+1)) + stT46 14 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 13
    simpa using h
  have hprev := st46_p13
  have hstep := st46_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p15 : ((35322101979269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT46 (i+1))
      = (∑ i ∈ Finset.range 14, stT46 (i+1)) + stT46 15 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 14
    simpa using h
  have hprev := st46_p14
  have hstep := st46_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p16 : ((35570581979269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT46 (i+1))
      = (∑ i ∈ Finset.range 15, stT46 (i+1)) + stT46 16 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 15
    simpa using h
  have hprev := st46_p15
  have hstep := st46_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p17 : ((17255065505687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT46 (i+1))
      = (∑ i ∈ Finset.range 16, stT46 (i+1)) + stT46 17 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 16
    simpa using h
  have hprev := st46_p16
  have hstep := st46_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p18 : ((9111823581373/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT46 (i+1))
      = (∑ i ∈ Finset.range 17, stT46 (i+1)) + stT46 18 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 17
    simpa using h
  have hprev := st46_p17
  have hstep := st46_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p19 : ((17077858626621/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT46 (i+1))
      = (∑ i ∈ Finset.range 18, stT46 (i+1)) + stT46 19 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 18
    simpa using h
  have hprev := st46_p18
  have hstep := st46_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p20 : ((17831860419021/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT46 (i+1))
      = (∑ i ∈ Finset.range 19, stT46 (i+1)) + stT46 20 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 19
    simpa using h
  have hprev := st46_p19
  have hstep := st46_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p21 : ((450060786337/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT46 (i+1))
      = (∑ i ∈ Finset.range 20, stT46 (i+1)) + stT46 21 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 20
    simpa using h
  have hprev := st46_p20
  have hstep := st46_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p22 : ((2128202234519/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT46 (i+1))
      = (∑ i ∈ Finset.range 21, stT46 (i+1)) + stT46 22 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 21
    simpa using h
  have hprev := st46_p21
  have hstep := st46_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p23 : ((278642844043/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT46 (i+1))
      = (∑ i ∈ Finset.range 22, stT46 (i+1)) + stT46 23 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 22
    simpa using h
  have hprev := st46_p22
  have hstep := st46_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p24 : ((906626337687/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT46 (i+1))
      = (∑ i ∈ Finset.range 23, stT46 (i+1)) + stT46 24 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 23
    simpa using h
  have hprev := st46_p23
  have hstep := st46_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p25 : ((34265038507473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT46 (i+1))
      = (∑ i ∈ Finset.range 24, stT46 (i+1)) + stT46 25 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 24
    simpa using h
  have hprev := st46_p24
  have hstep := st46_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p26 : ((1389442963151/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT46 (i+1))
      = (∑ i ∈ Finset.range 25, stT46 (i+1)) + stT46 26 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 25
    simpa using h
  have hprev := st46_p25
  have hstep := st46_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p27 : ((1460104444751/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT46 (i+1))
      = (∑ i ∈ Finset.range 26, stT46 (i+1)) + stT46 27 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 26
    simpa using h
  have hprev := st46_p26
  have hstep := st46_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p28 : ((4447497815221/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT46 (i+1))
      = (∑ i ∈ Finset.range 27, stT46 (i+1)) + stT46 28 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 27
    simpa using h
  have hprev := st46_p27
  have hstep := st46_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p29 : ((17000042100807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT46 (i+1))
      = (∑ i ∈ Finset.range 28, stT46 (i+1)) + stT46 29 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 28
    simpa using h
  have hprev := st46_p28
  have hstep := st46_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p30 : ((2183868293529/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT46 (i+1))
      = (∑ i ∈ Finset.range 29, stT46 (i+1)) + stT46 30 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 29
    simpa using h
  have hprev := st46_p29
  have hstep := st46_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p31 : ((36535230582513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT46 (i+1))
      = (∑ i ∈ Finset.range 30, stT46 (i+1)) + stT46 31 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 30
    simpa using h
  have hprev := st46_p30
  have hstep := st46_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p32 : ((8974286561257/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT46 (i+1))
      = (∑ i ∈ Finset.range 31, stT46 (i+1)) + stT46 32 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 31
    simpa using h
  have hprev := st46_p31
  have hstep := st46_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p33 : ((34195966699447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT46 (i+1))
      = (∑ i ∈ Finset.range 32, stT46 (i+1)) + stT46 33 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 32
    simpa using h
  have hprev := st46_p32
  have hstep := st46_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p34 : ((17111983629771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT46 (i+1))
      = (∑ i ∈ Finset.range 33, stT46 (i+1)) + stT46 34 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 33
    simpa using h
  have hprev := st46_p33
  have hstep := st46_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p35 : ((17936541226791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT46 (i+1))
      = (∑ i ∈ Finset.range 34, stT46 (i+1)) + stT46 35 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 34
    simpa using h
  have hprev := st46_p34
  have hstep := st46_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p36 : ((733321576061/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT46 (i+1))
      = (∑ i ∈ Finset.range 35, stT46 (i+1)) + stT46 36 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 35
    simpa using h
  have hprev := st46_p35
  have hstep := st46_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p37 : ((3552815495677/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT46 (i+1))
      = (∑ i ∈ Finset.range 36, stT46 (i+1)) + stT46 37 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 36
    simpa using h
  have hprev := st46_p36
  have hstep := st46_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p38 : ((6809418101227/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT46 (i+1))
      = (∑ i ∈ Finset.range 37, stT46 (i+1)) + stT46 38 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 37
    simpa using h
  have hprev := st46_p37
  have hstep := st46_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p39 : ((17059076877817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT46 (i+1))
      = (∑ i ∈ Finset.range 38, stT46 (i+1)) + stT46 39 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 38
    simpa using h
  have hprev := st46_p38
  have hstep := st46_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p40 : ((4449611169133/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT46 (i+1))
      = (∑ i ∈ Finset.range 39, stT46 (i+1)) + stT46 40 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 39
    simpa using h
  have hprev := st46_p39
  have hstep := st46_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p41 : ((18356751598399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT46 (i+1))
      = (∑ i ∈ Finset.range 40, stT46 (i+1)) + stT46 41 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 40
    simpa using h
  have hprev := st46_p40
  have hstep := st46_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p42 : ((4530005023409/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT46 (i+1))
      = (∑ i ∈ Finset.range 41, stT46 (i+1)) + stT46 42 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 41
    simpa using h
  have hprev := st46_p41
  have hstep := st46_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p43 : ((17369344972643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT46 (i+1))
      = (∑ i ∈ Finset.range 42, stT46 (i+1)) + stT46 43 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 42
    simpa using h
  have hprev := st46_p42
  have hstep := st46_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p44 : ((33779167603711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT46 (i+1))
      = (∑ i ∈ Finset.range 43, stT46 (i+1)) + stT46 44 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 43
    simpa using h
  have hprev := st46_p43
  have hstep := st46_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p45 : ((3428169969821/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT46 (i+1))
      = (∑ i ∈ Finset.range 44, stT46 (i+1)) + stT46 45 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 44
    simpa using h
  have hprev := st46_p44
  have hstep := st46_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p46 : ((35721825186689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT46 (i+1))
      = (∑ i ∈ Finset.range 45, stT46 (i+1)) + stT46 46 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 45
    simpa using h
  have hprev := st46_p45
  have hstep := st46_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p47 : ((36765456455911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT46 (i+1))
      = (∑ i ∈ Finset.range 46, stT46 (i+1)) + stT46 47 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 46
    simpa using h
  have hprev := st46_p46
  have hstep := st46_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p48 : ((36519659626743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT46 (i+1))
      = (∑ i ∈ Finset.range 47, stT46 (i+1)) + stT46 48 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 47
    simpa using h
  have hprev := st46_p47
  have hstep := st46_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p49 : ((35234001969623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT46 (i+1))
      = (∑ i ∈ Finset.range 48, stT46 (i+1)) + stT46 49 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 48
    simpa using h
  have hprev := st46_p48
  have hstep := st46_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p50 : ((33978287417887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT46 (i+1))
      = (∑ i ∈ Finset.range 49, stT46 (i+1)) + stT46 50 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 49
    simpa using h
  have hprev := st46_p49
  have hstep := st46_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p51 : ((33725069003533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT46 (i+1))
      = (∑ i ∈ Finset.range 50, stT46 (i+1)) + stT46 51 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 50
    simpa using h
  have hprev := st46_p50
  have hstep := st46_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p52 : ((34630451730283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT46 (i+1))
      = (∑ i ∈ Finset.range 51, stT46 (i+1)) + stT46 52 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 51
    simpa using h
  have hprev := st46_p51
  have hstep := st46_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p53 : ((36003792998123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT46 (i+1))
      = (∑ i ∈ Finset.range 52, stT46 (i+1)) + stT46 53 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 52
    simpa using h
  have hprev := st46_p52
  have hstep := st46_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p54 : ((7374845387419/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT46 (i+1))
      = (∑ i ∈ Finset.range 53, stT46 (i+1)) + stT46 54 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 53
    simpa using h
  have hprev := st46_p53
  have hstep := st46_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p55 : ((7334539014619/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT46 (i+1))
      = (∑ i ∈ Finset.range 54, stT46 (i+1)) + stT46 55 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 54
    simpa using h
  have hprev := st46_p54
  have hstep := st46_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p56 : ((17781852960279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT46 (i+1))
      = (∑ i ∈ Finset.range 55, stT46 (i+1)) + stT46 56 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 55
    simpa using h
  have hprev := st46_p55
  have hstep := st46_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p57 : ((17135835831123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT46 (i+1))
      = (∑ i ∈ Finset.range 56, stT46 (i+1)) + stT46 57 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 56
    simpa using h
  have hprev := st46_p56
  have hstep := st46_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p58 : ((33586885942641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT46 (i+1))
      = (∑ i ∈ Finset.range 57, stT46 (i+1)) + stT46 58 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 57
    simpa using h
  have hprev := st46_p57
  have hstep := st46_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p59 : ((1694673454257/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT46 (i+1))
      = (∑ i ∈ Finset.range 58, stT46 (i+1)) + stT46 59 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 58
    simpa using h
  have hprev := st46_p58
  have hstep := st46_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p60 : ((17493638976287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT46 (i+1))
      = (∑ i ∈ Finset.range 59, stT46 (i+1)) + stT46 60 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 59
    simpa using h
  have hprev := st46_p59
  have hstep := st46_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p61 : ((18120971922671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT46 (i+1))
      = (∑ i ∈ Finset.range 60, stT46 (i+1)) + stT46 61 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 60
    simpa using h
  have hprev := st46_p60
  have hstep := st46_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p62 : ((7396446247649/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT46 (i+1))
      = (∑ i ∈ Finset.range 61, stT46 (i+1)) + stT46 62 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 61
    simpa using h
  have hprev := st46_p61
  have hstep := st46_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p63 : ((36839282506761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT46 (i+1))
      = (∑ i ∈ Finset.range 62, stT46 (i+1)) + stT46 63 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 62
    simpa using h
  have hprev := st46_p62
  have hstep := st46_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p64 : ((718200360267/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT46 (i+1))
      = (∑ i ∈ Finset.range 63, stT46 (i+1)) + stT46 64 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 63
    simpa using h
  have hprev := st46_p63
  have hstep := st46_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p65 : ((17334922451209/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT46 (i+1))
      = (∑ i ∈ Finset.range 64, stT46 (i+1)) + stT46 65 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 64
    simpa using h
  have hprev := st46_p64
  have hstep := st46_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p66 : ((33714813650453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT46 (i+1))
      = (∑ i ∈ Finset.range 65, stT46 (i+1)) + stT46 66 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 65
    simpa using h
  have hprev := st46_p65
  have hstep := st46_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p67 : ((16738251857639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT46 (i+1))
      = (∑ i ∈ Finset.range 66, stT46 (i+1)) + stT46 67 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 66
    simpa using h
  have hprev := st46_p66
  have hstep := st46_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p68 : ((3404204095129/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT46 (i+1))
      = (∑ i ∈ Finset.range 67, stT46 (i+1)) + stT46 68 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 67
    simpa using h
  have hprev := st46_p67
  have hstep := st46_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p69 : ((8786030296099/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT46 (i+1))
      = (∑ i ∈ Finset.range 68, stT46 (i+1)) + stT46 69 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 68
    simpa using h
  have hprev := st46_p68
  have hstep := st46_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p70 : ((9075691411443/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT46 (i+1))
      = (∑ i ∈ Finset.range 69, stT46 (i+1)) + stT46 70 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 69
    simpa using h
  have hprev := st46_p69
  have hstep := st46_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p71 : ((18520050406631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT46 (i+1))
      = (∑ i ∈ Finset.range 70, stT46 (i+1)) + stT46 71 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 70
    simpa using h
  have hprev := st46_p70
  have hstep := st46_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p72 : ((37071957144103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT46 (i+1))
      = (∑ i ∈ Finset.range 71, stT46 (i+1)) + stT46 72 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 71
    simpa using h
  have hprev := st46_p71
  have hstep := st46_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p73 : ((36403896508211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT46 (i+1))
      = (∑ i ∈ Finset.range 72, stT46 (i+1)) + stT46 73 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 72
    simpa using h
  have hprev := st46_p72
  have hstep := st46_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p74 : ((35306952986609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT46 (i+1))
      = (∑ i ∈ Finset.range 73, stT46 (i+1)) + stT46 74 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 73
    simpa using h
  have hprev := st46_p73
  have hstep := st46_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p75 : ((6839428428537/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT46 (i+1))
      = (∑ i ∈ Finset.range 74, stT46 (i+1)) + stT46 75 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 74
    simpa using h
  have hprev := st46_p74
  have hstep := st46_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p76 : ((13075936071/3906250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT46 (i+1))
      = (∑ i ∈ Finset.range 75, stT46 (i+1)) + stT46 76 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 75
    simpa using h
  have hprev := st46_p75
  have hstep := st46_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p77 : ((16691481166781/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT46 (i+1))
      = (∑ i ∈ Finset.range 76, stT46 (i+1)) + stT46 77 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 76
    simpa using h
  have hprev := st46_p76
  have hstep := st46_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p78 : ((339389035469/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT46 (i+1))
      = (∑ i ∈ Finset.range 77, stT46 (i+1)) + stT46 78 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 77
    simpa using h
  have hprev := st46_p77
  have hstep := st46_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p79 : ((8735291762321/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT46 (i+1))
      = (∑ i ∈ Finset.range 78, stT46 (i+1)) + stT46 79 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 78
    simpa using h
  have hprev := st46_p78
  have hstep := st46_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p80 : ((36052736700511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT46 (i+1))
      = (∑ i ∈ Finset.range 79, stT46 (i+1)) + stT46 80 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 79
    simpa using h
  have hprev := st46_p79
  have hstep := st46_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p81 : ((36917665502907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT46 (i+1))
      = (∑ i ∈ Finset.range 80, stT46 (i+1)) + stT46 81 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 80
    simpa using h
  have hprev := st46_p80
  have hstep := st46_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p82 : ((2329573947027/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT46 (i+1))
      = (∑ i ∈ Finset.range 81, stT46 (i+1)) + stT46 82 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 81
    simpa using h
  have hprev := st46_p81
  have hstep := st46_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p83 : ((37023149955819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT46 (i+1))
      = (∑ i ∈ Finset.range 82, stT46 (i+1)) + stT46 83 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 82
    simpa using h
  have hprev := st46_p82
  have hstep := st46_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p84 : ((36255240813819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT46 (i+1))
      = (∑ i ∈ Finset.range 83, stT46 (i+1)) + stT46 84 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 83
    simpa using h
  have hprev := st46_p83
  have hstep := st46_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p85 : ((17601560990277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT46 (i+1))
      = (∑ i ∈ Finset.range 84, stT46 (i+1)) + stT46 85 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 84
    simpa using h
  have hprev := st46_p84
  have hstep := st46_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p86 : ((683409374393/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT46 (i+1))
      = (∑ i ∈ Finset.range 85, stT46 (i+1)) + stT46 86 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 85
    simpa using h
  have hprev := st46_p85
  have hstep := st46_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p87 : ((33442189863541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT46 (i+1))
      = (∑ i ∈ Finset.range 86, stT46 (i+1)) + stT46 87 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 86
    simpa using h
  have hprev := st46_p86
  have hstep := st46_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p88 : ((33208451430477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT46 (i+1))
      = (∑ i ∈ Finset.range 87, stT46 (i+1)) + stT46 88 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 87
    simpa using h
  have hprev := st46_p87
  have hstep := st46_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p89 : ((6704080437519/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT46 (i+1))
      = (∑ i ∈ Finset.range 88, stT46 (i+1)) + stT46 89 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 88
    simpa using h
  have hprev := st46_p88
  have hstep := st46_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p90 : ((34285803687003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT46 (i+1))
      = (∑ i ∈ Finset.range 89, stT46 (i+1)) + stT46 90 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 89
    simpa using h
  have hprev := st46_p89
  have hstep := st46_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p91 : ((35301508068567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT46 (i+1))
      = (∑ i ∈ Finset.range 90, stT46 (i+1)) + stT46 91 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 90
    simpa using h
  have hprev := st46_p90
  have hstep := st46_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p92 : ((36310844958351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT46 (i+1))
      = (∑ i ∈ Finset.range 91, stT46 (i+1)) + stT46 92 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 91
    simpa using h
  have hprev := st46_p91
  have hstep := st46_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p93 : ((37069322767301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT46 (i+1))
      = (∑ i ∈ Finset.range 92, stT46 (i+1)) + stT46 93 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 92
    simpa using h
  have hprev := st46_p92
  have hstep := st46_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p94 : ((37402067433269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT46 (i+1))
      = (∑ i ∈ Finset.range 93, stT46 (i+1)) + stT46 94 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 93
    simpa using h
  have hprev := st46_p93
  have hstep := st46_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p95 : ((465504266719/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT46 (i+1))
      = (∑ i ∈ Finset.range 94, stT46 (i+1)) + stT46 95 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 94
    simpa using h
  have hprev := st46_p94
  have hstep := st46_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p96 : ((18315422423749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT46 (i+1))
      = (∑ i ∈ Finset.range 95, stT46 (i+1)) + stT46 96 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 95
    simpa using h
  have hprev := st46_p95
  have hstep := st46_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p97 : ((17859192494851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT46 (i+1))
      = (∑ i ∈ Finset.range 96, stT46 (i+1)) + stT46 97 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 96
    simpa using h
  have hprev := st46_p96
  have hstep := st46_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p98 : ((34708338055767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT46 (i+1))
      = (∑ i ∈ Finset.range 97, stT46 (i+1)) + stT46 98 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 97
    simpa using h
  have hprev := st46_p97
  have hstep := st46_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p99 : ((33818977919491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT46 (i+1))
      = (∑ i ∈ Finset.range 98, stT46 (i+1)) + stT46 99 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 98
    simpa using h
  have hprev := st46_p98
  have hstep := st46_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st46_p100 : ((33234754919491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT46 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT46 (i+1))
      = (∑ i ∈ Finset.range 99, stT46 (i+1)) + stT46 100 := by
    have h := Finset.sum_range_succ (fun i => stT46 (i+1)) 99
    simpa using h
  have hprev := st46_p99
  have hstep := st46_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 46`.** -/
theorem station_46_sign : hardyG (((46:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 46 100 (by norm_num) (by norm_num)
    ((80837/200000 : ℚ) : ℝ)
  have hchain := st46_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT46 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((46:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((80837/200000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((46:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((46:ℕ)):ℝ)+1) * ((((46:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((526943/1150000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((33234754919491/10000000000000 : ℚ) : ℝ) - ((526943/1150000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((80837/200000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((46:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((80837/200000 : ℚ) : ℝ)
        * (riemannZeta (line (((46:ℕ)):ℝ))).re
      - Real.sin ((80837/200000 : ℚ) : ℝ)
        * (riemannZeta (line (((46:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((46:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((46:ℕ)):ℝ)
      = ((((46:ℕ)):ℝ) * (Real.log (((46:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((46:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_46
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
  have hθwin : |(((80837/200000 : ℚ) : ℝ) + ((4:ℤ)) * (2*Real.pi) - Real.pi) - theta (((46:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((46:ℕ)):ℝ))
    (φ := ((80837/200000 : ℚ) : ℝ) + ((4:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((80837/200000 : ℚ) : ℝ) + ((4:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((80837/200000 : ℚ)) : ℝ) - Real.pi) + ((4:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((80837/200000 : ℚ)) : ℝ) - Real.pi) 4).1,
    (cos_sin_shift ((((80837/200000 : ℚ)) : ℝ) - Real.pi) 4).2]
  exact cos_sin_flip ((80837/200000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_46_sign
end AxiomAudit
