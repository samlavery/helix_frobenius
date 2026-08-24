import RequestProject.DVPSqrtTable

/-!
# Station `t = 49` of the Hardy ladder (sign +)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT49 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((49 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((148297/500000 : ℚ) : ℝ))

theorem st49_c1 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((956337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -148297/2000000) (δ := 1/100000000) (ψ := 148297/500000) 49 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t1 : ((956287/1000000 : ℚ) : ℝ) ≤ stT49 1 := by
  have hc : ((956287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((956287/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((956287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c2 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-629489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1407307/2500000) (δ := 77/20000000) (ψ := 148297/500000) 49 5
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t2 : ((-1112878269413/2500000000000 : ℚ) : ℝ) ≤ stT49 2 := by
  have hc : ((-629539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1112878269413/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-629539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c3 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-991777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7533149/10000000) (δ := 219/50000000) (ψ := 148297/500000) 49 9
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t3 : ((-5726316159981/10000000000000 : ℚ) : ℝ) ≤ stT49 3 := by
  have hc : ((-991827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5726316159981/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-991827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c4 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((21869/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1854011/5000000) (δ := 289/100000000) (ψ := 148297/500000) 49 11
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t4 : ((43713/1000000 : ℚ) : ℝ) ≤ stT49 4 := by
  have hc : ((43713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43713/1000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((43713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c5 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-999661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7788863/10000000) (δ := 211/50000000) (ψ := 148297/500000) 49 13
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t5 : ((-558855444087/1250000000000 : ℚ) : ℝ) ≤ stT49 5 := by
  have hc : ((-999711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-558855444087/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-999711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c6 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((893833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -290609/2500000) (δ := 83/25000000) (ψ := 148297/500000) 49 14
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t6 : ((1824426504703/5000000000000 : ℚ) : ℝ) ≤ stT49 6 := by
  have hc : ((893783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1824426504703/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((893783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c7 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((13859/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2013059/10000000) (δ := 261/100000000) (ψ := 148297/500000) 49 15
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t7 : ((6547288319/25000000000 : ℚ) : ℝ) ≤ stT49 7 := by
  have hc : ((6929/10000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6547288319/25000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((6929/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c8 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((484437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 665673/2500000) (δ := 27/10000000) (ψ := 148297/500000) 49 16
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t8 : ((1712566223271/10000000000000 : ℚ) : ℝ) ≤ stT49 8 := by
  have hc : ((484387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1712566223271/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((484387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c9 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((13294/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27663/200000) (δ := 187/50000000) (ψ := 148297/500000) 49 17
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t9 : ((1417943191539/5000000000000 : ℚ) : ℝ) ≤ stT49 9 := by
  have hc : ((425383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1417943191539/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((425383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c10 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((52711/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28363/200000) (δ := 227/50000000) (ψ := 148297/500000) 49 18
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t10 : ((1333415206651/5000000000000 : ℚ) : ℝ) ≤ stT49 10 := by
  have hc : ((421663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1333415206651/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((421663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c11 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-572417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -681327/1250000) (δ := 73/20000000) (ψ := 148297/500000) 49 19
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t11 : ((-863026633119/5000000000000 : ℚ) : ℝ) ≤ stT49 11 := by
  have hc : ((-572467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-863026633119/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-572467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c12 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-490371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2604139/5000000) (δ := 53/20000000) (ψ := 148297/500000) 49 19
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t12 : ((-44241368831/312500000000 : ℚ) : ℝ) ≤ stT49 12 := by
  have hc : ((-490421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44241368831/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-490421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c13 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((480833/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -347227/5000000) (δ := 143/50000000) (ψ := 148297/500000) 49 20
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t13 : ((333380247/1250000000 : ℚ) : ℝ) ≤ stT49 13 := by
  have hc : ((60101/62500 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((333380247/1250000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((60101/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c14 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-97763/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7324191/10000000) (δ := 89/25000000) (ψ := 148297/500000) 49 21
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t14 : ((-32662003473/125000000000 : ℚ) : ℝ) ≤ stT49 14 := by
  have hc : ((-12221/12500 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32662003473/125000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-12221/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c15 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((900023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 281859/2500000) (δ := 243/50000000) (ψ := 148297/500000) 49 21
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t15 : ((580929871581/2500000000000 : ℚ) : ℝ) ≤ stT49 15 := by
  have hc : ((899973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((580929871581/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((899973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c16 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-445383/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3337279/5000000) (δ := 183/50000000) (ψ := 148297/500000) 49 22
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t16 : ((-34797513919/156250000000 : ℚ) : ℝ) ≤ stT49 16 := by
  have hc : ((-13919/15625 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34797513919/156250000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-13919/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c17 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((191021/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 375979/5000000) (δ := 133/50000000) (ψ := 148297/500000) 49 22
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t17 : ((115817418729/500000000000 : ℚ) : ℝ) ≤ stT49 17 := by
  have hc : ((191011/200000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115817418729/500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((191011/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c18 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-499599/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7753863/10000000) (δ := 267/100000000) (ψ := 148297/500000) 49 22
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t18 : ((-147203157419/625000000000 : ℚ) : ℝ) ≤ stT49 18 := by
  have hc : ((-62453/62500 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147203157419/625000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-62453/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c19 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((861619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -266173/2000000) (δ := 199/50000000) (ψ := 148297/500000) 49 23
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t19 : ((1976574552333/10000000000000 : ℚ) : ℝ) ≤ stT49 19 := by
  have hc : ((861569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1976574552333/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((861569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c20 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-398819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4952563/10000000) (δ := 87/25000000) (ψ := 148297/500000) 49 23
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t20 : ((-222974551773/2500000000000 : ℚ) : ℝ) ≤ stT49 20 := by
  have hc : ((-398869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222974551773/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-398869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c21 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-20881/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -955721/2000000) (δ := 157/50000000) (ψ := 148297/500000) 49 24
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t21 : ((-364583192067/5000000000000 : ℚ) : ℝ) ≤ stT49 21 := by
  have hc : ((-167073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-364583192067/5000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-167073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c22 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((186607/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 920097/10000000) (δ := 259/100000000) (ψ := 148297/500000) 49 24
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t22 : ((397826110179/2000000000000 : ℚ) : ℝ) ≤ stT49 22 := by
  have hc : ((186597/200000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((397826110179/2000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((186597/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c23 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-413957/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3182719/5000000) (δ := 207/50000000) (ψ := 148297/500000) 49 24
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t23 : ((-86321249739/500000000000 : ℚ) : ℝ) ≤ stT49 23 := by
  have hc : ((-206991/250000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86321249739/500000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-206991/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c24 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-16141/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1032243/2500000) (δ := 81/25000000) (ψ := 148297/500000) 49 25
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t24 : ((-16484049771/1000000000000 : ℚ) : ℝ) ≤ stT49 24 := by
  have hc : ((-16151/200000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16484049771/1000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-16151/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c25 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((469911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 435861/5000000) (δ := 91/25000000) (ψ := 148297/500000) 49 25
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t25 : ((234943/1250000 : ℚ) : ℝ) ≤ stT49 25 := by
  have hc : ((234943/250000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234943/1250000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((234943/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c26 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-321997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5676259/10000000) (δ := 157/50000000) (ψ := 148297/500000) 49 25
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t26 : ((-157884327391/1250000000000 : ℚ) : ℝ) ≤ stT49 26 := by
  have hc : ((-161011/250000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157884327391/1250000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-161011/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c27 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-558527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2704257/5000000) (δ := 1/312500) (ψ := 148297/500000) 49 26
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t27 : ((-1074981995077/10000000000000 : ℚ) : ℝ) ≤ stT49 27 := by
  have hc : ((-558577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1074981995077/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-558577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c28 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((232037/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -953477/10000000) (δ := 423/100000000) (ψ := 148297/500000) 49 26
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t28 : ((438485004639/2500000000000 : ℚ) : ℝ) ≤ stT49 28 := by
  have hc : ((464049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((438485004639/2500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((464049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c29 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((115309/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3345209/10000000) (δ := 353/100000000) (ψ := 148297/500000) 49 26
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t29 : ((53519242413/1250000000000 : ℚ) : ℝ) ≤ stT49 29 := by
  have hc : ((28821/125000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53519242413/1250000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((28821/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c30 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-15467/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7498149/10000000) (δ := 39/10000000) (ψ := 148297/500000) 49 26
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t30 : ((-451842845999/2500000000000 : ℚ) : ℝ) ≤ stT49 30 := by
  have hc : ((-494969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-451842845999/2500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-494969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c31 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-106227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4193061/10000000) (δ := 241/50000000) (ψ := 148297/500000) 49 27
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t31 : ((-95439615479/5000000000000 : ℚ) : ℝ) ≤ stT49 31 := by
  have hc : ((-106277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95439615479/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-106277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c32 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((992623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -60769/2000000) (δ := 59/12500000) (ψ := 148297/500000) 49 27
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t32 : ((877318400959/5000000000000 : ℚ) : ℝ) ≤ stT49 32 := by
  have hc : ((992573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((877318400959/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((992573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c33 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((91739/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3465683/10000000) (δ := 301/100000000) (ψ := 148297/500000) 49 27
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t33 : ((9978345629/312500000000 : ℚ) : ℝ) ≤ stT49 33 := by
  have hc : ((45857/250000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9978345629/312500000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((45857/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c34 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-957519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7122671/10000000) (δ := 93/25000000) (ψ := 148297/500000) 49 27
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t34 : ((-821108714517/5000000000000 : ℚ) : ℝ) ≤ stT49 34 := by
  have hc : ((-957569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-821108714517/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-957569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c35 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-42859/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5034319/10000000) (δ := 151/50000000) (ψ := 148297/500000) 49 28
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t35 : ((-4528337811/62500000000 : ℚ) : ℝ) ≤ stT49 35 := by
  have hc : ((-2679/6250 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4528337811/62500000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-2679/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c36 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((806047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1583387/10000000) (δ := 321/100000000) (ψ := 148297/500000) 49 28
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t36 : ((671663898001/5000000000000 : ℚ) : ℝ) ≤ stT49 36 := by
  have hc : ((805997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((671663898001/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((805997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c37 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((379443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 443247/2500000) (δ := 421/100000000) (ψ := 148297/500000) 49 28
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t37 : ((311879509201/2500000000000 : ℚ) : ℝ) ≤ stT49 37 := by
  have hc : ((189709/250000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((311879509201/2500000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((189709/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c38 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-430587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 629981/1250000) (δ := 73/25000000) (ψ := 148297/500000) 49 28
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t38 : ((-139717160191/2000000000000 : ℚ) : ℝ) ≤ stT49 38 := by
  have hc : ((-430637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139717160191/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-430637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c39 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-494597/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3743059/5000000) (δ := 261/100000000) (ψ := 148297/500000) 49 29
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t39 : ((-198007326351/1250000000000 : ℚ) : ℝ) ≤ stT49 39 := by
  have hc : ((-247311/250000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198007326351/1250000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-247311/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c40 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-182057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4384687/10000000) (δ := 63/25000000) (ψ := 148297/500000) 49 29
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t40 : ((-287936479873/10000000000000 : ℚ) : ℝ) ≤ stT49 40 := by
  have hc : ((-182107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-287936479873/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-182107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c41 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((427839/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -679921/5000000) (δ := 39/12500000) (ψ := 148297/500000) 49 29
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t41 : ((334066476459/2500000000000 : ℚ) : ℝ) ≤ stT49 41 := by
  have hc : ((213907/250000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334066476459/2500000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((213907/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c42 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((803977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 398027/2500000) (δ := 421/100000000) (ψ := 148297/500000) 49 29
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t42 : ((1240485890591/10000000000000 : ℚ) : ℝ) ≤ stT49 42 := by
  have hc : ((803927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1240485890591/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((803927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c43 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-108647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2237297/5000000) (δ := 431/100000000) (ψ := 148297/500000) 49 29
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t43 : ((-647356557/19531250000 : ℚ) : ℝ) ≤ stT49 43 := by
  have hc : ((-3396/15625 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-647356557/19531250000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-3396/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c44 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-487367/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 729081/1000000) (δ := 341/100000000) (ψ := 148297/500000) 49 29
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t44 : ((-22961600667/156250000000 : ℚ) : ℝ) ≤ stT49 44 := by
  have hc : ((-15231/15625 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22961600667/156250000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-15231/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c45 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-128061/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1416057/2500000) (δ := 443/100000000) (ψ := 148297/500000) 49 30
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t45 : ((-23864622069/250000000000 : ℚ) : ℝ) ≤ stT49 45 := by
  have hc : ((-128071/200000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23864622069/250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-128071/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c46 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((372843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -742953/2500000) (δ := 473/100000000) (ψ := 148297/500000) 49 30
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t46 : ((549653082267/10000000000000 : ℚ) : ℝ) ≤ stT49 46 := by
  have hc : ((372793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((549653082267/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((372793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c47 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((15483/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -168651/5000000) (δ := 49/10000000) (ψ := 148297/500000) 49 30
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t47 : ((722659932719/5000000000000 : ℚ) : ℝ) ≤ stT49 47 := by
  have hc : ((495431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((722659932719/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((495431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c48 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((312097/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2241741/10000000) (δ := 43/10000000) (ψ := 148297/500000) 49 30
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t48 : ((450436923/5000000000 : ℚ) : ℝ) ≤ stT49 48 := by
  have hc : ((39009/62500 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((450436923/5000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((39009/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c49 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-65989/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4767603/10000000) (δ := 463/100000000) (ψ := 148297/500000) 49 30
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t49 : ((-23571080857/500000000000 : ℚ) : ℝ) ≤ stT49 49 := by
  have hc : ((-65999/200000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23571080857/500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-65999/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c50 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-97023/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1448487/2000000) (δ := 47/10000000) (ψ := 148297/500000) 49 30
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t50 : ((-17152294499/125000000000 : ℚ) : ℝ) ≤ stT49 50 := by
  have hc : ((-24257/25000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17152294499/125000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-24257/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c51 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-187007/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3019853/5000000) (δ := 319/100000000) (ψ := 148297/500000) 49 31
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t51 : ((-523759704959/5000000000000 : ℚ) : ℝ) ≤ stT49 51 := by
  have hc : ((-374039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-523759704959/5000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-374039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c52 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((106199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3660991/10000000) (δ := 409/100000000) (ψ := 148297/500000) 49 31
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t52 : ((588808503/40000000000 : ℚ) : ℝ) ≤ stT49 52 := by
  have hc : ((106149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((588808503/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((106149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c53 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((862283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1327587/10000000) (δ := 429/100000000) (ψ := 148297/500000) 49 31
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t53 : ((236873511993/2000000000000 : ℚ) : ℝ) ≤ stT49 53 := by
  have hc : ((862233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((236873511993/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((862233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c54 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((231711/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 962199/10000000) (δ := 279/100000000) (ψ := 148297/500000) 49 31
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t54 : ((630603149319/5000000000000 : ℚ) : ℝ) ≤ stT49 54 := by
  have hc : ((463397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((630603149319/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((463397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c55 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((282893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3209969/10000000) (δ := 53/12500000) (ψ := 148297/500000) 49 31
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t55 : ((381385218357/10000000000000 : ℚ) : ℝ) ≤ stT49 55 := by
  have hc : ((282843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((381385218357/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((282843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c56 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-280709/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1354309/2500000) (δ := 227/50000000) (ψ := 148297/500000) 49 31
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t56 : ((-187573404669/2500000000000 : ℚ) : ℝ) ≤ stT49 56 := by
  have hc : ((-140367/250000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187573404669/2500000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-140367/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c57 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-248559/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3792717/5000000) (δ := 167/50000000) (ψ := 148297/500000) 49 31
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t57 : ((-658482309219/5000000000000 : ℚ) : ℝ) ≤ stT49 57 := by
  have hc : ((-497143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-658482309219/5000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-497143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c58 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-18381/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5992041/10000000) (δ := 449/100000000) (ψ := 148297/500000) 49 32
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t58 : ((-19309671277/200000000000 : ℚ) : ℝ) ≤ stT49 58 := by
  have hc : ((-73529/100000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19309671277/200000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-73529/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c59 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((11607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3897973/10000000) (δ := 289/100000000) (ψ := 148297/500000) 49 32
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t59 : ((15045931173/10000000000000 : ℚ) : ℝ) ≤ stT49 59 := by
  have hc : ((11557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15045931173/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((11557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c60 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((741401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1839101/10000000) (δ := 147/50000000) (ψ := 148297/500000) 49 32
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t60 : ((478539846447/5000000000000 : ℚ) : ℝ) ≤ stT49 60 := by
  have hc : ((741351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((478539846447/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((741351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c61 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((997241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 185739/10000000) (δ := 81/25000000) (ψ := 148297/500000) 49 32
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t61 : ((79798215393/625000000000 : ℚ) : ℝ) ≤ stT49 61 := by
  have hc : ((997191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79798215393/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((997191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c62 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((128803/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2177653/10000000) (δ := 217/50000000) (ψ := 148297/500000) 49 32
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t62 : ((163567238793/2000000000000 : ℚ) : ℝ) ≤ stT49 62 := by
  have hc : ((128793/200000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163567238793/2000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((128793/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c63 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-42091/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2068847/5000000) (δ := 379/100000000) (ψ := 148297/500000) 49 32
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t63 : ((-6632648789/625000000000 : ℚ) : ℝ) ≤ stT49 63 := by
  have hc : ((-10529/125000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6632648789/625000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-10529/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c64 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-151039/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1516717/2500000) (δ := 101/25000000) (ψ := 148297/500000) 49 32
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t64 : ((-188811401049/2000000000000 : ℚ) : ℝ) ≤ stT49 64 := by
  have hc : ((-151049/200000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188811401049/2000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-151049/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c65 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-499497/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -967729/1250000) (δ := 71/20000000) (ψ := 148297/500000) 49 33
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t65 : ((-77447639207/625000000000 : ℚ) : ℝ) ≤ stT49 65 := by
  have hc : ((-249761/250000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77447639207/625000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-249761/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c66 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-140347/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5871567/10000000) (δ := 9/3125000) (ψ := 148297/500000) 49 33
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t66 : ((-34553507331/400000000000 : ℚ) : ℝ) ≤ stT49 66 := by
  have hc : ((-140357/200000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34553507331/400000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-140357/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c67 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-40963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4029427/10000000) (δ := 199/50000000) (ψ := 148297/500000) 49 33
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t67 : ((-10021075407/2000000000000 : ℚ) : ℝ) ≤ stT49 67 := by
  have hc : ((-41013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10021075407/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-41013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c68 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((316323/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2214579/10000000) (δ := 117/25000000) (ψ := 148297/500000) 49 33
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t68 : ((95891906511/1250000000000 : ℚ) : ℝ) ≤ stT49 68 := by
  have hc : ((158149/250000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95891906511/1250000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((158149/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c69 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((492751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -213113/5000000) (δ := 117/25000000) (ψ := 148297/500000) 49 33
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t69 : ((148293034227/1250000000000 : ℚ) : ℝ) ≤ stT49 69 := by
  have hc : ((246363/250000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148293034227/1250000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((246363/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c70 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((430247/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 668197/5000000) (δ := 149/50000000) (ψ := 148297/500000) 49 33
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t70 : ((64276672577/625000000000 : ℚ) : ℝ) ≤ stT49 70 := by
  have hc : ((215111/250000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64276672577/625000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((215111/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c71 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((33461/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 768503/2500000) (δ := 3/800000) (ψ := 148297/500000) 49 33
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t71 : ((2481559071/62500000000 : ℚ) : ℝ) ≤ stT49 71 := by
  have hc : ((2091/6250 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2481559071/62500000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((2091/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c72 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-168691/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4787327/10000000) (δ := 97/25000000) (ψ := 148297/500000) 49 33
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t72 : ((-3106778603/78125000000 : ℚ) : ℝ) ≤ stT49 72 := by
  have hc : ((-42179/125000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3106778603/78125000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-42179/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c73 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-53257/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6477009/10000000) (δ := 139/50000000) (ψ := 148297/500000) 49 33
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t73 : ((-124672578843/1250000000000 : ℚ) : ℝ) ≤ stT49 73 := by
  have hc : ((-426081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124672578843/1250000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-426081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c74 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-993293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3782131/5000000) (δ := 233/50000000) (ψ := 148297/500000) 49 34
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t74 : ((-1154738390611/10000000000000 : ℚ) : ℝ) ≤ stT49 74 := by
  have hc : ((-993343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1154738390611/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-993343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c75 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-715389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2959971/5000000) (δ := 417/100000000) (ψ := 148297/500000) 49 34
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t75 : ((-826118128739/10000000000000 : ℚ) : ℝ) ≤ stT49 75 := by
  have hc : ((-715439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-826118128739/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-715439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c76 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-147623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2148701/5000000) (δ := 297/100000000) (ψ := 148297/500000) 49 34
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t76 : ((-169392597167/10000000000000 : ℚ) : ℝ) ≤ stT49 76 := by
  have hc : ((-147673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169392597167/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-147673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c77 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((236357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -337009/1250000) (δ := 387/100000000) (ψ := 148297/500000) 49 34
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t77 : ((13466256443/250000000000 : ℚ) : ℝ) ≤ stT49 77 := by
  have hc : ((59083/125000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13466256443/250000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((59083/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c78 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((90211/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -223081/2000000) (δ := 367/100000000) (ψ := 148297/500000) 49 34
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t78 : ((51069089531/500000000000 : ℚ) : ℝ) ≤ stT49 78 := by
  have hc : ((45103/50000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51069089531/500000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((45103/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c79 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((984191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 222563/5000000) (δ := 133/50000000) (ψ := 148297/500000) 49 34
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t79 : ((1107244245267/10000000000000 : ℚ) : ℝ) ≤ stT49 79 := by
  have hc : ((984141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1107244245267/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((984141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c80 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((140141/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1986027/10000000) (δ := 307/100000000) (ψ := 148297/500000) 49 34
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t80 : ((156671082323/2000000000000 : ℚ) : ℝ) ≤ stT49 80 := by
  have hc : ((140131/200000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156671082323/2000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((140131/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c81 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((83449/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 701557/2000000) (δ := 1/390625) (ψ := 148297/500000) 49 34
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t81 : ((2896666377/156250000000 : ℚ) : ℝ) ≤ stT49 81 := by
  have hc : ((2607/15625 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2896666377/156250000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((2607/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c82 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-420097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 626359/1250000) (δ := 247/100000000) (ψ := 148297/500000) 49 34
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t82 : ((-115993763613/2500000000000 : ℚ) : ℝ) ≤ stT49 82 := by
  have hc : ((-420147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115993763613/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-420147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c83 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-856009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3247869/5000000) (δ := 467/100000000) (ψ := 148297/500000) 49 34
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t83 : ((-939647168937/10000000000000 : ℚ) : ℝ) ≤ stT49 83 := by
  have hc : ((-856059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-939647168937/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-856059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c84 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-249763/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3872571/5000000) (δ := 129/25000000) (ψ := 148297/500000) 49 35
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t84 : ((-54505510059/500000000000 : ℚ) : ℝ) ≤ stT49 84 := by
  have hc : ((-499551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54505510059/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-499551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c85 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-202971/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -314771/500000) (δ := 297/100000000) (ψ := 148297/500000) 49 35
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t85 : ((-440333324451/5000000000000 : ℚ) : ℝ) ≤ stT49 85 := by
  have hc : ((-405967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-440333324451/5000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-405967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c86 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-36559/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -75979/156250) (δ := 457/100000000) (ψ := 148297/500000) 49 35
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t86 : ((-1232124531/31250000000 : ℚ) : ℝ) ≤ stT49 86 := by
  have hc : ((-9141/25000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1232124531/31250000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-9141/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c87 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((191033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -689291/2000000) (δ := 203/50000000) (ψ := 148297/500000) 49 35
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t87 : ((12797197881/625000000000 : ℚ) : ℝ) ≤ stT49 87 := by
  have hc : ((190983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12797197881/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((190983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c88 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((341631/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51161/250000) (δ := 109/25000000) (ψ := 148297/500000) 49 35
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t88 : ((182076510409/2500000000000 : ℚ) : ℝ) ≤ stT49 88 := by
  have hc : ((170803/250000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182076510409/2500000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((170803/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c89 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((965119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -165561/2500000) (δ := 347/100000000) (ψ := 148297/500000) 49 35
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t89 : ((1022970244793/10000000000000 : ℚ) : ℝ) ≤ stT49 89 := by
  have hc : ((965069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1022970244793/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((965069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c90 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((192067/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 141297/2000000) (δ := 337/100000000) (ψ := 148297/500000) 49 35
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t90 : ((50611436811/500000000000 : ℚ) : ℝ) ≤ stT49 90 := by
  have hc : ((192057/200000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50611436811/500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((192057/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c91 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((135853/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 206009/1000000) (δ := 517/100000000) (ψ := 148297/500000) 49 35
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t91 : ((35600510853/500000000000 : ℚ) : ℝ) ≤ stT49 91 := by
  have hc : ((135843/200000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35600510853/500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((135843/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c92 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((209669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3398901/10000000) (δ := 367/100000000) (ψ := 148297/500000) 49 35
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t92 : ((54635725017/2500000000000 : ℚ) : ℝ) ≤ stT49 92 := by
  have hc : ((209619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54635725017/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((209619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c93 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-156571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4723239/10000000) (δ := 477/100000000) (ψ := 148297/500000) 49 35
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t93 : ((-5074454231/156250000000 : ℚ) : ℝ) ≤ stT49 93 := by
  have hc : ((-39149/125000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5074454231/156250000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-39149/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c94 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-149271/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6033411/10000000) (δ := 387/100000000) (ψ := 148297/500000) 49 35
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t94 : ((-76985853791/1000000000000 : ℚ) : ℝ) ≤ stT49 94 := by
  have hc : ((-149281/200000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76985853791/1000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-149281/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c95 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-244523/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183243/250000) (δ := 457/100000000) (ψ := 148297/500000) 49 35
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t95 : ((-501776575509/5000000000000 : ℚ) : ℝ) ≤ stT49 95 := by
  have hc : ((-489071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-501776575509/5000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-489071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c96 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-954329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7095509/10000000) (δ := 457/100000000) (ψ := 148297/500000) 49 36
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t96 : ((-974059249359/10000000000000 : ℚ) : ℝ) ≤ stT49 96 := by
  have hc : ((-954379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-974059249359/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-954379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c97 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-344327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1456517/2500000) (δ := 377/100000000) (ψ := 148297/500000) 49 36
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t97 : ((-10926149067/156250000000 : ℚ) : ℝ) ≤ stT49 97 := by
  have hc : ((-10761/15625 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10926149067/156250000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-10761/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c98 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((-254241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4569647/10000000) (δ := 367/100000000) (ψ := 148297/500000) 49 36
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t98 : ((-256872816523/10000000000000 : ℚ) : ℝ) ≤ stT49 98 := by
  have hc : ((-254291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-256872816523/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-254291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c99 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((47619/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3325981/10000000) (δ := 247/100000000) (ψ := 148297/500000) 49 36
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t99 : ((47848806533/2000000000000 : ℚ) : ℝ) ≤ stT49 99 := by
  have hc : ((47609/200000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47848806533/2000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((47609/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_c100 :
    |Real.cos (((49 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((148297/500000 : ℚ) : ℝ))
      - ((334503/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -418963/2000000) (δ := 417/100000000) (ψ := 148297/500000) 49 36
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st49_t100 : ((167238832761/2500000000000 : ℚ) : ℝ) ≤ stT49 100 := by
  have hc : ((167239/250000 : ℚ) : ℝ)
      ≤ Real.cos (((49 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((148297/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st49_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167238832761/2500000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((167239/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st49_p1 : ((956287/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT49 (i+1) := by
  rw [Finset.sum_range_one]
  exact st49_t1

theorem st49_p2 : ((1277839230587/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT49 (i+1))
      = (∑ i ∈ Finset.range 1, stT49 (i+1)) + stT49 2 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 1
    simpa using h
  have hprev := st49_p1
  have hstep := st49_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p3 : ((-614959237633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT49 (i+1))
      = (∑ i ∈ Finset.range 2, stT49 (i+1)) + stT49 3 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 2
    simpa using h
  have hprev := st49_p2
  have hstep := st49_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p4 : ((-177829237633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT49 (i+1))
      = (∑ i ∈ Finset.range 3, stT49 (i+1)) + stT49 4 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 3
    simpa using h
  have hprev := st49_p3
  have hstep := st49_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p5 : ((-4648672790329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT49 (i+1))
      = (∑ i ∈ Finset.range 4, stT49 (i+1)) + stT49 5 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 4
    simpa using h
  have hprev := st49_p4
  have hstep := st49_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p6 : ((-999819780923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT49 (i+1))
      = (∑ i ∈ Finset.range 5, stT49 (i+1)) + stT49 6 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 5
    simpa using h
  have hprev := st49_p5
  have hstep := st49_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p7 : ((1619095546677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT49 (i+1))
      = (∑ i ∈ Finset.range 6, stT49 (i+1)) + stT49 7 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 6
    simpa using h
  have hprev := st49_p6
  have hstep := st49_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p8 : ((832915442487/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT49 (i+1))
      = (∑ i ∈ Finset.range 7, stT49 (i+1)) + stT49 8 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 7
    simpa using h
  have hprev := st49_p7
  have hstep := st49_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p9 : ((3083774076513/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT49 (i+1))
      = (∑ i ∈ Finset.range 8, stT49 (i+1)) + stT49 9 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 8
    simpa using h
  have hprev := st49_p8
  have hstep := st49_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p10 : ((1104297320791/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT49 (i+1))
      = (∑ i ∈ Finset.range 9, stT49 (i+1)) + stT49 10 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 9
    simpa using h
  have hprev := st49_p9
  have hstep := st49_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p11 : ((710832530009/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT49 (i+1))
      = (∑ i ∈ Finset.range 10, stT49 (i+1)) + stT49 11 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 10
    simpa using h
  have hprev := st49_p10
  have hstep := st49_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p12 : ((2846300748749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT49 (i+1))
      = (∑ i ∈ Finset.range 11, stT49 (i+1)) + stT49 12 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 11
    simpa using h
  have hprev := st49_p11
  have hstep := st49_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p13 : ((4179821736749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT49 (i+1))
      = (∑ i ∈ Finset.range 12, stT49 (i+1)) + stT49 13 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 12
    simpa using h
  have hprev := st49_p12
  have hstep := st49_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p14 : ((2873341597829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT49 (i+1))
      = (∑ i ∈ Finset.range 13, stT49 (i+1)) + stT49 14 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 13
    simpa using h
  have hprev := st49_p13
  have hstep := st49_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p15 : ((4035201340991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT49 (i+1))
      = (∑ i ∈ Finset.range 14, stT49 (i+1)) + stT49 15 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 14
    simpa using h
  have hprev := st49_p14
  have hstep := st49_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p16 : ((2921680895583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT49 (i+1))
      = (∑ i ∈ Finset.range 15, stT49 (i+1)) + stT49 16 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 15
    simpa using h
  have hprev := st49_p15
  have hstep := st49_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p17 : ((4079855082873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT49 (i+1))
      = (∑ i ∈ Finset.range 16, stT49 (i+1)) + stT49 17 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 16
    simpa using h
  have hprev := st49_p16
  have hstep := st49_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p18 : ((2902229823521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT49 (i+1))
      = (∑ i ∈ Finset.range 17, stT49 (i+1)) + stT49 18 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 17
    simpa using h
  have hprev := st49_p17
  have hstep := st49_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p19 : ((12449654719/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT49 (i+1))
      = (∑ i ∈ Finset.range 18, stT49 (i+1)) + stT49 19 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 18
    simpa using h
  have hprev := st49_p18
  have hstep := st49_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p20 : ((6889135992283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT49 (i+1))
      = (∑ i ∈ Finset.range 19, stT49 (i+1)) + stT49 20 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 19
    simpa using h
  have hprev := st49_p19
  have hstep := st49_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p21 : ((6159969608149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT49 (i+1))
      = (∑ i ∈ Finset.range 20, stT49 (i+1)) + stT49 21 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 20
    simpa using h
  have hprev := st49_p20
  have hstep := st49_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p22 : ((2037275039761/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT49 (i+1))
      = (∑ i ∈ Finset.range 21, stT49 (i+1)) + stT49 22 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 21
    simpa using h
  have hprev := st49_p21
  have hstep := st49_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p23 : ((802834395533/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT49 (i+1))
      = (∑ i ∈ Finset.range 22, stT49 (i+1)) + stT49 23 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 22
    simpa using h
  have hprev := st49_p22
  have hstep := st49_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p24 : ((3128917333277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT49 (i+1))
      = (∑ i ∈ Finset.range 23, stT49 (i+1)) + stT49 24 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 23
    simpa using h
  have hprev := st49_p23
  have hstep := st49_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p25 : ((4068689333277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT49 (i+1))
      = (∑ i ∈ Finset.range 24, stT49 (i+1)) + stT49 25 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 24
    simpa using h
  have hprev := st49_p24
  have hstep := st49_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p26 : ((3437152023713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT49 (i+1))
      = (∑ i ∈ Finset.range 25, stT49 (i+1)) + stT49 26 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 25
    simpa using h
  have hprev := st49_p25
  have hstep := st49_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p27 : ((5799322052349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT49 (i+1))
      = (∑ i ∈ Finset.range 26, stT49 (i+1)) + stT49 27 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 26
    simpa using h
  have hprev := st49_p26
  have hstep := st49_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p28 : ((1510652414181/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT49 (i+1))
      = (∑ i ∈ Finset.range 27, stT49 (i+1)) + stT49 28 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 27
    simpa using h
  have hprev := st49_p27
  have hstep := st49_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p29 : ((7981416010209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT49 (i+1))
      = (∑ i ∈ Finset.range 28, stT49 (i+1)) + stT49 29 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 28
    simpa using h
  have hprev := st49_p28
  have hstep := st49_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p30 : ((6174044626213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT49 (i+1))
      = (∑ i ∈ Finset.range 29, stT49 (i+1)) + stT49 30 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 29
    simpa using h
  have hprev := st49_p29
  have hstep := st49_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p31 : ((1196633079051/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT49 (i+1))
      = (∑ i ∈ Finset.range 30, stT49 (i+1)) + stT49 31 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 30
    simpa using h
  have hprev := st49_p30
  have hstep := st49_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p32 : ((7737802197173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT49 (i+1))
      = (∑ i ∈ Finset.range 31, stT49 (i+1)) + stT49 32 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 31
    simpa using h
  have hprev := st49_p31
  have hstep := st49_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p33 : ((8057109257301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT49 (i+1))
      = (∑ i ∈ Finset.range 32, stT49 (i+1)) + stT49 33 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 32
    simpa using h
  have hprev := st49_p32
  have hstep := st49_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p34 : ((6414891828267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT49 (i+1))
      = (∑ i ∈ Finset.range 33, stT49 (i+1)) + stT49 34 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 33
    simpa using h
  have hprev := st49_p33
  have hstep := st49_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p35 : ((5690357778507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT49 (i+1))
      = (∑ i ∈ Finset.range 34, stT49 (i+1)) + stT49 35 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 34
    simpa using h
  have hprev := st49_p34
  have hstep := st49_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p36 : ((7033685574509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT49 (i+1))
      = (∑ i ∈ Finset.range 35, stT49 (i+1)) + stT49 36 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 35
    simpa using h
  have hprev := st49_p35
  have hstep := st49_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p37 : ((8281203611313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT49 (i+1))
      = (∑ i ∈ Finset.range 36, stT49 (i+1)) + stT49 37 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 36
    simpa using h
  have hprev := st49_p36
  have hstep := st49_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p38 : ((3791308905179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT49 (i+1))
      = (∑ i ∈ Finset.range 37, stT49 (i+1)) + stT49 38 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 37
    simpa using h
  have hprev := st49_p37
  have hstep := st49_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p39 : ((119971183991/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT49 (i+1))
      = (∑ i ∈ Finset.range 38, stT49 (i+1)) + stT49 39 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 38
    simpa using h
  have hprev := st49_p38
  have hstep := st49_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p40 : ((5710622719677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT49 (i+1))
      = (∑ i ∈ Finset.range 39, stT49 (i+1)) + stT49 40 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 39
    simpa using h
  have hprev := st49_p39
  have hstep := st49_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p41 : ((7046888625513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT49 (i+1))
      = (∑ i ∈ Finset.range 40, stT49 (i+1)) + stT49 41 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 40
    simpa using h
  have hprev := st49_p40
  have hstep := st49_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p42 : ((1035921814513/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT49 (i+1))
      = (∑ i ∈ Finset.range 41, stT49 (i+1)) + stT49 42 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 41
    simpa using h
  have hprev := st49_p41
  have hstep := st49_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p43 : ((198898198973/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT49 (i+1))
      = (∑ i ∈ Finset.range 42, stT49 (i+1)) + stT49 43 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 42
    simpa using h
  have hprev := st49_p42
  have hstep := st49_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p44 : ((810798189529/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT49 (i+1))
      = (∑ i ∈ Finset.range 43, stT49 (i+1)) + stT49 44 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 43
    simpa using h
  have hprev := st49_p43
  have hstep := st49_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p45 : ((43217192449/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT49 (i+1))
      = (∑ i ∈ Finset.range 44, stT49 (i+1)) + stT49 45 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 44
    simpa using h
  have hprev := st49_p44
  have hstep := st49_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p46 : ((6081453715739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT49 (i+1))
      = (∑ i ∈ Finset.range 45, stT49 (i+1)) + stT49 46 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 45
    simpa using h
  have hprev := st49_p45
  have hstep := st49_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p47 : ((7526773581177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT49 (i+1))
      = (∑ i ∈ Finset.range 46, stT49 (i+1)) + stT49 47 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 46
    simpa using h
  have hprev := st49_p46
  have hstep := st49_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p48 : ((8427647427177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT49 (i+1))
      = (∑ i ∈ Finset.range 47, stT49 (i+1)) + stT49 48 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 47
    simpa using h
  have hprev := st49_p47
  have hstep := st49_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p49 : ((7956225810037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT49 (i+1))
      = (∑ i ∈ Finset.range 48, stT49 (i+1)) + stT49 49 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 48
    simpa using h
  have hprev := st49_p48
  have hstep := st49_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p50 : ((6584042250117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT49 (i+1))
      = (∑ i ∈ Finset.range 49, stT49 (i+1)) + stT49 50 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 49
    simpa using h
  have hprev := st49_p49
  have hstep := st49_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p51 : ((5536522840199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT49 (i+1))
      = (∑ i ∈ Finset.range 50, stT49 (i+1)) + stT49 51 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 50
    simpa using h
  have hprev := st49_p50
  have hstep := st49_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p52 : ((5683724965949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT49 (i+1))
      = (∑ i ∈ Finset.range 51, stT49 (i+1)) + stT49 52 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 51
    simpa using h
  have hprev := st49_p51
  have hstep := st49_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p53 : ((3434046262957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT49 (i+1))
      = (∑ i ∈ Finset.range 52, stT49 (i+1)) + stT49 53 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 52
    simpa using h
  have hprev := st49_p52
  have hstep := st49_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p54 : ((1016162353069/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT49 (i+1))
      = (∑ i ∈ Finset.range 53, stT49 (i+1)) + stT49 54 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 53
    simpa using h
  have hprev := st49_p53
  have hstep := st49_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p55 : ((8510684042909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT49 (i+1))
      = (∑ i ∈ Finset.range 54, stT49 (i+1)) + stT49 55 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 54
    simpa using h
  have hprev := st49_p54
  have hstep := st49_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p56 : ((7760390424233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT49 (i+1))
      = (∑ i ∈ Finset.range 55, stT49 (i+1)) + stT49 56 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 55
    simpa using h
  have hprev := st49_p55
  have hstep := st49_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p57 : ((1288685161159/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT49 (i+1))
      = (∑ i ∈ Finset.range 56, stT49 (i+1)) + stT49 57 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 56
    simpa using h
  have hprev := st49_p56
  have hstep := st49_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p58 : ((1095588448389/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT49 (i+1))
      = (∑ i ∈ Finset.range 57, stT49 (i+1)) + stT49 58 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 57
    simpa using h
  have hprev := st49_p57
  have hstep := st49_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p59 : ((2746494086559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT49 (i+1))
      = (∑ i ∈ Finset.range 58, stT49 (i+1)) + stT49 59 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 58
    simpa using h
  have hprev := st49_p58
  have hstep := st49_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p60 : ((1612516966503/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT49 (i+1))
      = (∑ i ∈ Finset.range 59, stT49 (i+1)) + stT49 60 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 59
    simpa using h
  have hprev := st49_p59
  have hstep := st49_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p61 : ((77268393123/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT49 (i+1))
      = (∑ i ∈ Finset.range 60, stT49 (i+1)) + stT49 61 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 60
    simpa using h
  have hprev := st49_p60
  have hstep := st49_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p62 : ((1708935101253/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT49 (i+1))
      = (∑ i ∈ Finset.range 61, stT49 (i+1)) + stT49 62 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 61
    simpa using h
  have hprev := st49_p61
  have hstep := st49_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p63 : ((8438553125641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT49 (i+1))
      = (∑ i ∈ Finset.range 62, stT49 (i+1)) + stT49 63 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 62
    simpa using h
  have hprev := st49_p62
  have hstep := st49_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p64 : ((1873624030099/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT49 (i+1))
      = (∑ i ∈ Finset.range 63, stT49 (i+1)) + stT49 64 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 63
    simpa using h
  have hprev := st49_p63
  have hstep := st49_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p65 : ((1563833473271/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT49 (i+1))
      = (∑ i ∈ Finset.range 64, stT49 (i+1)) + stT49 65 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 64
    simpa using h
  have hprev := st49_p64
  have hstep := st49_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p66 : ((5391496209809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT49 (i+1))
      = (∑ i ∈ Finset.range 65, stT49 (i+1)) + stT49 66 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 65
    simpa using h
  have hprev := st49_p65
  have hstep := st49_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p67 : ((2670695416387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT49 (i+1))
      = (∑ i ∈ Finset.range 66, stT49 (i+1)) + stT49 67 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 66
    simpa using h
  have hprev := st49_p66
  have hstep := st49_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p68 : ((3054263042431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT49 (i+1))
      = (∑ i ∈ Finset.range 67, stT49 (i+1)) + stT49 68 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 67
    simpa using h
  have hprev := st49_p67
  have hstep := st49_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p69 : ((3647435179339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT49 (i+1))
      = (∑ i ∈ Finset.range 68, stT49 (i+1)) + stT49 69 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 68
    simpa using h
  have hprev := st49_p68
  have hstep := st49_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p70 : ((832329711991/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT49 (i+1))
      = (∑ i ∈ Finset.range 69, stT49 (i+1)) + stT49 70 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 69
    simpa using h
  have hprev := st49_p69
  have hstep := st49_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p71 : ((872034657127/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT49 (i+1))
      = (∑ i ∈ Finset.range 70, stT49 (i+1)) + stT49 71 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 70
    simpa using h
  have hprev := st49_p70
  have hstep := st49_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p72 : ((4161339455043/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT49 (i+1))
      = (∑ i ∈ Finset.range 71, stT49 (i+1)) + stT49 72 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 71
    simpa using h
  have hprev := st49_p71
  have hstep := st49_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p73 : ((3662649139671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT49 (i+1))
      = (∑ i ∈ Finset.range 72, stT49 (i+1)) + stT49 73 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 72
    simpa using h
  have hprev := st49_p72
  have hstep := st49_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p74 : ((6170559888731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT49 (i+1))
      = (∑ i ∈ Finset.range 73, stT49 (i+1)) + stT49 74 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 73
    simpa using h
  have hprev := st49_p73
  have hstep := st49_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p75 : ((668055219999/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT49 (i+1))
      = (∑ i ∈ Finset.range 74, stT49 (i+1)) + stT49 75 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 74
    simpa using h
  have hprev := st49_p74
  have hstep := st49_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p76 : ((207001966513/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT49 (i+1))
      = (∑ i ∈ Finset.range 75, stT49 (i+1)) + stT49 76 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 75
    simpa using h
  have hprev := st49_p75
  have hstep := st49_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p77 : ((1142739884109/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT49 (i+1))
      = (∑ i ∈ Finset.range 76, stT49 (i+1)) + stT49 77 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 76
    simpa using h
  have hprev := st49_p76
  have hstep := st49_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p78 : ((1347016242233/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT49 (i+1))
      = (∑ i ∈ Finset.range 77, stT49 (i+1)) + stT49 78 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 77
    simpa using h
  have hprev := st49_p77
  have hstep := st49_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p79 : ((490145341027/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT49 (i+1))
      = (∑ i ∈ Finset.range 78, stT49 (i+1)) + stT49 79 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 78
    simpa using h
  have hprev := st49_p78
  have hstep := st49_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p80 : ((8625680868047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT49 (i+1))
      = (∑ i ∈ Finset.range 79, stT49 (i+1)) + stT49 80 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 79
    simpa using h
  have hprev := st49_p79
  have hstep := st49_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p81 : ((352442700647/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT49 (i+1))
      = (∑ i ∈ Finset.range 80, stT49 (i+1)) + stT49 81 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 80
    simpa using h
  have hprev := st49_p80
  have hstep := st49_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p82 : ((8347092461723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT49 (i+1))
      = (∑ i ∈ Finset.range 81, stT49 (i+1)) + stT49 82 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 81
    simpa using h
  have hprev := st49_p81
  have hstep := st49_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p83 : ((3703722646393/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT49 (i+1))
      = (∑ i ∈ Finset.range 82, stT49 (i+1)) + stT49 83 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 82
    simpa using h
  have hprev := st49_p82
  have hstep := st49_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p84 : ((3158667545803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT49 (i+1))
      = (∑ i ∈ Finset.range 83, stT49 (i+1)) + stT49 84 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 83
    simpa using h
  have hprev := st49_p83
  have hstep := st49_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p85 : ((339791777669/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT49 (i+1))
      = (∑ i ∈ Finset.range 84, stT49 (i+1)) + stT49 85 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 84
    simpa using h
  have hprev := st49_p84
  have hstep := st49_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p86 : ((315149287049/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT49 (i+1))
      = (∑ i ∈ Finset.range 85, stT49 (i+1)) + stT49 86 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 85
    simpa using h
  have hprev := st49_p85
  have hstep := st49_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p87 : ((32794648493/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT49 (i+1))
      = (∑ i ∈ Finset.range 86, stT49 (i+1)) + stT49 87 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 86
    simpa using h
  have hprev := st49_p86
  have hstep := st49_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p88 : ((1493862450129/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT49 (i+1))
      = (∑ i ∈ Finset.range 87, stT49 (i+1)) + stT49 88 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 87
    simpa using h
  have hprev := st49_p87
  have hstep := st49_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p89 : ((6998420045309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT49 (i+1))
      = (∑ i ∈ Finset.range 88, stT49 (i+1)) + stT49 89 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 88
    simpa using h
  have hprev := st49_p88
  have hstep := st49_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p90 : ((8010648781529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT49 (i+1))
      = (∑ i ∈ Finset.range 89, stT49 (i+1)) + stT49 90 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 89
    simpa using h
  have hprev := st49_p89
  have hstep := st49_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p91 : ((8722658998589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT49 (i+1))
      = (∑ i ∈ Finset.range 90, stT49 (i+1)) + stT49 91 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 90
    simpa using h
  have hprev := st49_p90
  have hstep := st49_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p92 : ((8941201898657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT49 (i+1))
      = (∑ i ∈ Finset.range 91, stT49 (i+1)) + stT49 92 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 91
    simpa using h
  have hprev := st49_p91
  have hstep := st49_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p93 : ((8616436827873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT49 (i+1))
      = (∑ i ∈ Finset.range 92, stT49 (i+1)) + stT49 93 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 92
    simpa using h
  have hprev := st49_p92
  have hstep := st49_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p94 : ((7846578289963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT49 (i+1))
      = (∑ i ∈ Finset.range 93, stT49 (i+1)) + stT49 94 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 93
    simpa using h
  have hprev := st49_p93
  have hstep := st49_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p95 : ((1368605027789/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT49 (i+1))
      = (∑ i ∈ Finset.range 94, stT49 (i+1)) + stT49 95 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 94
    simpa using h
  have hprev := st49_p94
  have hstep := st49_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p96 : ((2934482944793/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT49 (i+1))
      = (∑ i ∈ Finset.range 95, stT49 (i+1)) + stT49 96 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 95
    simpa using h
  have hprev := st49_p95
  have hstep := st49_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p97 : ((2584846174649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT49 (i+1))
      = (∑ i ∈ Finset.range 96, stT49 (i+1)) + stT49 97 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 96
    simpa using h
  have hprev := st49_p96
  have hstep := st49_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p98 : ((196512781311/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT49 (i+1))
      = (∑ i ∈ Finset.range 97, stT49 (i+1)) + stT49 98 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 97
    simpa using h
  have hprev := st49_p97
  have hstep := st49_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p99 : ((8050099321/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT49 (i+1))
      = (∑ i ∈ Finset.range 98, stT49 (i+1)) + stT49 99 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 98
    simpa using h
  have hprev := st49_p98
  have hstep := st49_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st49_p100 : ((1455254724121/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT49 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT49 (i+1))
      = (∑ i ∈ Finset.range 99, stT49 (i+1)) + stT49 100 := by
    have h := Finset.sum_range_succ (fun i => stT49 (i+1)) 99
    simpa using h
  have hprev := st49_p99
  have hstep := st49_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 49`.** -/
theorem station_49_sign : 0 < hardyG (((49:ℕ)):ℝ) := by
  have hcore := phase_station_lower 49 100 (by norm_num) (by norm_num)
    ((148297/500000 : ℚ) : ℝ)
  have hchain := st49_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT49 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((49:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((148297/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((49:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((49:ℕ)):ℝ)+1) * ((((49:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((368299/784000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1455254724121/2500000000000 : ℚ) : ℝ) - ((368299/784000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((148297/500000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((49:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((148297/500000 : ℚ) : ℝ)
        * (riemannZeta (line (((49:ℕ)):ℝ))).re
      - Real.sin ((148297/500000 : ℚ) : ℝ)
        * (riemannZeta (line (((49:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((49:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((49:ℕ)):ℝ)
      = ((((49:ℕ)):ℝ) * (Real.log (((49:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((49:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_49
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
  have hθwin : |(((148297/500000 : ℚ) : ℝ) + ((4:ℤ)) * (2*Real.pi)) - theta (((49:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((49:ℕ)):ℝ))
    (φ := ((148297/500000 : ℚ) : ℝ) + ((4:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((148297/500000 : ℚ)) : ℝ) 4).1,
    (cos_sin_shift (((148297/500000 : ℚ)) : ℝ) 4).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_49_sign
end AxiomAudit
