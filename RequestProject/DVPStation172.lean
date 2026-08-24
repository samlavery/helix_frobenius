import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 172` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT172 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((172 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((32731/100000 : ℚ) : ℝ))

theorem st172_c1 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((946911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32731/400000) (δ := 1/1000000000) (ψ := 32731/100000) 172 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t1 : ((946861/1000000 : ℚ) : ℝ) ≤ stT172 1 := by
  have hc : ((946861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((946861/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((946861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c2 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((176793/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1216303/10000000) (δ := 1753/200000000) (ψ := 32731/100000) 172 19
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t2 : ((1250044437461/2000000000000 : ℚ) : ℝ) ≤ stT172 2 := by
  have hc : ((176783/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1250044437461/2000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((176783/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c3 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((990433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 173047/5000000) (δ := 4393/500000000) (ψ := 32731/100000) 172 30
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t3 : ((2858989115633/5000000000000 : ℚ) : ℝ) ≤ stT172 3 := by
  have hc : ((990383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2858989115633/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((990383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c4 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((159733/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1614309/10000000) (δ := 8729/1000000000) (ψ := 32731/100000) 172 38
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t4 : ((159723/400000 : ℚ) : ℝ) ≤ stT172 4 := by
  have hc : ((159723/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159723/400000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((159723/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c5 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((999357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4483/500000) (δ := 8717/1000000000) (ψ := 32731/100000) 172 44
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t5 : ((893807162089/2000000000000 : ℚ) : ℝ) ≤ stT172 5 := by
  have hc : ((999307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((893807162089/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((999307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c6 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((124973/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6489/1250000) (δ := 7/800000) (ψ := 32731/100000) 172 49
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t6 : ((1020349014947/2500000000000 : ℚ) : ℝ) ≤ stT172 6 := by
  have hc : ((499867/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1020349014947/2500000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((499867/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c7 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((208833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 850259/2500000) (δ := 8721/1000000000) (ψ := 32731/100000) 172 53
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t7 : ((197281353313/2500000000000 : ℚ) : ℝ) ≤ stT172 7 := by
  have hc : ((208783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197281353313/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((208783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c8 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((138633/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -402463/2000000) (δ := 2173/250000000) (ψ := 32731/100000) 172 57
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t8 : ((490106191059/2000000000000 : ℚ) : ℝ) ≤ stT172 8 := by
  have hc : ((138623/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((490106191059/2000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((138623/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c9 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((10287/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 302097/2000000) (δ := 8771/1000000000) (ψ := 32731/100000) 172 60
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t9 : ((274303305903/1000000000000 : ℚ) : ℝ) ≤ stT172 9 := by
  have hc : ((82291/100000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274303305903/1000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((82291/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c10 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((992401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -308389/10000000) (δ := 4377/500000000) (ψ := 32731/100000) 172 63
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t10 : ((3138088743227/10000000000000 : ℚ) : ℝ) ≤ stT172 10 := by
  have hc : ((992351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3138088743227/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((992351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c11 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-211543/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6448893/10000000) (δ := 347/40000000) (ψ := 32731/100000) 172 66
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t11 : ((-637863949827/2500000000000 : ℚ) : ℝ) ≤ stT172 11 := by
  have hc : ((-423111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-637863949827/2500000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-423111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c12 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((19677/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -224959/5000000) (δ := 8713/1000000000) (ψ := 32731/100000) 172 68
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t12 : ((14199928169/50000000000 : ℚ) : ℝ) ≤ stT172 12 := by
  have hc : ((4919/5000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14199928169/50000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((4919/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c13 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((130627/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2552517/10000000) (δ := 17/1953125) (ψ := 32731/100000) 172 70
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t13 : ((1449037263/10000000000 : ℚ) : ℝ) ≤ stT172 13 := by
  have hc : ((261229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1449037263/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((261229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c14 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((90307/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 300303/1000000) (δ := 1737/200000000) (ψ := 32731/100000) 172 72
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t14 : ((120661082117/1250000000000 : ℚ) : ℝ) ≤ stT172 14 := by
  have hc : ((180589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120661082117/1250000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((180589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c15 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((175361/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1254051/10000000) (δ := 8733/1000000000) (ψ := 32731/100000) 172 74
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t15 : ((113188544447/500000000000 : ℚ) : ℝ) ≤ stT172 15 := by
  have hc : ((175351/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113188544447/500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((175351/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c16 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((570133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2410321/10000000) (δ := 541/62500000) (ψ := 32731/100000) 172 76
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t16 : ((570083/4000000 : ℚ) : ℝ) ≤ stT172 16 := by
  have hc : ((570083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((570083/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((570083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c17 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-499629/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7757669/10000000) (δ := 4381/500000000) (ψ := 32731/100000) 172 78
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t17 : ((-605919663239/2500000000000 : ℚ) : ℝ) ≤ stT172 17 := by
  have hc : ((-249827/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-605919663239/2500000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-249827/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c18 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((451307/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1112479/10000000) (δ := 4367/500000000) (ψ := 32731/100000) 172 79
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t18 : ((265920400551/1250000000000 : ℚ) : ℝ) ≤ stT172 18 := by
  have hc : ((225641/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((265920400551/1250000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((225641/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c19 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-949307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7054551/10000000) (δ := 8683/1000000000) (ψ := 32731/100000) 172 81
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t19 : ((-1088987478203/5000000000000 : ℚ) : ℝ) ≤ stT172 19 := by
  have hc : ((-949357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1088987478203/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-949357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c20 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((192069/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -141279/2000000) (δ := 879/100000000) (ψ := 32731/100000) 172 82
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t20 : ((429456791953/2000000000000 : ℚ) : ℝ) ≤ stT172 20 := by
  have hc : ((192059/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((429456791953/2000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((192059/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c21 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-3947/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4565427/10000000) (δ := 4353/500000000) (ψ := 32731/100000) 172 83
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t21 : ((-275672490891/5000000000000 : ℚ) : ℝ) ≤ stT172 21 := by
  have hc : ((-126329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275672490891/5000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-126329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c22 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-459977/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6846899/10000000) (δ := 1089/125000000) (ψ := 32731/100000) 172 85
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t22 : ((-61295496501/312500000000 : ℚ) : ℝ) ≤ stT172 22 := by
  have hc : ((-230001/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61295496501/312500000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-230001/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c23 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((24167/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3440589/10000000) (δ := 549/62500000) (ψ := 32731/100000) 172 86
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t23 : ((25189321449/625000000000 : ℚ) : ℝ) ≤ stT172 23 := by
  have hc : ((96643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25189321449/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((96643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c24 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((943031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -211981/2500000) (δ := 8677/1000000000) (ψ := 32731/100000) 172 87
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t24 : ((1924851479421/10000000000000 : ℚ) : ℝ) ≤ stT172 24 := by
  have hc : ((942981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1924851479421/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((942981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c25 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((921439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 997573/10000000) (δ := 8633/1000000000) (ψ := 32731/100000) 172 88
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t25 : ((921389/5000000 : ℚ) : ℝ) ≤ stT172 25 := by
  have hc : ((921389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((921389/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((921389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c26 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((651069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2154511/10000000) (δ := 437/50000000) (ψ := 32731/100000) 172 89
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t26 : ((1276753073059/10000000000000 : ℚ) : ℝ) ≤ stT172 26 := by
  have hc : ((651019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1276753073059/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((651019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c27 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((60021/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 668719/2500000) (δ := 1751/200000000) (ψ := 32731/100000) 172 90
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t27 : ((923987091/10000000000 : ℚ) : ℝ) ≤ stT172 27 := by
  have hc : ((240059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((923987091/10000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((240059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c28 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((252243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 81407/312500) (δ := 1081/125000000) (ψ := 32731/100000) 172 91
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t28 : ((119161781299/1250000000000 : ℚ) : ℝ) ≤ stT172 28 := by
  have hc : ((126109/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119161781299/1250000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((126109/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c29 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((350311/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24829/125000) (δ := 4331/500000000) (ψ := 32731/100000) 172 92
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t29 : ((325232319279/2500000000000 : ℚ) : ℝ) ≤ stT172 29 := by
  have hc : ((175143/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((325232319279/2500000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((175143/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c30 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((941951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 428001/5000000) (δ := 8769/1000000000) (ψ := 32731/100000) 172 93
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t30 : ((1719667273641/10000000000000 : ℚ) : ℝ) ≤ stT172 30 := by
  have hc : ((941901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1719667273641/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((941901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c31 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((119383/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -150461/2000000) (δ := 8727/1000000000) (ψ := 32731/100000) 172 94
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t31 : ((857627879871/5000000000000 : ℚ) : ℝ) ≤ stT172 31 := by
  have hc : ((477507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((857627879871/5000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((477507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c32 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((216341/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2808327/10000000) (δ := 8619/1000000000) (ψ := 32731/100000) 172 95
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t32 : ((47799508757/625000000000 : ℚ) : ℝ) ≤ stT172 32 := by
  have hc : ((54079/125000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47799508757/625000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((54079/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c33 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-516711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2642251/5000000) (δ := 8691/1000000000) (ψ := 32731/100000) 172 96
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t33 : ((-899565663297/10000000000000 : ℚ) : ℝ) ≤ stT172 33 := by
  have hc : ((-516761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-899565663297/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-516761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c34 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-992727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 236009/312500) (δ := 8691/1000000000) (ψ := 32731/100000) 172 96
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t34 : ((-851299328061/5000000000000 : ℚ) : ℝ) ≤ stT172 34 := by
  have hc : ((-992777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-851299328061/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-992777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c35 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-15219/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 86179/200000) (δ := 4399/500000000) (ψ := 32731/100000) 172 97
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t35 : ((-3216658027/125000000000 : ℚ) : ℝ) ≤ stT172 35 := by
  have hc : ((-1903/12500 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3216658027/125000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-1903/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c36 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((959439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 714473/10000000) (δ := 4349/500000000) (ψ := 32731/100000) 172 98
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t36 : ((799490513537/5000000000000 : ℚ) : ℝ) ≤ stT172 36 := by
  have hc : ((959389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((799490513537/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((959389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c37 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((8817/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40149/125000) (δ := 2153/250000000) (ψ := 32731/100000) 172 99
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t37 : ((231879716483/5000000000000 : ℚ) : ℝ) ≤ stT172 37 := by
  have hc : ((141047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((231879716483/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((141047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c38 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-15424/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7452557/10000000) (δ := 8719/1000000000) (ψ := 32731/100000) 172 100
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t38 : ((-160142793699/1000000000000 : ℚ) : ℝ) ≤ stT172 38 := by
  have hc : ((-493593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160142793699/1000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-493593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c39 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((41967/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 929227/2500000) (δ := 8719/1000000000) (ψ := 32731/100000) 172 100
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t39 : ((33580463851/2500000000000 : ℚ) : ℝ) ≤ stT172 39 := by
  have hc : ((20971/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33580463851/2500000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((20971/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c40 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((113/125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -552201/5000000) (δ := 1097/125000000) (ψ := 32731/100000) 172 101
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t40 : ((14292696951/100000000000 : ℚ) : ℝ) ≤ stT172 40 := by
  have hc : ((18079/20000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14292696951/100000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((18079/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c41 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-787673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6194547/10000000) (δ := 8669/1000000000) (ψ := 32731/100000) 172 102
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t41 : ((-615108471287/5000000000000 : ℚ) : ℝ) ≤ stT172 41 := by
  have hc : ((-787723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-615108471287/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-787723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c42 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-12003/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4167421/10000000) (δ := 8669/1000000000) (ψ := 32731/100000) 172 102
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t42 : ((-37061362129/2500000000000 : ℚ) : ℝ) ≤ stT172 42 := by
  have hc : ((-48037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37061362129/2500000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-48037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c43 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((105307/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1422427/10000000) (δ := 8641/1000000000) (ψ := 32731/100000) 172 103
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t43 : ((128465651391/1000000000000 : ℚ) : ℝ) ≤ stT172 43 := by
  have hc : ((421203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128465651391/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((421203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c44 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-970469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1448981/2000000) (δ := 2187/250000000) (ψ := 32731/100000) 172 104
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t44 : ((-1463112712083/10000000000000 : ℚ) : ℝ) ≤ stT172 44 := by
  have hc : ((-970519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1463112712083/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-970519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c45 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((141869/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2418399/10000000) (δ := 2187/250000000) (ψ := 32731/100000) 172 104
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t45 : ((422934089943/5000000000000 : ℚ) : ℝ) ≤ stT172 45 := by
  have hc : ((283713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((422934089943/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((283713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c46 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((17667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1919319/5000000) (δ := 2187/250000000) (ψ := 32731/100000) 172 105
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t46 : ((13005849999/2500000000000 : ℚ) : ℝ) ≤ stT172 46 := by
  have hc : ((8821/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13005849999/2500000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((8821/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c47 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-69839/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5409071/10000000) (δ := 2187/250000000) (ψ := 32731/100000) 172 105
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t47 : ((-8150381913/100000000000 : ℚ) : ℝ) ≤ stT172 47 := by
  have hc : ((-279381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8150381913/100000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-279381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c48 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((439181/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -124593/1000000) (δ := 27/3125000) (ψ := 32731/100000) 172 106
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t48 : ((1267733583/10000000000 : ℚ) : ℝ) ≤ stT172 48 := by
  have hc : ((109789/125000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1267733583/10000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((109789/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c49 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-248909/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3810163/5000000) (δ := 27/3125000) (ψ := 32731/100000) 172 106
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t49 : ((-177801142549/1250000000000 : ℚ) : ℝ) ≤ stT172 49 := by
  have hc : ((-497843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177801142549/1250000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-497843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c50 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((971379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 599567/10000000) (δ := 867/100000000) (ψ := 32731/100000) 172 107
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t50 : ((1373666099077/10000000000000 : ℚ) : ℝ) ≤ stT172 50 := by
  have hc : ((971329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1373666099077/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((971329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c51 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-437761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3296639/5000000) (δ := 8777/1000000000) (ψ := 32731/100000) 172 108
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t51 : ((-306511708933/2500000000000 : ℚ) : ℝ) ≤ stT172 51 := by
  have hc : ((-218893/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-306511708933/2500000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-218893/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c52 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((763163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 351301/2000000) (δ := 8777/1000000000) (ψ := 32731/100000) 172 108
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t52 : ((4232987811/40000000000 : ℚ) : ℝ) ≤ stT172 52 := by
  have hc : ((763113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4232987811/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((763113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c53 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-669471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5760733/10000000) (δ := 8719/1000000000) (ψ := 32731/100000) 172 109
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t53 : ((-459829031363/5000000000000 : ℚ) : ℝ) ≤ stT172 53 := by
  have hc : ((-669521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-459829031363/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-669521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c54 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((122631/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 227687/1000000) (δ := 8719/1000000000) (ψ := 32731/100000) 172 109
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t54 : ((166865967567/2000000000000 : ℚ) : ℝ) ≤ stT172 54 := by
  have hc : ((122621/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166865967567/2000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((122621/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c55 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-300837/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -277049/500000) (δ := 2153/250000000) (ψ := 32731/100000) 172 110
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t55 : ((-507102901/6250000000 : ℚ) : ℝ) ≤ stT172 55 := by
  have hc : ((-150431/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-507102901/6250000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-150431/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c56 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((317499/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 88279/400000) (δ := 2153/250000000) (ψ := 32731/100000) 172 110
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t56 : ((106060602761/1250000000000 : ℚ) : ℝ) ≤ stT172 56 := by
  have hc : ((158737/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106060602761/1250000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((158737/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c57 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-141403/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -73627/125000) (δ := 4349/500000000) (ψ := 32731/100000) 172 111
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t57 : ((-187306185129/2000000000000 : ℚ) : ℝ) ≤ stT172 57 := by
  have hc : ((-141413/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187306185129/2000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-141413/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c58 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((804879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 794157/5000000) (δ := 4349/500000000) (ψ := 32731/100000) 172 111
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t58 : ((132098998257/1250000000000 : ℚ) : ℝ) ≤ stT172 58 := by
  have hc : ((804829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132098998257/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((804829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c59 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-113413/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3384529/5000000) (δ := 8797/1000000000) (ψ := 32731/100000) 172 112
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t59 : ((-59063754953/500000000000 : ℚ) : ℝ) ≤ stT172 59 := by
  have hc : ((-453677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59063754953/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-453677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c60 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((491633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 91599/2000000) (δ := 8797/1000000000) (ψ := 32731/100000) 172 112
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t60 : ((39666436147/312500000000 : ℚ) : ℝ) ≤ stT172 60 := by
  have hc : ((61451/62500 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39666436147/312500000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((61451/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c61 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-496677/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3782797/5000000) (δ := 8797/1000000000) (ψ := 32731/100000) 172 112
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t61 : ((-317980921519/2500000000000 : ℚ) : ℝ) ≤ stT172 61 := by
  have hc : ((-248351/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-317980921519/2500000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-248351/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c62 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((89599/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -575177/5000000) (δ := 869/100000000) (ψ := 32731/100000) 172 113
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t62 : ((56892234797/500000000000 : ℚ) : ℝ) ≤ stT172 62 := by
  have hc : ((44797/50000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56892234797/500000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((44797/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c63 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-330117/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2864909/5000000) (δ := 869/100000000) (ψ := 32731/100000) 172 113
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t63 : ((-103984990811/1250000000000 : ℚ) : ℝ) ≤ stT172 63 := by
  have hc : ((-165071/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103984990811/1250000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-165071/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c64 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((284271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -400797/1250000) (δ := 431/50000000) (ψ := 32731/100000) 172 114
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t64 : ((284221/8000000 : ℚ) : ℝ) ≤ stT172 64 := by
  have hc : ((284221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((284221/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((284221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c65 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((185543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 346043/1000000) (δ := 431/50000000) (ψ := 32731/100000) 172 114
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t65 : ((230075686071/10000000000000 : ℚ) : ℝ) ≤ stT172 65 := by
  have hc : ((185493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230075686071/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((185493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c66 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-40369/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1420627/2500000) (δ := 8727/1000000000) (ψ := 32731/100000) 172 115
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t66 : ((-79511446791/1000000000000 : ℚ) : ℝ) ≤ stT172 66 := by
  have hc : ((-322977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79511446791/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-322977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c67 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((190251/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 783789/10000000) (δ := 8727/1000000000) (ψ := 32731/100000) 172 115
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t67 : ((116208144127/1000000000000 : ℚ) : ℝ) ≤ stT172 67 := by
  have hc : ((190241/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116208144127/1000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((190241/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c68 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-961089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3577141/5000000) (δ := 8727/1000000000) (ψ := 32731/100000) 172 115
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t68 : ((-1165553081381/10000000000000 : ℚ) : ℝ) ≤ stT172 68 := by
  have hc : ((-961139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1165553081381/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-961139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c69 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((613367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1138099/5000000) (δ := 8769/1000000000) (ψ := 32731/100000) 172 116
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t69 : ((369173288493/5000000000000 : ℚ) : ℝ) ≤ stT172 69 := by
  have hc : ((613317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((369173288493/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((613317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c70 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((6419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3910943/10000000) (δ := 8769/1000000000) (ψ := 32731/100000) 172 116
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t70 : ((1903101783/2500000000000 : ℚ) : ℝ) ≤ stT172 70 := by
  have hc : ((6369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1903101783/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((6369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c71 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-325257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2848821/5000000) (δ := 8661/1000000000) (ψ := 32731/100000) 172 117
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t71 : ((-96509705631/1250000000000 : ℚ) : ℝ) ≤ stT172 71 := by
  have hc : ((-162641/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96509705631/1250000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-162641/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c72 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((991999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 316467/10000000) (δ := 8661/1000000000) (ψ := 32731/100000) 172 117
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t72 : ((1169022807939/10000000000000 : ℚ) : ℝ) ≤ stT172 72 := by
  have hc : ((991949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1169022807939/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((991949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c73 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-160113/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3123793/5000000) (δ := 8661/1000000000) (ψ := 32731/100000) 172 117
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t73 : ((-46852470169/500000000000 : ℚ) : ℝ) ≤ stT172 73 := by
  have hc : ((-160123/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46852470169/500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-160123/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c74 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((126469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3609969/10000000) (δ := 8649/1000000000) (ψ := 32731/100000) 172 118
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t74 : ((36739763361/2500000000000 : ℚ) : ℝ) ≤ stT172 74 := by
  have hc : ((126419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36739763361/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((126419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c75 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((648803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 540491/2500000) (δ := 8649/1000000000) (ψ := 32731/100000) 172 118
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t75 : ((7491150891/100000000000 : ℚ) : ℝ) ≤ stT172 75 := by
  have hc : ((648753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7491150891/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((648753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c76 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-999999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7850563/10000000) (δ := 2189/250000000) (ψ := 32731/100000) 172 119
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t76 : ((-1147135206871/10000000000000 : ℚ) : ℝ) ≤ stT172 76 := by
  have hc : ((-1000049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1147135206871/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-1000049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c77 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((313997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55739/250000) (δ := 2189/250000000) (ψ := 32731/100000) 172 119
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t77 : ((17890203053/250000000000 : ℚ) : ℝ) ≤ stT172 77 := by
  have hc : ((78493/125000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17890203053/250000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((78493/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c78 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((60211/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1659451/5000000) (δ := 2189/250000000) (ψ := 32731/100000) 172 119
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t78 : ((136322753969/5000000000000 : ℚ) : ℝ) ≤ stT172 78 := by
  have hc : ((120397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136322753969/5000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((120397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c79 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-185949/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1727823/2500000) (δ := 437/50000000) (ψ := 32731/100000) 172 120
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t79 : ((-6538132481/62500000000 : ℚ) : ℝ) ≤ stT172 79 := by
  have hc : ((-185959/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6538132481/62500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-185959/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c80 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((824791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -187801/1250000) (δ := 437/50000000) (ψ := 32731/100000) 172 120
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t80 : ((922087654453/10000000000000 : ℚ) : ℝ) ≤ stT172 80 := by
  have hc : ((824741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((922087654453/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((824741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c81 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((17541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3839267/10000000) (δ := 437/50000000) (ψ := 32731/100000) 172 120
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t81 : ((4865555069/1250000000000 : ℚ) : ℝ) ≤ stT172 81 := by
  have hc : ((4379/125000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4865555069/1250000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((4379/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c82 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-437691/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6592553/10000000) (δ := 8633/1000000000) (ψ := 32731/100000) 172 121
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t82 : ((-30211048891/312500000000 : ℚ) : ℝ) ≤ stT172 82 := by
  have hc : ((-109429/125000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30211048891/312500000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-109429/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c83 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((212851/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1380351/10000000) (δ := 8633/1000000000) (ψ := 32731/100000) 172 121
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t83 : ((233620476817/2500000000000 : ℚ) : ℝ) ≤ stT172 83 := by
  have hc : ((425677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233620476817/2500000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((425677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c84 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((62997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1884697/5000000) (δ := 1737/100000000) (ψ := 32731/100000) 172 121
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t84 : ((68680779283/10000000000000 : ℚ) : ℝ) ≤ stT172 84 := by
  have hc : ((62947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68680779283/10000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((62947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c85 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-920401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1712439/2500000) (δ := 8677/1000000000) (ψ := 32731/100000) 172 122
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t85 : ((-998369938503/10000000000000 : ℚ) : ℝ) ≤ stT172 85 := by
  have hc : ((-920451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-998369938503/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-920451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c86 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((37319/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -455119/2500000) (δ := 8677/1000000000) (ψ := 32731/100000) 172 122
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t86 : ((80478778991/1000000000000 : ℚ) : ℝ) ≤ stT172 86 := by
  have hc : ((74633/100000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80478778991/1000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((74633/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c87 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((152773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3150711/10000000) (δ := 8677/1000000000) (ψ := 32731/100000) 172 122
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t87 : ((2558796309/78125000000 : ℚ) : ℝ) ≤ stT172 87 := by
  have hc : ((38187/125000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2558796309/78125000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((38187/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c88 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-498219/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7642911/10000000) (δ := 1757/200000000) (ψ := 32731/100000) 172 123
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t88 : ((-33195631061/312500000000 : ℚ) : ℝ) ≤ stT172 88 := by
  have hc : ((-124561/125000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33195631061/312500000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-124561/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c89 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((441389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1392063/5000000) (δ := 1757/200000000) (ψ := 32731/100000) 172 123
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t89 : ((467818015983/10000000000000 : ℚ) : ℝ) ≤ stT172 89 := by
  have hc : ((441339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((467818015983/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((441339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c90 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((43177/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2020393/10000000) (δ := 1757/200000000) (ψ := 32731/100000) 172 123
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t90 : ((91018472493/1250000000000 : ℚ) : ℝ) ≤ stT172 90 := by
  have hc : ((345391/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91018472493/1250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((345391/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c91 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-907769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1692957/2500000) (δ := 8609/500000000) (ψ := 32731/100000) 172 123
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t91 : ((-190330608083/2000000000000 : ℚ) : ℝ) ≤ stT172 91 := by
  have hc : ((-907819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190330608083/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-907819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c92 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-24709/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1059161/2500000) (δ := 8711/1000000000) (ψ := 32731/100000) 172 124
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t92 : ((-25771361987/2000000000000 : ℚ) : ℝ) ≤ stT172 92 := by
  have hc : ((-24719/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25771361987/2000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-24719/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c93 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((61653/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 412043/10000000) (δ := 8711/1000000000) (ψ := 32731/100000) 172 124
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t93 : ((511423196249/5000000000000 : ℚ) : ℝ) ≤ stT172 93 := by
  have hc : ((493199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((511423196249/5000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((493199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c94 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-52519/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2505511/5000000) (δ := 8711/1000000000) (ψ := 32731/100000) 172 124
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t94 : ((-108351396811/2500000000000 : ℚ) : ℝ) ≤ stT172 94 := by
  have hc : ((-210101/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108351396811/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-210101/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c95 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-387861/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3073319/5000000) (δ := 2151/250000000) (ψ := 32731/100000) 172 125
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t95 : ((-198981445197/2500000000000 : ℚ) : ℝ) ≤ stT172 95 := by
  have hc : ((-193943/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198981445197/2500000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-193943/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c96 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((791467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1643979/10000000) (δ := 2151/250000000) (ψ := 32731/100000) 172 125
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t96 : ((40386800927/500000000000 : ℚ) : ℝ) ≤ stT172 96 := by
  have hc : ((791417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40386800927/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((791417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c97 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((107837/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 112481/400000) (δ := 2151/250000000) (ψ := 32731/100000) 172 125
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t97 : ((109479174777/2500000000000 : ℚ) : ℝ) ≤ stT172 97 := by
  have hc : ((215649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109479174777/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((215649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c98 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-3873/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 90279/125000) (δ := 2151/250000000) (ψ := 32731/100000) 172 125
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t98 : ((-9781311499/100000000000 : ℚ) : ℝ) ≤ stT172 98 := by
  have hc : ((-9683/10000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9781311499/100000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-9683/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c99 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-77171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4120111/10000000) (δ := 4353/500000000) (ψ := 32731/100000) 172 126
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t99 : ((-38805019699/5000000000000 : ℚ) : ℝ) ≤ stT172 99 := by
  have hc : ((-77221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38805019699/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-77221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c100 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((996753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 100759/5000000) (δ := 4353/500000000) (ψ := 32731/100000) 172 126
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t100 : ((996702003297/10000000000000 : ℚ) : ℝ) ≤ stT172 100 := by
  have hc : ((996703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((996702003297/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((996703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c101 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-109739/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 448019/1000000) (δ := 4353/500000000) (ψ := 32731/100000) 172 126
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t101 : ((-13652418879/625000000000 : ℚ) : ℝ) ≤ stT172 101 := by
  have hc : ((-27441/125000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13652418879/625000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-27441/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c102 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-941049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1398257/2000000) (δ := 879/100000000) (ψ := 32731/100000) 172 127
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t102 : ((-232956823163/2500000000000 : ℚ) : ℝ) ≤ stT172 102 := by
  have hc : ((-941099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232956823163/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-941099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c103 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((54633/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1398081/5000000) (δ := 879/100000000) (ψ := 32731/100000) 172 127
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t103 : ((215301283803/5000000000000 : ℚ) : ℝ) ≤ stT172 103 := by
  have hc : ((218507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215301283803/5000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((218507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c104 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((171193/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 271691/2000000) (δ := 879/100000000) (ψ := 32731/100000) 172 127
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t104 : ((8392931307/100000000000 : ℚ) : ℝ) ≤ stT172 104 := by
  have hc : ((171183/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8392931307/100000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((171183/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c105 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-289923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 273667/500000) (δ := 879/100000000) (ψ := 32731/100000) 172 127
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t105 : ((-70740135787/1250000000000 : ℚ) : ℝ) ≤ stT172 105 := by
  have hc : ((-72487/125000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70740135787/1250000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-72487/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c106 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-778779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3079391/5000000) (δ := 8683/1000000000) (ψ := 32731/100000) 172 128
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t106 : ((-378232852047/5000000000000 : ℚ) : ℝ) ≤ stT172 106 := by
  have hc : ((-778829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-378232852047/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-778829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c107 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((330567/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -132573/625000) (δ := 8683/1000000000) (ψ := 32731/100000) 172 128
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t107 : ((9985839091/156250000000 : ℚ) : ℝ) ≤ stT172 107 := by
  have hc : ((165271/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9985839091/156250000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((165271/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c108 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((365317/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 117429/625000) (δ := 8683/1000000000) (ψ := 32731/100000) 172 128
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t108 : ((351502227/5000000000 : ℚ) : ℝ) ≤ stT172 108 := by
  have hc : ((91323/125000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((351502227/5000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((91323/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c109 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-693261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2921001/5000000) (δ := 8683/1000000000) (ψ := 32731/100000) 172 128
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t109 : ((-664071995197/10000000000000 : ℚ) : ℝ) ≤ stT172 109 := by
  have hc : ((-693311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-664071995197/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-693311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c110 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-720691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2969493/5000000) (δ := 2157/250000000) (ψ := 32731/100000) 172 129
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t110 : ((-687199876083/10000000000000 : ℚ) : ℝ) ≤ stT172 110 := by
  have hc : ((-720741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-687199876083/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-720741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c111 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((10671/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2047529/10000000) (δ := 2157/250000000) (ψ := 32731/100000) 172 129
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t111 : ((324086810179/5000000000000 : ℚ) : ℝ) ≤ stT172 111 := by
  have hc : ((341447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((324086810179/5000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((341447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c112 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((149887/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1808969/10000000) (δ := 2157/250000000) (ψ := 32731/100000) 172 129
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t112 : ((141620425947/2000000000000 : ℚ) : ℝ) ≤ stT172 112 := by
  have hc : ((149877/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141620425947/2000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((149877/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c113 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-630113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5631239/10000000) (δ := 2157/250000000) (ψ := 32731/100000) 172 129
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t113 : ((-592807567523/10000000000000 : ℚ) : ℝ) ≤ stT172 113 := by
  have hc : ((-630163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-592807567523/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-630163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c114 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-405093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3144083/5000000) (δ := 1747/200000000) (ψ := 32731/100000) 172 130
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t114 : ((-94856961787/1250000000000 : ℚ) : ℝ) ≤ stT172 114 := by
  have hc : ((-202559/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94856961787/1250000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-202559/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c115 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((264629/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -101307/400000) (δ := 1747/200000000) (ψ := 32731/100000) 172 130
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t115 : ((7710759013/156250000000 : ℚ) : ℝ) ≤ stT172 115 := by
  have hc : ((66151/125000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7710759013/156250000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((66151/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c116 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((444393/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 238053/2000000) (δ := 1747/200000000) (ψ := 32731/100000) 172 130
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t116 : ((6446640987/78125000000 : ℚ) : ℝ) ≤ stT172 116 := by
  have hc : ((27773/31250 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6446640987/78125000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((27773/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c117 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-9313/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4881299/10000000) (δ := 1747/200000000) (ψ := 32731/100000) 172 130
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t117 : ((-34444133757/1000000000000 : ℚ) : ℝ) ≤ stT172 117 := by
  have hc : ((-37257/100000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34444133757/1000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-37257/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c118 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-120311/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -895883/1250000) (δ := 8761/1000000000) (ψ := 32731/100000) 172 131
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t118 : ((-17721768387/200000000000 : ℚ) : ℝ) ≤ stT172 118 := by
  have hc : ((-481269/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17721768387/200000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-481269/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c119 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((154819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -176919/500000) (δ := 8761/1000000000) (ψ := 32731/100000) 172 131
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t119 : ((70938216381/5000000000000 : ℚ) : ℝ) ≤ stT172 119 := by
  have hc : ((154769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70938216381/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((154769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c120 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((31241/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 59989/10000000) (δ := 8761/1000000000) (ψ := 32731/100000) 172 131
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t120 : ((45628072497/500000000000 : ℚ) : ℝ) ≤ stT172 120 := by
  have hc : ((499831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45628072497/500000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((499831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c121 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((29781/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3628473/10000000) (δ := 8761/1000000000) (ψ := 32731/100000) 172 131
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t121 : ((5412449133/500000000000 : ℚ) : ℝ) ≤ stT172 121 := by
  have hc : ((59537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5412449133/500000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((59537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c122 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-192509/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1791897/2500000) (δ := 8761/1000000000) (ψ := 32731/100000) 172 131
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t122 : ((-87149308401/1000000000000 : ℚ) : ℝ) ≤ stT172 122 := by
  have hc : ((-192519/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87149308401/1000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-192519/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c123 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-85417/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1257539/2500000) (δ := 4327/500000000) (ψ := 32731/100000) 172 132
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t123 : ((-7702696309/200000000000 : ℚ) : ℝ) ≤ stT172 123 := by
  have hc : ((-85427/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7702696309/200000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-85427/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c124 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((814259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -38709/250000) (δ := 4327/500000000) (ψ := 32731/100000) 172 132
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t124 : ((365590425717/5000000000000 : ℚ) : ℝ) ≤ stT172 124 := by
  have hc : ((814209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((365590425717/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((814209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c125 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((361661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 952743/5000000) (δ := 4327/500000000) (ψ := 32731/100000) 172 132
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t125 : ((80864250643/1250000000000 : ℚ) : ℝ) ≤ stT172 125 := by
  have hc : ((90409/125000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80864250643/1250000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((90409/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c126 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-532819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1332953/2500000) (δ := 4327/500000000) (ψ := 32731/100000) 172 132
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t126 : ((-474717538899/10000000000000 : ℚ) : ℝ) ≤ stT172 126 := by
  have hc : ((-532869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-474717538899/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-532869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c127 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-187819/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3488479/5000000) (δ := 541/62500000) (ψ := 32731/100000) 172 133
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t127 : ((-166671377953/2000000000000 : ℚ) : ℝ) ≤ stT172 127 := by
  have hc : ((-187829/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166671377953/2000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-187829/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c128 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((64343/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1802191/5000000) (δ := 541/62500000) (ψ := 32731/100000) 172 133
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t128 : ((28424793397/2500000000000 : ℚ) : ℝ) ≤ stT172 128 := by
  have hc : ((32159/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28424793397/2500000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((32159/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c129 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((497339/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -64509/2500000) (δ := 541/62500000) (ψ := 32731/100000) 172 133
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t129 : ((4378601113/50000000000 : ℚ) : ℝ) ≤ stT172 129 := by
  have hc : ((248657/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4378601113/50000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((248657/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c130 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((13559/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 382803/1250000) (δ := 541/62500000) (ψ := 32731/100000) 172 133
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t130 : ((5945137653/200000000000 : ℚ) : ℝ) ≤ stT172 130 := by
  have hc : ((13557/40000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5945137653/200000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((13557/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c131 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-826123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6357471/10000000) (δ := 541/62500000) (ψ := 32731/100000) 172 133
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t131 : ((-144366296193/2000000000000 : ℚ) : ℝ) ≤ stT172 131 := by
  have hc : ((-826173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144366296193/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-826173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c132 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-758761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3040257/5000000) (δ := 2191/250000000) (ψ := 32731/100000) 172 134
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t132 : ((-660460747479/10000000000000 : ℚ) : ℝ) ≤ stT172 132 := by
  have hc : ((-758811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-660460747479/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-758811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c133 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((5287/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1417609/5000000) (δ := 2191/250000000) (ψ := 32731/100000) 172 134
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t133 : ((36670906719/1000000000000 : ℚ) : ℝ) ≤ stT172 133 := by
  have hc : ((42291/100000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36670906719/1000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((42291/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c134 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((988119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 385761/10000000) (δ := 17239/1000000000) (ψ := 32731/100000) 172 134
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t134 : ((213390297723/2500000000000 : ℚ) : ℝ) ≤ stT172 134 := by
  have hc : ((988069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213390297723/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((988069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c135 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((68623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 358279/1000000) (δ := 2191/250000000) (ψ := 32731/100000) 172 134
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t135 : ((14759922969/1250000000000 : ℚ) : ℝ) ≤ stT172 135 := by
  have hc : ((34299/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14759922969/1250000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((34299/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c136 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-181027/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6756233/10000000) (δ := 2191/250000000) (ψ := 32731/100000) 172 134
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t136 : ((-155237960241/2000000000000 : ℚ) : ℝ) ≤ stT172 136 := by
  have hc : ((-181037/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155237960241/2000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-181037/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c137 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-681497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1450377/2500000) (δ := 2183/250000000) (ψ := 32731/100000) 172 135
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t137 : ((-291142565913/5000000000000 : ℚ) : ℝ) ≤ stT172 137 := by
  have hc : ((-681547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291142565913/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-681547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c138 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((120097/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2674247/10000000) (δ := 2183/250000000) (ψ := 32731/100000) 172 135
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t138 : ((25555662783/625000000000 : ℚ) : ℝ) ≤ stT172 138 := by
  have hc : ((240169/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25555662783/625000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((240169/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c139 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((985211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 215241/5000000) (δ := 2183/250000000) (ψ := 32731/100000) 172 135
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t139 : ((208900434567/2500000000000 : ℚ) : ℝ) ≤ stT172 139 := by
  have hc : ((985161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208900434567/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((985161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c140 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((32973/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3512937/10000000) (δ := 2183/250000000) (ψ := 32731/100000) 172 135
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t140 : ((13929405651/1000000000000 : ℚ) : ℝ) ≤ stT172 140 := by
  have hc : ((32963/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13929405651/1000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((32963/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c141 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-108957/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6573419/10000000) (δ := 2183/250000000) (ψ := 32731/100000) 172 135
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t141 : ((-45881809457/625000000000 : ℚ) : ℝ) ≤ stT172 141 := by
  have hc : ((-435853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45881809457/625000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-435853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c142 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-76269/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -190489/312500) (δ := 69/8000000) (ψ := 32731/100000) 172 136
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t142 : ((-16001941967/250000000000 : ℚ) : ℝ) ≤ stT172 142 := by
  have hc : ((-38137/50000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16001941967/250000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-38137/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c143 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((83269/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9619/31250) (δ := 69/8000000) (ψ := 32731/100000) 172 136
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t143 : ((69622582073/2500000000000 : ℚ) : ℝ) ≤ stT172 143 := by
  have hc : ((166513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69622582073/2500000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((166513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c144 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((249867/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40791/5000000) (δ := 69/8000000) (ψ := 32731/100000) 172 136
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t144 : ((416424000097/5000000000000 : ℚ) : ℝ) ≤ stT172 144 := by
  have hc : ((499709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((416424000097/5000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((499709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c145 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((401453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2894233/10000000) (δ := 69/8000000) (ψ := 32731/100000) 172 136
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t145 : ((166673363481/5000000000000 : ℚ) : ℝ) ≤ stT172 145 := by
  have hc : ((401403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166673363481/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((401403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c146 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-695443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 292479/500000) (δ := 69/8000000) (ψ := 32731/100000) 172 136
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t146 : ((-287797089879/5000000000000 : ℚ) : ℝ) ≤ stT172 146 := by
  have hc : ((-695493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-287797089879/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-695493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c147 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-186299/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3461623/5000000) (δ := 1737/200000000) (ψ := 32731/100000) 172 137
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t147 : ((-153665241183/2000000000000 : ℚ) : ℝ) ≤ stT172 147 := by
  have hc : ((-186309/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153665241183/2000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-186309/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c148 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-8097/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -160319/400000) (δ := 1737/200000000) (ψ := 32731/100000) 172 137
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t148 : ((-2666387381/1000000000000 : ℚ) : ℝ) ≤ stT172 148 := by
  have hc : ((-16219/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2666387381/1000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-16219/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c149 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((902643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -139039/1250000) (δ := 1737/200000000) (ψ := 32731/100000) 172 137
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t149 : ((739432165983/10000000000000 : ℚ) : ℝ) ≤ stT172 149 := by
  have hc : ((902593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((739432165983/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((902593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c150 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((152249/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 352783/2000000) (δ := 1737/200000000) (ψ := 32731/100000) 172 137
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t150 : ((7768908409/125000000000 : ℚ) : ℝ) ≤ stT172 150 := by
  have hc : ((152239/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7768908409/125000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((152239/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c151 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-34261/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4621093/10000000) (δ := 1737/200000000) (ψ := 32731/100000) 172 137
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t151 : ((-111545244441/5000000000000 : ℚ) : ℝ) ≤ stT172 151 := by
  have hc : ((-137069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111545244441/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-137069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c152 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-98757/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3729697/5000000) (δ := 1737/200000000) (ψ := 32731/100000) 172 137
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t152 : ((-10013331037/125000000000 : ℚ) : ℝ) ≤ stT172 152 := by
  have hc : ((-49381/50000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10013331037/125000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-49381/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c153 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-141317/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5428887/10000000) (δ := 1099/125000000) (ψ := 32731/100000) 172 138
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t153 : ((-228516516527/5000000000000 : ℚ) : ℝ) ≤ stT172 153 := by
  have hc : ((-282659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228516516527/5000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-282659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c154 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((12417/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1313783/5000000) (δ := 1099/125000000) (ψ := 32731/100000) 172 138
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t154 : ((20009768993/500000000000 : ℚ) : ℝ) ≤ stT172 154 := by
  have hc : ((49663/100000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20009768993/500000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((49663/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c155 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((998063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 155609/10000000) (δ := 1099/125000000) (ψ := 32731/100000) 172 138
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t155 : ((801623003847/10000000000000 : ℚ) : ℝ) ≤ stT172 155 := by
  have hc : ((998013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((801623003847/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((998013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c156 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((391663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45639/156250) (δ := 1099/125000000) (ψ := 32731/100000) 172 138
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t156 : ((489907863/15625000000 : ℚ) : ℝ) ≤ stT172 156 := by
  have hc : ((391613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((489907863/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((391613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c157 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-641619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 566851/1000000) (δ := 1099/125000000) (ψ := 32731/100000) 172 138
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t157 : ((-512107687203/10000000000000 : ℚ) : ℝ) ≤ stT172 157 := by
  have hc : ((-641669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512107687203/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-641669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c158 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-976359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3654649/5000000) (δ := 17/1953125) (ψ := 32731/100000) 172 139
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t158 : ((-388394995611/5000000000000 : ℚ) : ℝ) ≤ stT172 158 := by
  have hc : ((-976409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-388394995611/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-976409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c159 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-264553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2298171/5000000) (δ := 17/1953125) (ψ := 32731/100000) 172 139
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t159 : ((-52460984589/2500000000000 : ℚ) : ℝ) ≤ stT172 159 := by
  have hc : ((-264603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52460984589/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-264603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c160 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((362361/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -950207/5000000) (δ := 17/1953125) (ψ := 32731/100000) 172 139
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t160 : ((8951612787/156250000000 : ℚ) : ℝ) ≤ stT172 160 := by
  have hc : ((11323/15625 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8951612787/156250000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((11323/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c161 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((951881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 778701/10000000) (δ := 17/1953125) (ψ := 32731/100000) 172 139
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t161 : ((75014752941/1000000000000 : ℚ) : ℝ) ≤ stT172 161 := by
  have hc : ((951831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75014752941/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((951831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c162 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((12067/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3441261/10000000) (δ := 17/1953125) (ψ := 32731/100000) 172 139
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t162 : ((37913091707/2500000000000 : ℚ) : ℝ) ≤ stT172 162 := by
  have hc : ((96511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37913091707/2500000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((96511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c163 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-380281/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3043719/5000000) (δ := 17/1953125) (ψ := 32731/100000) 172 139
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t163 : ((-148939428933/2500000000000 : ℚ) : ℝ) ≤ stT172 163 := by
  have hc : ((-190153/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148939428933/2500000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-190153/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c164 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-940951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6990559/10000000) (δ := 8607/1000000000) (ψ := 32731/100000) 172 140
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t164 : ((-734798509869/10000000000000 : ℚ) : ℝ) ≤ stT172 164 := by
  have hc : ((-941001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-734798509869/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-941001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c165 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-178871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4376589/10000000) (δ := 8607/1000000000) (ψ := 32731/100000) 172 140
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t165 : ((-139289819579/10000000000000 : ℚ) : ℝ) ≤ stT172 165 := by
  have hc : ((-178921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139289819579/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-178921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c166 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((30299/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2223/12500) (δ := 8607/1000000000) (ψ := 32731/100000) 172 140
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t166 : ((470300331/8000000000 : ℚ) : ℝ) ≤ stT172 166 := by
  have hc : ((30297/40000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((470300331/8000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((30297/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c167 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((948703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 804223/10000000) (δ := 8607/1000000000) (ψ := 32731/100000) 172 140
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t167 : ((734089510419/10000000000000 : ℚ) : ℝ) ≤ stT172 167 := by
  have hc : ((948653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((734089510419/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((948653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c168 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((8817/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1685683/5000000) (δ := 8607/1000000000) (ψ := 32731/100000) 172 140
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t168 : ((340045677/20000000000 : ℚ) : ℝ) ≤ stT172 168 := by
  have hc : ((1763/8000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((340045677/20000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((1763/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c169 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-143267/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 592333/1000000) (δ := 8607/1000000000) (ψ := 32731/100000) 172 140
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t169 : ((-110213109987/2000000000000 : ℚ) : ℝ) ≤ stT172 169 := by
  have hc : ((-143277/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110213109987/2000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-143277/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c170 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-121343/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3623881/5000000) (δ := 4357/500000000) (ψ := 32731/100000) 172 141
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t170 : ((-74456502021/1000000000000 : ℚ) : ℝ) ≤ stT172 170 := by
  have hc : ((-485397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74456502021/1000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-485397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c171 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-314103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4725769/10000000) (δ := 4357/500000000) (ψ := 32731/100000) 172 141
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t171 : ((-3002988527/125000000000 : ℚ) : ℝ) ≤ stT172 171 := by
  have hc : ((-314153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3002988527/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-314153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c172 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((157859/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1109241/5000000) (δ := 4357/500000000) (ψ := 32731/100000) 172 141
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t172 : ((60178346739/1250000000000 : ℚ) : ℝ) ≤ stT172 172 := by
  have hc : ((315693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60178346739/1250000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((315693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c173 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((248497/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 274271/10000000) (δ := 4357/500000000) (ψ := 32731/100000) 172 141
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t173 : ((75567615233/1000000000000 : ℚ) : ℝ) ≤ stT172 173 := by
  have hc : ((496969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75567615233/1000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((496969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c174 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((452647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1376331/5000000) (δ := 4357/500000000) (ψ := 32731/100000) 172 141
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t174 : ((171556440253/5000000000000 : ℚ) : ℝ) ≤ stT172 174 := by
  have hc : ((452597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171556440253/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((452597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c175 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-6167/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5216863/10000000) (δ := 4357/500000000) (ψ := 32731/100000) 172 141
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t175 : ((-37298292789/1000000000000 : ℚ) : ℝ) ≤ stT172 175 := by
  have hc : ((-49341/100000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37298292789/1000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-49341/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c176 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-249301/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7667003/10000000) (δ := 4357/500000000) (ψ := 32731/100000) 172 141
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t176 : ((-375854561433/5000000000000 : ℚ) : ℝ) ≤ stT172 176 := by
  have hc : ((-498627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-375854561433/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-498627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c177 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-24873/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5604667/10000000) (δ := 4391/500000000) (ψ := 32731/100000) 172 142
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t177 : ((-149577753/3200000000 : ℚ) : ℝ) ≤ stT172 177 := by
  have hc : ((-199/320 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149577753/3200000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-199/320 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c178 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((58711/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3182133/10000000) (δ := 4391/500000000) (ψ := 32731/100000) 172 142
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t178 : ((43998219231/2000000000000 : ℚ) : ℝ) ≤ stT172 178 := by
  have hc : ((58701/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43998219231/2000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((58701/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c179 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((11907/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -96643/1250000) (δ := 4391/500000000) (ψ := 32731/100000) 172 142
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t179 : ((14238786237/200000000000 : ℚ) : ℝ) ≤ stT172 179 := by
  have hc : ((95251/100000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14238786237/200000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((95251/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c180 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((199179/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 811193/5000000) (δ := 4391/500000000) (ψ := 32731/100000) 172 142
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t180 : ((59379898643/1000000000000 : ℚ) : ℝ) ≤ stT172 180 := by
  have hc : ((398333/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59379898643/1000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((398333/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c181 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-31067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 62573/156250) (δ := 4391/500000000) (ψ := 32731/100000) 172 142
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t181 : ((-4625822103/2000000000000 : ℚ) : ℝ) ≤ stT172 181 := by
  have hc : ((-31117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4625822103/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-31117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c182 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-414893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31869/50000) (δ := 4391/500000000) (ψ := 32731/100000) 172 142
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t182 : ((-123023187/2000000000 : ℚ) : ℝ) ≤ stT172 182 := by
  have hc : ((-207459/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123023187/2000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-207459/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c183 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-187847/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3488989/5000000) (δ := 347/40000000) (ψ := 32731/100000) 172 143
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t183 : ((-69434013627/1000000000000 : ℚ) : ℝ) ≤ stT172 183 := by
  have hc : ((-187857/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69434013627/1000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-187857/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c184 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-279299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -92693/200000) (δ := 347/40000000) (ψ := 32731/100000) 172 143
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t184 : ((-20593887629/1000000000000 : ℚ) : ℝ) ≤ stT172 184 := by
  have hc : ((-279349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20593887629/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-279349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c185 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((9446/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2304007/10000000) (δ := 347/40000000) (ψ := 32731/100000) 172 143
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t185 : ((111108112929/2500000000000 : ℚ) : ℝ) ≤ stT172 185 := by
  have hc : ((302247/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111108112929/2500000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((302247/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c186 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((62499/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14037/10000000) (δ := 347/40000000) (ψ := 32731/100000) 172 143
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t186 : ((73318660649/1000000000000 : ℚ) : ℝ) ≤ stT172 186 := by
  have hc : ((499967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73318660649/1000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((499967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c187 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((599533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2319697/10000000) (δ := 347/40000000) (ψ := 32731/100000) 172 143
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t187 : ((54798141547/1250000000000 : ℚ) : ℝ) ≤ stT172 187 := by
  have hc : ((599483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54798141547/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((599483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c188 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-270979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 576627/1250000) (δ := 347/40000000) (ψ := 32731/100000) 172 143
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t188 : ((-7906729017/400000000000 : ℚ) : ℝ) ≤ stT172 188 := by
  have hc : ((-271029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7906729017/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-271029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c189 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-115901/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6894209/10000000) (δ := 347/40000000) (ψ := 32731/100000) 172 143
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t189 : ((-337240489197/5000000000000 : ℚ) : ℝ) ≤ stT172 189 := by
  have hc : ((-463629/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-337240489197/5000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-463629/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c190 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-865957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1636161/2500000) (δ := 1727/200000000) (ψ := 32731/100000) 172 144
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t190 : ((-628268160339/10000000000000 : ℚ) : ℝ) ≤ stT172 190 := by
  have hc : ((-866007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-628268160339/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-866007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c191 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-71833/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2143701/5000000) (δ := 1727/200000000) (ψ := 32731/100000) 172 144
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t191 : ((-1039893047/100000000000 : ℚ) : ℝ) ≤ stT172 191 := by
  have hc : ((-35929/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1039893047/100000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-35929/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c192 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((342281/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -408397/2000000) (δ := 1727/200000000) (ψ := 32731/100000) 172 144
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t192 : ((15437606617/312500000000 : ℚ) : ℝ) ≤ stT172 192 := by
  have hc : ((21391/31250 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15437606617/312500000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((21391/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c193 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((997059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 191779/10000000) (δ := 1727/200000000) (ψ := 32731/100000) 172 144
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t193 : ((143532406667/2000000000000 : ℚ) : ℝ) ≤ stT172 193 := by
  have hc : ((997009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143532406667/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((997009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c194 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((568917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2414019/10000000) (δ := 1727/200000000) (ψ := 32731/100000) 172 144
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t194 : ((204211306793/5000000000000 : ℚ) : ℝ) ≤ stT172 194 := by
  have hc : ((568867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204211306793/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((568867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c195 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-275521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4624821/10000000) (δ := 1727/200000000) (ψ := 32731/100000) 172 144
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t195 : ((-39468105333/2000000000000 : ℚ) : ℝ) ≤ stT172 195 := by
  have hc : ((-275571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39468105333/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-275571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c196 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-7331/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3412157/5000000) (δ := 1727/200000000) (ψ := 32731/100000) 172 144
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t196 : ((-13091790951/200000000000 : ℚ) : ℝ) ≤ stT172 196 := by
  have hc : ((-36657/40000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13091790951/200000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-36657/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c197 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-55907/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -836917/1250000) (δ := 8743/1000000000) (ψ := 32731/100000) 172 145
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t197 : ((-318674741351/5000000000000 : ℚ) : ℝ) ≤ stT172 197 := by
  have hc : ((-447281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-318674741351/5000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-447281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c198 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-234253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4518117/10000000) (δ := 8743/1000000000) (ψ := 32731/100000) 172 145
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t198 : ((-16651211301/1000000000000 : ℚ) : ℝ) ≤ stT172 198 := by
  have hc : ((-234303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16651211301/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-234303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c199 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((294593/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2351863/10000000) (δ := 8743/1000000000) (ψ := 32731/100000) 172 145
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t199 : ((26101707301/625000000000 : ℚ) : ℝ) ≤ stT172 199 := by
  have hc : ((36821/62500 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26101707301/625000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((36821/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c200 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((996913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24561/1250000) (δ := 8743/1000000000) (ψ := 32731/100000) 172 145
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t200 : ((352443904239/5000000000000 : ℚ) : ℝ) ≤ stT172 200 := by
  have hc : ((996863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352443904239/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((996863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c201 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((28457/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97409/500000) (δ := 8743/1000000000) (ψ := 32731/100000) 172 145
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t201 : ((802823679/16000000000 : ℚ) : ℝ) ≤ stT172 201 := by
  have hc : ((5691/8000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((802823679/16000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((5691/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c202 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-3101/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4082141/10000000) (δ := 8743/1000000000) (ψ := 32731/100000) 172 145
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t202 : ((-2183616393/500000000000 : ℚ) : ℝ) ≤ stT172 202 := by
  have hc : ((-6207/100000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2183616393/500000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-6207/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c203 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-790391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 620561/1000000) (δ := 8743/1000000000) (ψ := 32731/100000) 172 145
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t203 : ((-554781291583/10000000000000 : ℚ) : ℝ) ≤ stT172 203 := by
  have hc : ((-790441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-554781291583/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-790441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c204 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-491389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3694667/5000000) (δ := 8753/1000000000) (ψ := 32731/100000) 172 146
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t204 : ((-172029544687/2500000000000 : ℚ) : ℝ) ≤ stT172 204 := by
  have hc : ((-245707/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172029544687/2500000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-245707/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c205 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-517441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2643317/5000000) (δ := 8753/1000000000) (ψ := 32731/100000) 172 146
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t205 : ((-361431756621/10000000000000 : ℚ) : ℝ) ≤ stT172 205 := by
  have hc : ((-517491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-361431756621/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-517491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c206 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((288949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -399271/1250000) (δ := 8753/1000000000) (ψ := 32731/100000) 172 146
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t206 : ((201285466967/10000000000000 : ℚ) : ℝ) ≤ stT172 206 := by
  have hc : ((288899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201285466967/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((288899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c207 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((902723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -22237/200000) (δ := 8753/1000000000) (ψ := 32731/100000) 172 146
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t207 : ((78425132913/1250000000000 : ℚ) : ℝ) ≤ stT172 207 := by
  have hc : ((902673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78425132913/1250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((902673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c208 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((463553/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 960449/10000000) (δ := 8753/1000000000) (ψ := 32731/100000) 172 146
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t208 : ((321398727/5000000000 : ℚ) : ℝ) ≤ stT172 208 := by
  have hc : ((57941/62500 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((321398727/5000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((57941/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c209 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((353837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 604563/2000000) (δ := 8753/1000000000) (ψ := 32731/100000) 172 146
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t209 : ((122359710459/5000000000000 : ℚ) : ℝ) ≤ stT172 209 := by
  have hc : ((353787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122359710459/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((353787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c210 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-221677/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2537667/5000000) (δ := 8753/1000000000) (ψ := 32731/100000) 172 146
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t210 : ((-38247253083/1250000000000 : ℚ) : ℝ) ≤ stT172 210 := by
  have hc : ((-110851/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38247253083/1250000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-110851/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c211 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-956989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1779523/2500000) (δ := 8753/1000000000) (ψ := 32731/100000) 172 146
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t211 : ((-658853401731/10000000000000 : ℚ) : ℝ) ≤ stT172 211 := by
  have hc : ((-957039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-658853401731/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-957039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c212 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-108547/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1639197/2500000) (δ := 4323/500000000) (ψ := 32731/100000) 172 147
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t212 : ((-298218791039/5000000000000 : ℚ) : ℝ) ≤ stT172 212 := by
  have hc : ((-434213/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-298218791039/5000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-434213/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c213 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-120067/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4533251/10000000) (δ := 4323/500000000) (ψ := 32731/100000) 172 147
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t213 : ((-20571429347/1250000000000 : ℚ) : ℝ) ≤ stT172 213 := by
  have hc : ((-30023/125000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20571429347/1250000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-30023/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c214 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((533833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1259587/5000000) (δ := 4323/500000000) (ψ := 32731/100000) 172 147
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t214 : ((72977210411/2000000000000 : ℚ) : ℝ) ≤ stT172 214 := by
  have hc : ((533783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72977210411/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((533783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c215 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((978897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -257257/5000000) (δ := 4323/500000000) (ψ := 32731/100000) 172 147
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t215 : ((333783890459/5000000000000 : ℚ) : ℝ) ≤ stT172 215 := by
  have hc : ((978847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((333783890459/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((978847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c216 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((165927/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 740429/5000000) (δ := 4323/500000000) (ψ := 32731/100000) 172 147
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t216 : ((112892083721/2000000000000 : ℚ) : ℝ) ≤ stT172 216 := by
  have hc : ((165917/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112892083721/2000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((165917/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c217 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((91483/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 693397/2000000) (δ := 4323/500000000) (ψ := 32731/100000) 172 147
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t217 : ((7760714319/625000000000 : ℚ) : ℝ) ≤ stT172 217 := by
  have hc : ((45729/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7760714319/625000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((45729/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c218 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-570243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1360999/2500000) (δ := 4323/500000000) (ψ := 32731/100000) 172 147
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t218 : ((-193125732399/5000000000000 : ℚ) : ℝ) ≤ stT172 218 := by
  have hc : ((-570293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193125732399/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-570293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c219 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-984411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7411977/10000000) (δ := 4323/500000000) (ψ := 32731/100000) 172 147
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t219 : ((-332618853609/5000000000000 : ℚ) : ℝ) ≤ stT172 219 := by
  have hc : ((-984461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-332618853609/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-984461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c220 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-821479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -198031/312500) (δ := 1083/125000000) (ψ := 32731/100000) 172 148
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t220 : ((-2769374259/50000000000 : ℚ) : ℝ) ≤ stT172 220 := by
  have hc : ((-821529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2769374259/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-821529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c221 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-18291/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -548357/1250000) (δ := 1083/125000000) (ψ := 32731/100000) 172 148
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t221 : ((-1538403151/125000000000 : ℚ) : ℝ) ≤ stT172 221 := by
  have hc : ((-2287/12500 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1538403151/125000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-2287/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c222 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((558491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1222789/5000000) (δ := 1083/125000000) (ψ := 32731/100000) 172 148
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t222 : ((93700256949/2500000000000 : ℚ) : ℝ) ≤ stT172 222 := by
  have hc : ((558441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93700256949/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((558441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c223 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((979021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -256493/5000000) (δ := 1083/125000000) (ψ := 32731/100000) 172 148
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t223 : ((655566951179/10000000000000 : ℚ) : ℝ) ≤ stT172 223 := by
  have hc : ((978971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((655566951179/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((978971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c224 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((422459/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1410963/10000000) (δ := 1083/125000000) (ψ := 32731/100000) 172 148
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t224 : ((141125272201/2500000000000 : ℚ) : ℝ) ≤ stT172 224 := by
  have hc : ((211217/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141125272201/2500000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((211217/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c225 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((4759/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 665271/2000000) (δ := 1083/125000000) (ψ := 32731/100000) 172 148
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t225 : ((792999207/50000000000 : ℚ) : ℝ) ≤ stT172 225 := by
  have hc : ((2379/10000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((792999207/50000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((2379/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c226 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-249519/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5233211/10000000) (δ := 17339/1000000000) (ψ := 32731/100000) 172 148
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t226 : ((-20749302863/625000000000 : ℚ) : ℝ) ≤ stT172 226 := by
  have hc : ((-31193/62500 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20749302863/625000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-31193/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c227 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-119819/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7131683/10000000) (δ := 1083/125000000) (ψ := 32731/100000) 172 148
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t227 : ((-79530894231/1250000000000 : ℚ) : ℝ) ≤ stT172 227 := by
  have hc : ((-479301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79530894231/1250000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-479301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c228 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-892867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1671543/2500000) (δ := 8771/1000000000) (ψ := 32731/100000) 172 149
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t228 : ((-591349462839/10000000000000 : ℚ) : ℝ) ≤ stT172 228 := by
  have hc : ((-892917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-591349462839/10000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-892917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c229 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-343773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -30027/62500) (δ := 8771/1000000000) (ψ := 32731/100000) 172 149
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t229 : ((-227204771037/10000000000000 : ℚ) : ℝ) ≤ stT172 229 := by
  have hc : ((-343823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-227204771037/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-343823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c230 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((194029/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2930681/10000000) (δ := 8771/1000000000) (ψ := 32731/100000) 172 149
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t230 : ((1599029469/62500000000 : ℚ) : ℝ) ≤ stT172 230 := by
  have hc : ((48501/125000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1599029469/62500000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((48501/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c231 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((455299/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1065169/10000000) (δ := 8771/1000000000) (ψ := 32731/100000) 172 149
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t231 : ((149773991787/2500000000000 : ℚ) : ℝ) ≤ stT172 231 := by
  have hc : ((227637/250000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149773991787/2500000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((227637/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c232 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((190041/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 792259/10000000) (δ := 8771/1000000000) (ψ := 32731/100000) 172 149
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t232 : ((31190358123/500000000000 : ℚ) : ℝ) ≤ stT172 232 := by
  have hc : ((190031/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31190358123/500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((190031/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c233 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((245877/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 660433/2500000) (δ := 8771/1000000000) (ψ := 32731/100000) 172 149
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t233 : ((40265702023/1250000000000 : ℚ) : ℝ) ≤ stT172 233 := by
  have hc : ((61463/125000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40265702023/1250000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((61463/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c234 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-220689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4483293/10000000) (δ := 8771/1000000000) (ψ := 32731/100000) 172 149
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t234 : ((-144301719819/10000000000000 : ℚ) : ℝ) ≤ stT172 234 := by
  have hc : ((-220739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144301719819/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-220739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c235 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-81689/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1263397/2000000) (δ := 8771/1000000000) (ψ := 32731/100000) 172 149
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t235 : ((-26645682663/500000000000 : ℚ) : ℝ) ≤ stT172 235 := by
  have hc : ((-40847/50000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26645682663/500000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-40847/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c236 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-99333/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -756507/1000000) (δ := 349/40000000) (ψ := 32731/100000) 172 150
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t236 : ((-6466357441/100000000000 : ℚ) : ℝ) ≤ stT172 236 := by
  have hc : ((-49669/50000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6466357441/100000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-49669/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c237 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-665351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5746901/10000000) (δ := 349/40000000) (ψ := 32731/100000) 172 150
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t237 : ((-43222452757/1000000000000 : ℚ) : ℝ) ≤ stT172 237 := by
  have hc : ((-665401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43222452757/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-665401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c238 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-1879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1968193/5000000) (δ := 349/40000000) (ψ := 32731/100000) 172 150
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t238 : ((-19284069/78125000000 : ℚ) : ℝ) ≤ stT172 238 := by
  have hc : ((-119/31250 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19284069/78125000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-119/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c239 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((657443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2133439/10000000) (δ := 349/40000000) (ψ := 32731/100000) 172 150
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t239 : ((212616016239/5000000000000 : ℚ) : ℝ) ≤ stT172 239 := by
  have hc : ((657393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212616016239/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((657393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c240 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((990873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -338017/10000000) (δ := 349/40000000) (ψ := 32731/100000) 172 150
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t240 : ((639573274031/10000000000000 : ℚ) : ℝ) ≤ stT172 240 := by
  have hc : ((990823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((639573274031/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((990823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c241 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((2614/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1449923/10000000) (δ := 349/40000000) (ψ := 32731/100000) 172 150
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t241 : ((13469785077/250000000000 : ℚ) : ℝ) ≤ stT172 241 := by
  have hc : ((83643/100000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13469785077/250000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((83643/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c242 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((275019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3230467/10000000) (δ := 349/40000000) (ψ := 32731/100000) 172 150
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t242 : ((22094584057/1250000000000 : ℚ) : ℝ) ≤ stT172 242 := by
  have hc : ((274969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22094584057/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((274969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c243 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-417477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2501829/5000000) (δ := 349/40000000) (ψ := 32731/100000) 172 150
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t243 : ((-267843988027/10000000000000 : ℚ) : ℝ) ≤ stT172 243 := by
  have hc : ((-417527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-267843988027/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-417527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c244 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-14178/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3384791/5000000) (δ := 349/40000000) (ψ := 32731/100000) 172 150
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t244 : ((-58093075677/1000000000000 : ℚ) : ℝ) ≤ stT172 244 := by
  have hc : ((-453721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58093075677/1000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-453721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c245 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-120481/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3589851/5000000) (δ := 8693/500000000) (ψ := 32731/100000) 172 151
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t245 : ((-307906131273/5000000000000 : ℚ) : ℝ) ≤ stT172 245 := by
  have hc : ((-481949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-307906131273/5000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-481949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c246 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((-565029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2714081/5000000) (δ := 8617/1000000000) (ψ := 32731/100000) 172 151
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t246 : ((-360281373583/10000000000000 : ℚ) : ℝ) ≤ stT172 246 := by
  have hc : ((-565079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-360281373583/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-565079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c247 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((24287/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1841869/5000000) (δ := 8617/1000000000) (ψ := 32731/100000) 172 151
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t247 : ((7722737979/1250000000000 : ℚ) : ℝ) ≤ stT172 247 := by
  have hc : ((48549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7722737979/1250000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((48549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c248 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((142387/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -973183/5000000) (δ := 8617/1000000000) (ψ := 32731/100000) 172 151
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t248 : ((18081879/400000000 : ℚ) : ℝ) ≤ stT172 248 := by
  have hc : ((142377/200000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18081879/400000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((142377/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c249 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((99627/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -216003/10000000) (δ := 8617/1000000000) (ψ := 32731/100000) 172 151
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t249 : ((7891606541/125000000000 : ℚ) : ℝ) ≤ stT172 249 := by
  have hc : ((49811/50000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7891606541/125000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((49811/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_c250 :
    |Real.cos (((172 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((823643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 37687/250000) (δ := 8617/1000000000) (ψ := 32731/100000) 172 151
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st172_t250 : ((104177102163/2000000000000 : ℚ) : ℝ) ≤ stT172 250 := by
  have hc : ((823593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((172 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((32731/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st172_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104177102163/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((823593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st172_p1 : ((946861/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT172 (i+1) := by
  rw [Finset.sum_range_one]
  exact st172_t1

theorem st172_p2 : ((3143766437461/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT172 (i+1))
      = (∑ i ∈ Finset.range 1, stT172 (i+1)) + stT172 2 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 1
    simpa using h
  have hprev := st172_p1
  have hstep := st172_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p3 : ((21436810418571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT172 (i+1))
      = (∑ i ∈ Finset.range 2, stT172 (i+1)) + stT172 3 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 2
    simpa using h
  have hprev := st172_p2
  have hstep := st172_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p4 : ((25429885418571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT172 (i+1))
      = (∑ i ∈ Finset.range 3, stT172 (i+1)) + stT172 4 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 3
    simpa using h
  have hprev := st172_p3
  have hstep := st172_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p5 : ((3737365153627/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT172 (i+1))
      = (∑ i ∈ Finset.range 4, stT172 (i+1)) + stT172 5 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 4
    simpa using h
  have hprev := st172_p4
  have hstep := st172_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p6 : ((8495079322201/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT172 (i+1))
      = (∑ i ∈ Finset.range 5, stT172 (i+1)) + stT172 6 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 5
    simpa using h
  have hprev := st172_p5
  have hstep := st172_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p7 : ((4346180337757/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT172 (i+1))
      = (∑ i ∈ Finset.range 6, stT172 (i+1)) + stT172 7 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 6
    simpa using h
  have hprev := st172_p6
  have hstep := st172_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p8 : ((37219973657351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT172 (i+1))
      = (∑ i ∈ Finset.range 7, stT172 (i+1)) + stT172 8 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 7
    simpa using h
  have hprev := st172_p7
  have hstep := st172_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p9 : ((39963006716381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT172 (i+1))
      = (∑ i ∈ Finset.range 8, stT172 (i+1)) + stT172 9 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 8
    simpa using h
  have hprev := st172_p8
  have hstep := st172_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p10 : ((5387636932451/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT172 (i+1))
      = (∑ i ∈ Finset.range 9, stT172 (i+1)) + stT172 10 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 9
    simpa using h
  have hprev := st172_p9
  have hstep := st172_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p11 : ((405496396603/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT172 (i+1))
      = (∑ i ∈ Finset.range 10, stT172 (i+1)) + stT172 11 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 10
    simpa using h
  have hprev := st172_p10
  have hstep := st172_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p12 : ((433896252941/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT172 (i+1))
      = (∑ i ∈ Finset.range 11, stT172 (i+1)) + stT172 12 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 11
    simpa using h
  have hprev := st172_p11
  have hstep := st172_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p13 : ((448386625571/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT172 (i+1))
      = (∑ i ∈ Finset.range 12, stT172 (i+1)) + stT172 13 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 12
    simpa using h
  have hprev := st172_p12
  have hstep := st172_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p14 : ((11450987803509/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT172 (i+1))
      = (∑ i ∈ Finset.range 13, stT172 (i+1)) + stT172 14 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 13
    simpa using h
  have hprev := st172_p13
  have hstep := st172_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p15 : ((751058157859/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT172 (i+1))
      = (∑ i ∈ Finset.range 14, stT172 (i+1)) + stT172 15 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 14
    simpa using h
  have hprev := st172_p14
  have hstep := st172_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p16 : ((1546654050093/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT172 (i+1))
      = (∑ i ∈ Finset.range 15, stT172 (i+1)) + stT172 16 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 15
    simpa using h
  have hprev := st172_p15
  have hstep := st172_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p17 : ((2353462547501/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT172 (i+1))
      = (∑ i ∈ Finset.range 16, stT172 (i+1)) + stT172 17 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 16
    simpa using h
  have hprev := st172_p16
  have hstep := st172_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p18 : ((12299153538607/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT172 (i+1))
      = (∑ i ∈ Finset.range 17, stT172 (i+1)) + stT172 18 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 17
    simpa using h
  have hprev := st172_p17
  have hstep := st172_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p19 : ((23509319599011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT172 (i+1))
      = (∑ i ∈ Finset.range 18, stT172 (i+1)) + stT172 19 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 18
    simpa using h
  have hprev := st172_p18
  have hstep := st172_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p20 : ((49165923157787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT172 (i+1))
      = (∑ i ∈ Finset.range 19, stT172 (i+1)) + stT172 20 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 19
    simpa using h
  have hprev := st172_p19
  have hstep := st172_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p21 : ((9722915635201/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT172 (i+1))
      = (∑ i ∈ Finset.range 20, stT172 (i+1)) + stT172 21 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 20
    simpa using h
  have hprev := st172_p20
  have hstep := st172_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p22 : ((46653122287973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT172 (i+1))
      = (∑ i ∈ Finset.range 21, stT172 (i+1)) + stT172 22 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 21
    simpa using h
  have hprev := st172_p21
  have hstep := st172_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p23 : ((47056151431157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT172 (i+1))
      = (∑ i ∈ Finset.range 22, stT172 (i+1)) + stT172 23 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 22
    simpa using h
  have hprev := st172_p22
  have hstep := st172_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p24 : ((24490501455289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT172 (i+1))
      = (∑ i ∈ Finset.range 23, stT172 (i+1)) + stT172 24 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 23
    simpa using h
  have hprev := st172_p23
  have hstep := st172_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p25 : ((25411890455289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT172 (i+1))
      = (∑ i ∈ Finset.range 24, stT172 (i+1)) + stT172 25 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 24
    simpa using h
  have hprev := st172_p24
  have hstep := st172_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p26 : ((52100533983637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT172 (i+1))
      = (∑ i ∈ Finset.range 25, stT172 (i+1)) + stT172 26 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 25
    simpa using h
  have hprev := st172_p25
  have hstep := st172_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p27 : ((53024521074637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT172 (i+1))
      = (∑ i ∈ Finset.range 26, stT172 (i+1)) + stT172 27 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 26
    simpa using h
  have hprev := st172_p26
  have hstep := st172_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p28 : ((53977815325029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT172 (i+1))
      = (∑ i ∈ Finset.range 27, stT172 (i+1)) + stT172 28 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 27
    simpa using h
  have hprev := st172_p27
  have hstep := st172_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p29 : ((11055748920429/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT172 (i+1))
      = (∑ i ∈ Finset.range 28, stT172 (i+1)) + stT172 29 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 28
    simpa using h
  have hprev := st172_p28
  have hstep := st172_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p30 : ((28499205937893/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT172 (i+1))
      = (∑ i ∈ Finset.range 29, stT172 (i+1)) + stT172 30 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 29
    simpa using h
  have hprev := st172_p29
  have hstep := st172_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p31 : ((7339208454441/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT172 (i+1))
      = (∑ i ∈ Finset.range 30, stT172 (i+1)) + stT172 31 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 30
    simpa using h
  have hprev := st172_p30
  have hstep := st172_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p32 : ((1486961494391/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT172 (i+1))
      = (∑ i ∈ Finset.range 31, stT172 (i+1)) + stT172 32 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 31
    simpa using h
  have hprev := st172_p31
  have hstep := st172_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p33 : ((58578894112343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT172 (i+1))
      = (∑ i ∈ Finset.range 32, stT172 (i+1)) + stT172 33 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 32
    simpa using h
  have hprev := st172_p32
  have hstep := st172_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p34 : ((56876295456221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT172 (i+1))
      = (∑ i ∈ Finset.range 33, stT172 (i+1)) + stT172 34 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 33
    simpa using h
  have hprev := st172_p33
  have hstep := st172_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p35 : ((56618962814061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT172 (i+1))
      = (∑ i ∈ Finset.range 34, stT172 (i+1)) + stT172 35 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 34
    simpa using h
  have hprev := st172_p34
  have hstep := st172_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p36 : ((11643588768227/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT172 (i+1))
      = (∑ i ∈ Finset.range 35, stT172 (i+1)) + stT172 36 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 35
    simpa using h
  have hprev := st172_p35
  have hstep := st172_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p37 : ((58681703274101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT172 (i+1))
      = (∑ i ∈ Finset.range 36, stT172 (i+1)) + stT172 37 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 36
    simpa using h
  have hprev := st172_p36
  have hstep := st172_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p38 : ((57080275337111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT172 (i+1))
      = (∑ i ∈ Finset.range 37, stT172 (i+1)) + stT172 38 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 37
    simpa using h
  have hprev := st172_p37
  have hstep := st172_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p39 : ((11442919438503/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT172 (i+1))
      = (∑ i ∈ Finset.range 38, stT172 (i+1)) + stT172 39 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 38
    simpa using h
  have hprev := st172_p38
  have hstep := st172_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p40 : ((11728773377523/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT172 (i+1))
      = (∑ i ∈ Finset.range 39, stT172 (i+1)) + stT172 40 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 39
    simpa using h
  have hprev := st172_p39
  have hstep := st172_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p41 : ((57413649945041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT172 (i+1))
      = (∑ i ∈ Finset.range 40, stT172 (i+1)) + stT172 41 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 40
    simpa using h
  have hprev := st172_p40
  have hstep := st172_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p42 : ((2290616179861/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT172 (i+1))
      = (∑ i ∈ Finset.range 41, stT172 (i+1)) + stT172 42 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 41
    simpa using h
  have hprev := st172_p41
  have hstep := st172_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p43 : ((11710012202087/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT172 (i+1))
      = (∑ i ∈ Finset.range 42, stT172 (i+1)) + stT172 43 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 42
    simpa using h
  have hprev := st172_p42
  have hstep := st172_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p44 : ((3567934268647/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT172 (i+1))
      = (∑ i ∈ Finset.range 43, stT172 (i+1)) + stT172 44 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 43
    simpa using h
  have hprev := st172_p43
  have hstep := st172_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p45 : ((28966408239119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT172 (i+1))
      = (∑ i ∈ Finset.range 44, stT172 (i+1)) + stT172 45 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 44
    simpa using h
  have hprev := st172_p44
  have hstep := st172_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p46 : ((28992419939117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT172 (i+1))
      = (∑ i ∈ Finset.range 45, stT172 (i+1)) + stT172 46 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 45
    simpa using h
  have hprev := st172_p45
  have hstep := st172_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p47 : ((28584900843467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT172 (i+1))
      = (∑ i ∈ Finset.range 46, stT172 (i+1)) + stT172 47 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 46
    simpa using h
  have hprev := st172_p46
  have hstep := st172_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p48 : ((29218767634967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT172 (i+1))
      = (∑ i ∈ Finset.range 47, stT172 (i+1)) + stT172 48 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 47
    simpa using h
  have hprev := st172_p47
  have hstep := st172_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p49 : ((28507563064771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT172 (i+1))
      = (∑ i ∈ Finset.range 48, stT172 (i+1)) + stT172 49 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 48
    simpa using h
  have hprev := st172_p48
  have hstep := st172_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p50 : ((58388792228619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT172 (i+1))
      = (∑ i ∈ Finset.range 49, stT172 (i+1)) + stT172 50 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 49
    simpa using h
  have hprev := st172_p49
  have hstep := st172_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p51 : ((57162745392887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT172 (i+1))
      = (∑ i ∈ Finset.range 50, stT172 (i+1)) + stT172 51 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 50
    simpa using h
  have hprev := st172_p50
  have hstep := st172_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p52 : ((58220992345637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT172 (i+1))
      = (∑ i ∈ Finset.range 51, stT172 (i+1)) + stT172 52 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 51
    simpa using h
  have hprev := st172_p51
  have hstep := st172_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p53 : ((57301334282911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT172 (i+1))
      = (∑ i ∈ Finset.range 52, stT172 (i+1)) + stT172 53 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 52
    simpa using h
  have hprev := st172_p52
  have hstep := st172_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p54 : ((29067832060373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT172 (i+1))
      = (∑ i ∈ Finset.range 53, stT172 (i+1)) + stT172 54 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 53
    simpa using h
  have hprev := st172_p53
  have hstep := st172_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p55 : ((28662149739573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT172 (i+1))
      = (∑ i ∈ Finset.range 54, stT172 (i+1)) + stT172 55 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 54
    simpa using h
  have hprev := st172_p54
  have hstep := st172_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p56 : ((29086392150617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT172 (i+1))
      = (∑ i ∈ Finset.range 55, stT172 (i+1)) + stT172 56 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 55
    simpa using h
  have hprev := st172_p55
  have hstep := st172_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p57 : ((57236253375589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT172 (i+1))
      = (∑ i ∈ Finset.range 56, stT172 (i+1)) + stT172 57 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 56
    simpa using h
  have hprev := st172_p56
  have hstep := st172_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p58 : ((11658609072329/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT172 (i+1))
      = (∑ i ∈ Finset.range 57, stT172 (i+1)) + stT172 58 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 57
    simpa using h
  have hprev := st172_p57
  have hstep := st172_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p59 : ((11422354052517/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT172 (i+1))
      = (∑ i ∈ Finset.range 58, stT172 (i+1)) + stT172 59 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 58
    simpa using h
  have hprev := st172_p58
  have hstep := st172_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p60 : ((58381096219289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT172 (i+1))
      = (∑ i ∈ Finset.range 59, stT172 (i+1)) + stT172 60 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 59
    simpa using h
  have hprev := st172_p59
  have hstep := st172_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p61 : ((57109172533213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT172 (i+1))
      = (∑ i ∈ Finset.range 60, stT172 (i+1)) + stT172 61 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 60
    simpa using h
  have hprev := st172_p60
  have hstep := st172_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p62 : ((58247017229153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT172 (i+1))
      = (∑ i ∈ Finset.range 61, stT172 (i+1)) + stT172 62 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 61
    simpa using h
  have hprev := st172_p61
  have hstep := st172_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p63 : ((11483027460533/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT172 (i+1))
      = (∑ i ∈ Finset.range 62, stT172 (i+1)) + stT172 63 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 62
    simpa using h
  have hprev := st172_p62
  have hstep := st172_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p64 : ((11554082710533/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT172 (i+1))
      = (∑ i ∈ Finset.range 63, stT172 (i+1)) + stT172 64 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 63
    simpa using h
  have hprev := st172_p63
  have hstep := st172_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p65 : ((3625030577421/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT172 (i+1))
      = (∑ i ∈ Finset.range 64, stT172 (i+1)) + stT172 65 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 64
    simpa using h
  have hprev := st172_p64
  have hstep := st172_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p66 : ((28602687385413/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT172 (i+1))
      = (∑ i ∈ Finset.range 65, stT172 (i+1)) + stT172 66 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 65
    simpa using h
  have hprev := st172_p65
  have hstep := st172_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p67 : ((455995751657/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT172 (i+1))
      = (∑ i ∈ Finset.range 66, stT172 (i+1)) + stT172 67 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 66
    simpa using h
  have hprev := st172_p66
  have hstep := st172_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p68 : ((11440380626143/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT172 (i+1))
      = (∑ i ∈ Finset.range 67, stT172 (i+1)) + stT172 68 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 67
    simpa using h
  have hprev := st172_p67
  have hstep := st172_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p69 : ((57940249707701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT172 (i+1))
      = (∑ i ∈ Finset.range 68, stT172 (i+1)) + stT172 69 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 68
    simpa using h
  have hprev := st172_p68
  have hstep := st172_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p70 : ((57947862114833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT172 (i+1))
      = (∑ i ∈ Finset.range 69, stT172 (i+1)) + stT172 70 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 69
    simpa using h
  have hprev := st172_p69
  have hstep := st172_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p71 : ((11435156893957/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT172 (i+1))
      = (∑ i ∈ Finset.range 70, stT172 (i+1)) + stT172 71 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 70
    simpa using h
  have hprev := st172_p70
  have hstep := st172_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p72 : ((14586201819431/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT172 (i+1))
      = (∑ i ∈ Finset.range 71, stT172 (i+1)) + stT172 72 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 71
    simpa using h
  have hprev := st172_p71
  have hstep := st172_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p73 : ((7175969734293/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT172 (i+1))
      = (∑ i ∈ Finset.range 72, stT172 (i+1)) + stT172 73 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 72
    simpa using h
  have hprev := st172_p72
  have hstep := st172_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p74 : ((14388679231947/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT172 (i+1))
      = (∑ i ∈ Finset.range 73, stT172 (i+1)) + stT172 74 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 73
    simpa using h
  have hprev := st172_p73
  have hstep := st172_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p75 : ((7287979002111/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT172 (i+1))
      = (∑ i ∈ Finset.range 74, stT172 (i+1)) + stT172 75 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 74
    simpa using h
  have hprev := st172_p74
  have hstep := st172_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p76 : ((57156696810017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT172 (i+1))
      = (∑ i ∈ Finset.range 75, stT172 (i+1)) + stT172 76 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 75
    simpa using h
  have hprev := st172_p75
  have hstep := st172_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p77 : ((57872304932137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT172 (i+1))
      = (∑ i ∈ Finset.range 76, stT172 (i+1)) + stT172 77 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 76
    simpa using h
  have hprev := st172_p76
  have hstep := st172_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p78 : ((2325798017603/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT172 (i+1))
      = (∑ i ∈ Finset.range 77, stT172 (i+1)) + stT172 78 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 77
    simpa using h
  have hprev := st172_p77
  have hstep := st172_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p79 : ((11419769848623/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT172 (i+1))
      = (∑ i ∈ Finset.range 78, stT172 (i+1)) + stT172 79 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 78
    simpa using h
  have hprev := st172_p78
  have hstep := st172_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p80 : ((1813154278049/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT172 (i+1))
      = (∑ i ∈ Finset.range 79, stT172 (i+1)) + stT172 80 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 79
    simpa using h
  have hprev := st172_p79
  have hstep := st172_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p81 : ((1451496533453/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT172 (i+1))
      = (∑ i ∈ Finset.range 80, stT172 (i+1)) + stT172 81 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 80
    simpa using h
  have hprev := st172_p80
  have hstep := st172_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p82 : ((7136638471701/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT172 (i+1))
      = (∑ i ∈ Finset.range 81, stT172 (i+1)) + stT172 82 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 81
    simpa using h
  have hprev := st172_p81
  have hstep := st172_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p83 : ((14506897420219/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT172 (i+1))
      = (∑ i ∈ Finset.range 82, stT172 (i+1)) + stT172 83 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 82
    simpa using h
  have hprev := st172_p82
  have hstep := st172_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p84 : ((58096270460159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT172 (i+1))
      = (∑ i ∈ Finset.range 83, stT172 (i+1)) + stT172 84 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 83
    simpa using h
  have hprev := st172_p83
  have hstep := st172_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p85 : ((7137237565207/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT172 (i+1))
      = (∑ i ∈ Finset.range 84, stT172 (i+1)) + stT172 85 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 84
    simpa using h
  have hprev := st172_p84
  have hstep := st172_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p86 : ((28951344155783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT172 (i+1))
      = (∑ i ∈ Finset.range 85, stT172 (i+1)) + stT172 86 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 85
    simpa using h
  have hprev := st172_p85
  have hstep := st172_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p87 : ((29115107119559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT172 (i+1))
      = (∑ i ∈ Finset.range 86, stT172 (i+1)) + stT172 87 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 86
    simpa using h
  have hprev := st172_p86
  have hstep := st172_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p88 : ((28583977022583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT172 (i+1))
      = (∑ i ∈ Finset.range 87, stT172 (i+1)) + stT172 88 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 87
    simpa using h
  have hprev := st172_p87
  have hstep := st172_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p89 : ((57635772061149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT172 (i+1))
      = (∑ i ∈ Finset.range 88, stT172 (i+1)) + stT172 89 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 88
    simpa using h
  have hprev := st172_p88
  have hstep := st172_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p90 : ((58363919841093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT172 (i+1))
      = (∑ i ∈ Finset.range 89, stT172 (i+1)) + stT172 90 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 89
    simpa using h
  have hprev := st172_p89
  have hstep := st172_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p91 : ((28706133400339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT172 (i+1))
      = (∑ i ∈ Finset.range 90, stT172 (i+1)) + stT172 91 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 90
    simpa using h
  have hprev := st172_p90
  have hstep := st172_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p92 : ((57283409990743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT172 (i+1))
      = (∑ i ∈ Finset.range 91, stT172 (i+1)) + stT172 92 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 91
    simpa using h
  have hprev := st172_p91
  have hstep := st172_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p93 : ((58306256383241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT172 (i+1))
      = (∑ i ∈ Finset.range 92, stT172 (i+1)) + stT172 93 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 92
    simpa using h
  have hprev := st172_p92
  have hstep := st172_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p94 : ((57872850795997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT172 (i+1))
      = (∑ i ∈ Finset.range 93, stT172 (i+1)) + stT172 94 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 93
    simpa using h
  have hprev := st172_p93
  have hstep := st172_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p95 : ((57076925015209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT172 (i+1))
      = (∑ i ∈ Finset.range 94, stT172 (i+1)) + stT172 95 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 94
    simpa using h
  have hprev := st172_p94
  have hstep := st172_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p96 : ((57884661033749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT172 (i+1))
      = (∑ i ∈ Finset.range 95, stT172 (i+1)) + stT172 96 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 95
    simpa using h
  have hprev := st172_p95
  have hstep := st172_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p97 : ((58322577732857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT172 (i+1))
      = (∑ i ∈ Finset.range 96, stT172 (i+1)) + stT172 97 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 96
    simpa using h
  have hprev := st172_p96
  have hstep := st172_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p98 : ((57344446582957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT172 (i+1))
      = (∑ i ∈ Finset.range 97, stT172 (i+1)) + stT172 98 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 97
    simpa using h
  have hprev := st172_p97
  have hstep := st172_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p99 : ((57266836543559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT172 (i+1))
      = (∑ i ∈ Finset.range 98, stT172 (i+1)) + stT172 99 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 98
    simpa using h
  have hprev := st172_p98
  have hstep := st172_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p100 : ((7282942318357/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT172 (i+1))
      = (∑ i ∈ Finset.range 99, stT172 (i+1)) + stT172 100 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 99
    simpa using h
  have hprev := st172_p99
  have hstep := st172_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p101 : ((7255637480599/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT172 (i+1))
      = (∑ i ∈ Finset.range 100, stT172 (i+1)) + stT172 101 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 100
    simpa using h
  have hprev := st172_p100
  have hstep := st172_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p102 : ((2855663627607/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT172 (i+1))
      = (∑ i ∈ Finset.range 101, stT172 (i+1)) + stT172 102 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 101
    simpa using h
  have hprev := st172_p101
  have hstep := st172_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p103 : ((28771937559873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT172 (i+1))
      = (∑ i ∈ Finset.range 102, stT172 (i+1)) + stT172 103 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 102
    simpa using h
  have hprev := st172_p102
  have hstep := st172_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p104 : ((29191584125223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT172 (i+1))
      = (∑ i ∈ Finset.range 103, stT172 (i+1)) + stT172 104 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 103
    simpa using h
  have hprev := st172_p103
  have hstep := st172_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p105 : ((1156344943283/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT172 (i+1))
      = (∑ i ∈ Finset.range 104, stT172 (i+1)) + stT172 105 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 104
    simpa using h
  have hprev := st172_p104
  have hstep := st172_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p106 : ((7132597682507/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT172 (i+1))
      = (∑ i ∈ Finset.range 105, stT172 (i+1)) + stT172 106 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 105
    simpa using h
  have hprev := st172_p105
  have hstep := st172_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p107 : ((1442496879047/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT172 (i+1))
      = (∑ i ∈ Finset.range 106, stT172 (i+1)) + stT172 107 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 106
    simpa using h
  have hprev := st172_p106
  have hstep := st172_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p108 : ((1460071990397/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT172 (i+1))
      = (∑ i ∈ Finset.range 107, stT172 (i+1)) + stT172 108 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 107
    simpa using h
  have hprev := st172_p107
  have hstep := st172_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p109 : ((57738807620683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT172 (i+1))
      = (∑ i ∈ Finset.range 108, stT172 (i+1)) + stT172 109 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 108
    simpa using h
  have hprev := st172_p108
  have hstep := st172_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p110 : ((285258038723/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT172 (i+1))
      = (∑ i ∈ Finset.range 109, stT172 (i+1)) + stT172 110 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 109
    simpa using h
  have hprev := st172_p109
  have hstep := st172_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p111 : ((28849890682479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT172 (i+1))
      = (∑ i ∈ Finset.range 110, stT172 (i+1)) + stT172 111 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 110
    simpa using h
  have hprev := st172_p110
  have hstep := st172_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p112 : ((58407883494693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT172 (i+1))
      = (∑ i ∈ Finset.range 111, stT172 (i+1)) + stT172 112 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 111
    simpa using h
  have hprev := st172_p111
  have hstep := st172_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p113 : ((5781507592717/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT172 (i+1))
      = (∑ i ∈ Finset.range 112, stT172 (i+1)) + stT172 113 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 112
    simpa using h
  have hprev := st172_p112
  have hstep := st172_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p114 : ((28528110116437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT172 (i+1))
      = (∑ i ∈ Finset.range 113, stT172 (i+1)) + stT172 114 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 113
    simpa using h
  have hprev := st172_p113
  have hstep := st172_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p115 : ((28774854404853/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT172 (i+1))
      = (∑ i ∈ Finset.range 114, stT172 (i+1)) + stT172 115 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 114
    simpa using h
  have hprev := st172_p114
  have hstep := st172_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p116 : ((29187439428021/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT172 (i+1))
      = (∑ i ∈ Finset.range 115, stT172 (i+1)) + stT172 116 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 115
    simpa using h
  have hprev := st172_p115
  have hstep := st172_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p117 : ((7253804689809/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT172 (i+1))
      = (∑ i ∈ Finset.range 116, stT172 (i+1)) + stT172 117 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 116
    simpa using h
  have hprev := st172_p116
  have hstep := st172_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p118 : ((28572174549561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT172 (i+1))
      = (∑ i ∈ Finset.range 117, stT172 (i+1)) + stT172 118 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 117
    simpa using h
  have hprev := st172_p117
  have hstep := st172_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p119 : ((14321556382971/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT172 (i+1))
      = (∑ i ∈ Finset.range 118, stT172 (i+1)) + stT172 119 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 118
    simpa using h
  have hprev := st172_p118
  have hstep := st172_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p120 : ((909356046591/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT172 (i+1))
      = (∑ i ∈ Finset.range 119, stT172 (i+1)) + stT172 120 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 119
    simpa using h
  have hprev := st172_p119
  have hstep := st172_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p121 : ((14576758991121/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT172 (i+1))
      = (∑ i ∈ Finset.range 120, stT172 (i+1)) + stT172 121 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 120
    simpa using h
  have hprev := st172_p120
  have hstep := st172_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p122 : ((28717771440237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT172 (i+1))
      = (∑ i ∈ Finset.range 121, stT172 (i+1)) + stT172 122 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 121
    simpa using h
  have hprev := st172_p121
  have hstep := st172_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p123 : ((27856644563/4882812500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT172 (i+1))
      = (∑ i ∈ Finset.range 122, stT172 (i+1)) + stT172 123 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 122
    simpa using h
  have hprev := st172_p122
  have hstep := st172_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p124 : ((28890794458229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT172 (i+1))
      = (∑ i ∈ Finset.range 123, stT172 (i+1)) + stT172 124 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 123
    simpa using h
  have hprev := st172_p123
  have hstep := st172_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p125 : ((29214251460801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT172 (i+1))
      = (∑ i ∈ Finset.range 124, stT172 (i+1)) + stT172 125 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 124
    simpa using h
  have hprev := st172_p124
  have hstep := st172_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p126 : ((57953785382703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT172 (i+1))
      = (∑ i ∈ Finset.range 125, stT172 (i+1)) + stT172 126 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 125
    simpa using h
  have hprev := st172_p125
  have hstep := st172_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p127 : ((28560214246469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT172 (i+1))
      = (∑ i ∈ Finset.range 126, stT172 (i+1)) + stT172 127 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 126
    simpa using h
  have hprev := st172_p126
  have hstep := st172_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p128 : ((28617063833263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT172 (i+1))
      = (∑ i ∈ Finset.range 127, stT172 (i+1)) + stT172 128 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 127
    simpa using h
  have hprev := st172_p127
  have hstep := st172_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p129 : ((29054923944563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT172 (i+1))
      = (∑ i ∈ Finset.range 128, stT172 (i+1)) + stT172 129 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 128
    simpa using h
  have hprev := st172_p128
  have hstep := st172_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p130 : ((912611012059/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT172 (i+1))
      = (∑ i ∈ Finset.range 129, stT172 (i+1)) + stT172 130 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 129
    simpa using h
  have hprev := st172_p129
  have hstep := st172_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p131 : ((57685273290811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT172 (i+1))
      = (∑ i ∈ Finset.range 130, stT172 (i+1)) + stT172 131 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 130
    simpa using h
  have hprev := st172_p130
  have hstep := st172_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p132 : ((14256203135833/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT172 (i+1))
      = (∑ i ∈ Finset.range 131, stT172 (i+1)) + stT172 132 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 131
    simpa using h
  have hprev := st172_p131
  have hstep := st172_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p133 : ((28695760805261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT172 (i+1))
      = (∑ i ∈ Finset.range 132, stT172 (i+1)) + stT172 133 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 132
    simpa using h
  have hprev := st172_p132
  have hstep := st172_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p134 : ((29122541400707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT172 (i+1))
      = (∑ i ∈ Finset.range 133, stT172 (i+1)) + stT172 134 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 133
    simpa using h
  have hprev := st172_p133
  have hstep := st172_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p135 : ((29181581092583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT172 (i+1))
      = (∑ i ∈ Finset.range 134, stT172 (i+1)) + stT172 135 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 134
    simpa using h
  have hprev := st172_p134
  have hstep := st172_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p136 : ((57586972383961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT172 (i+1))
      = (∑ i ∈ Finset.range 135, stT172 (i+1)) + stT172 136 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 135
    simpa using h
  have hprev := st172_p135
  have hstep := st172_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p137 : ((11400937450427/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT172 (i+1))
      = (∑ i ∈ Finset.range 136, stT172 (i+1)) + stT172 137 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 136
    simpa using h
  have hprev := st172_p136
  have hstep := st172_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p138 : ((57413577856663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT172 (i+1))
      = (∑ i ∈ Finset.range 137, stT172 (i+1)) + stT172 138 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 137
    simpa using h
  have hprev := st172_p137
  have hstep := st172_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p139 : ((58249179594931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT172 (i+1))
      = (∑ i ∈ Finset.range 138, stT172 (i+1)) + stT172 139 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 138
    simpa using h
  have hprev := st172_p138
  have hstep := st172_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p140 : ((58388473651441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT172 (i+1))
      = (∑ i ∈ Finset.range 139, stT172 (i+1)) + stT172 140 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 139
    simpa using h
  have hprev := st172_p139
  have hstep := st172_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p141 : ((57654364700129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT172 (i+1))
      = (∑ i ∈ Finset.range 140, stT172 (i+1)) + stT172 141 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 140
    simpa using h
  have hprev := st172_p140
  have hstep := st172_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p142 : ((57014287021449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT172 (i+1))
      = (∑ i ∈ Finset.range 141, stT172 (i+1)) + stT172 142 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 141
    simpa using h
  have hprev := st172_p141
  have hstep := st172_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p143 : ((57292777349741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT172 (i+1))
      = (∑ i ∈ Finset.range 142, stT172 (i+1)) + stT172 143 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 142
    simpa using h
  have hprev := st172_p142
  have hstep := st172_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p144 : ((11625125069987/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT172 (i+1))
      = (∑ i ∈ Finset.range 143, stT172 (i+1)) + stT172 144 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 143
    simpa using h
  have hprev := st172_p143
  have hstep := st172_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p145 : ((58458972076897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT172 (i+1))
      = (∑ i ∈ Finset.range 144, stT172 (i+1)) + stT172 145 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 144
    simpa using h
  have hprev := st172_p144
  have hstep := st172_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p146 : ((57883377897139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT172 (i+1))
      = (∑ i ∈ Finset.range 145, stT172 (i+1)) + stT172 146 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 145
    simpa using h
  have hprev := st172_p145
  have hstep := st172_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p147 : ((7139381461403/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT172 (i+1))
      = (∑ i ∈ Finset.range 146, stT172 (i+1)) + stT172 147 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 146
    simpa using h
  have hprev := st172_p146
  have hstep := st172_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p148 : ((28544193908707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT172 (i+1))
      = (∑ i ∈ Finset.range 147, stT172 (i+1)) + stT172 148 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 147
    simpa using h
  have hprev := st172_p147
  have hstep := st172_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p149 : ((57827819983397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT172 (i+1))
      = (∑ i ∈ Finset.range 148, stT172 (i+1)) + stT172 149 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 148
    simpa using h
  have hprev := st172_p148
  have hstep := st172_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p150 : ((58449332656117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT172 (i+1))
      = (∑ i ∈ Finset.range 149, stT172 (i+1)) + stT172 150 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 149
    simpa using h
  have hprev := st172_p149
  have hstep := st172_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p151 : ((11645248433447/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT172 (i+1))
      = (∑ i ∈ Finset.range 150, stT172 (i+1)) + stT172 151 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 150
    simpa using h
  have hprev := st172_p150
  have hstep := st172_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p152 : ((2297007027371/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT172 (i+1))
      = (∑ i ∈ Finset.range 151, stT172 (i+1)) + stT172 152 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 151
    simpa using h
  have hprev := st172_p151
  have hstep := st172_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p153 : ((56968142651221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT172 (i+1))
      = (∑ i ∈ Finset.range 152, stT172 (i+1)) + stT172 153 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 152
    simpa using h
  have hprev := st172_p152
  have hstep := st172_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p154 : ((57368338031081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT172 (i+1))
      = (∑ i ∈ Finset.range 153, stT172 (i+1)) + stT172 154 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 153
    simpa using h
  have hprev := st172_p153
  have hstep := st172_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p155 : ((3635622564683/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT172 (i+1))
      = (∑ i ∈ Finset.range 154, stT172 (i+1)) + stT172 155 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 154
    simpa using h
  have hprev := st172_p154
  have hstep := st172_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p156 : ((3655218879203/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT172 (i+1))
      = (∑ i ∈ Finset.range 155, stT172 (i+1)) + stT172 156 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 155
    simpa using h
  have hprev := st172_p155
  have hstep := st172_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p157 : ((11594278876009/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT172 (i+1))
      = (∑ i ∈ Finset.range 156, stT172 (i+1)) + stT172 157 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 156
    simpa using h
  have hprev := st172_p156
  have hstep := st172_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p158 : ((57194604388823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT172 (i+1))
      = (∑ i ∈ Finset.range 157, stT172 (i+1)) + stT172 158 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 157
    simpa using h
  have hprev := st172_p157
  have hstep := st172_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p159 : ((56984760450467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT172 (i+1))
      = (∑ i ∈ Finset.range 158, stT172 (i+1)) + stT172 159 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 158
    simpa using h
  have hprev := st172_p158
  have hstep := st172_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p160 : ((11511532733767/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT172 (i+1))
      = (∑ i ∈ Finset.range 159, stT172 (i+1)) + stT172 160 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 159
    simpa using h
  have hprev := st172_p159
  have hstep := st172_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p161 : ((11661562239649/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT172 (i+1))
      = (∑ i ∈ Finset.range 160, stT172 (i+1)) + stT172 161 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 160
    simpa using h
  have hprev := st172_p160
  have hstep := st172_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p162 : ((58459463565073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT172 (i+1))
      = (∑ i ∈ Finset.range 161, stT172 (i+1)) + stT172 162 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 161
    simpa using h
  have hprev := st172_p161
  have hstep := st172_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p163 : ((57863705849341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT172 (i+1))
      = (∑ i ∈ Finset.range 162, stT172 (i+1)) + stT172 163 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 162
    simpa using h
  have hprev := st172_p162
  have hstep := st172_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p164 : ((3570556708717/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT172 (i+1))
      = (∑ i ∈ Finset.range 163, stT172 (i+1)) + stT172 164 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 163
    simpa using h
  have hprev := st172_p163
  have hstep := st172_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p165 : ((56989617519893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT172 (i+1))
      = (∑ i ∈ Finset.range 164, stT172 (i+1)) + stT172 165 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 164
    simpa using h
  have hprev := st172_p164
  have hstep := st172_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p166 : ((57577492933643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT172 (i+1))
      = (∑ i ∈ Finset.range 165, stT172 (i+1)) + stT172 166 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 165
    simpa using h
  have hprev := st172_p165
  have hstep := st172_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p167 : ((29155791222031/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT172 (i+1))
      = (∑ i ∈ Finset.range 166, stT172 (i+1)) + stT172 167 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 166
    simpa using h
  have hprev := st172_p166
  have hstep := st172_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p168 : ((29240802641281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT172 (i+1))
      = (∑ i ∈ Finset.range 167, stT172 (i+1)) + stT172 168 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 167
    simpa using h
  have hprev := st172_p167
  have hstep := st172_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p169 : ((57930539732627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT172 (i+1))
      = (∑ i ∈ Finset.range 168, stT172 (i+1)) + stT172 169 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 168
    simpa using h
  have hprev := st172_p168
  have hstep := st172_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p170 : ((57185974712417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT172 (i+1))
      = (∑ i ∈ Finset.range 169, stT172 (i+1)) + stT172 170 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 169
    simpa using h
  have hprev := st172_p169
  have hstep := st172_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p171 : ((56945735630257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT172 (i+1))
      = (∑ i ∈ Finset.range 170, stT172 (i+1)) + stT172 171 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 170
    simpa using h
  have hprev := st172_p170
  have hstep := st172_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p172 : ((57427162404169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT172 (i+1))
      = (∑ i ∈ Finset.range 171, stT172 (i+1)) + stT172 172 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 171
    simpa using h
  have hprev := st172_p171
  have hstep := st172_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p173 : ((58182838556499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT172 (i+1))
      = (∑ i ∈ Finset.range 172, stT172 (i+1)) + stT172 173 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 172
    simpa using h
  have hprev := st172_p172
  have hstep := st172_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p174 : ((11705190287401/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT172 (i+1))
      = (∑ i ∈ Finset.range 173, stT172 (i+1)) + stT172 174 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 173
    simpa using h
  have hprev := st172_p173
  have hstep := st172_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p175 : ((11630593701823/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT172 (i+1))
      = (∑ i ∈ Finset.range 174, stT172 (i+1)) + stT172 175 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 174
    simpa using h
  have hprev := st172_p174
  have hstep := st172_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p176 : ((57401259386249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT172 (i+1))
      = (∑ i ∈ Finset.range 175, stT172 (i+1)) + stT172 176 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 175
    simpa using h
  have hprev := st172_p175
  have hstep := st172_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p177 : ((14233457227031/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT172 (i+1))
      = (∑ i ∈ Finset.range 176, stT172 (i+1)) + stT172 177 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 176
    simpa using h
  have hprev := st172_p176
  have hstep := st172_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p178 : ((57153820004279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT172 (i+1))
      = (∑ i ∈ Finset.range 177, stT172 (i+1)) + stT172 178 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 177
    simpa using h
  have hprev := st172_p177
  have hstep := st172_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p179 : ((57865759316129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT172 (i+1))
      = (∑ i ∈ Finset.range 178, stT172 (i+1)) + stT172 179 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 178
    simpa using h
  have hprev := st172_p178
  have hstep := st172_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p180 : ((58459558302559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT172 (i+1))
      = (∑ i ∈ Finset.range 179, stT172 (i+1)) + stT172 180 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 179
    simpa using h
  have hprev := st172_p179
  have hstep := st172_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p181 : ((14609107298011/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT172 (i+1))
      = (∑ i ∈ Finset.range 180, stT172 (i+1)) + stT172 181 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 180
    simpa using h
  have hprev := st172_p180
  have hstep := st172_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p182 : ((14455328314261/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT172 (i+1))
      = (∑ i ∈ Finset.range 181, stT172 (i+1)) + stT172 182 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 181
    simpa using h
  have hprev := st172_p181
  have hstep := st172_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p183 : ((28563486560387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT172 (i+1))
      = (∑ i ∈ Finset.range 182, stT172 (i+1)) + stT172 183 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 182
    simpa using h
  have hprev := st172_p182
  have hstep := st172_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p184 : ((14230258561121/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT172 (i+1))
      = (∑ i ∈ Finset.range 183, stT172 (i+1)) + stT172 184 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 183
    simpa using h
  have hprev := st172_p183
  have hstep := st172_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p185 : ((286827333481/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT172 (i+1))
      = (∑ i ∈ Finset.range 184, stT172 (i+1)) + stT172 185 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 184
    simpa using h
  have hprev := st172_p184
  have hstep := st172_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p186 : ((5809865330269/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT172 (i+1))
      = (∑ i ∈ Finset.range 185, stT172 (i+1)) + stT172 186 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 185
    simpa using h
  have hprev := st172_p185
  have hstep := st172_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p187 : ((29268519217533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT172 (i+1))
      = (∑ i ∈ Finset.range 186, stT172 (i+1)) + stT172 187 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 186
    simpa using h
  have hprev := st172_p186
  have hstep := st172_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p188 : ((58339370209641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT172 (i+1))
      = (∑ i ∈ Finset.range 187, stT172 (i+1)) + stT172 188 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 187
    simpa using h
  have hprev := st172_p187
  have hstep := st172_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p189 : ((57664889231247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT172 (i+1))
      = (∑ i ∈ Finset.range 188, stT172 (i+1)) + stT172 189 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 188
    simpa using h
  have hprev := st172_p188
  have hstep := st172_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p190 : ((14259155267727/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT172 (i+1))
      = (∑ i ∈ Finset.range 189, stT172 (i+1)) + stT172 190 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 189
    simpa using h
  have hprev := st172_p189
  have hstep := st172_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p191 : ((889572371347/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT172 (i+1))
      = (∑ i ∈ Finset.range 190, stT172 (i+1)) + stT172 191 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 190
    simpa using h
  have hprev := st172_p190
  have hstep := st172_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p192 : ((1794582349311/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT172 (i+1))
      = (∑ i ∈ Finset.range 191, stT172 (i+1)) + stT172 192 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 191
    simpa using h
  have hprev := st172_p191
  have hstep := st172_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p193 : ((58144297211287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT172 (i+1))
      = (∑ i ∈ Finset.range 192, stT172 (i+1)) + stT172 193 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 192
    simpa using h
  have hprev := st172_p192
  have hstep := st172_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p194 : ((58552719824873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT172 (i+1))
      = (∑ i ∈ Finset.range 193, stT172 (i+1)) + stT172 194 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 193
    simpa using h
  have hprev := st172_p193
  have hstep := st172_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p195 : ((1823605603069/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT172 (i+1))
      = (∑ i ∈ Finset.range 194, stT172 (i+1)) + stT172 195 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 194
    simpa using h
  have hprev := st172_p194
  have hstep := st172_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p196 : ((28850394875329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT172 (i+1))
      = (∑ i ∈ Finset.range 195, stT172 (i+1)) + stT172 196 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 195
    simpa using h
  have hprev := st172_p195
  have hstep := st172_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p197 : ((14265860066989/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT172 (i+1))
      = (∑ i ∈ Finset.range 196, stT172 (i+1)) + stT172 197 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 196
    simpa using h
  have hprev := st172_p196
  have hstep := st172_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p198 : ((28448464077473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT172 (i+1))
      = (∑ i ∈ Finset.range 197, stT172 (i+1)) + stT172 198 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 197
    simpa using h
  have hprev := st172_p197
  have hstep := st172_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p199 : ((28657277735881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT172 (i+1))
      = (∑ i ∈ Finset.range 198, stT172 (i+1)) + stT172 199 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 198
    simpa using h
  have hprev := st172_p198
  have hstep := st172_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p200 : ((725243041003/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT172 (i+1))
      = (∑ i ∈ Finset.range 199, stT172 (i+1)) + stT172 200 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 199
    simpa using h
  have hprev := st172_p199
  have hstep := st172_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p201 : ((11704241615923/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT172 (i+1))
      = (∑ i ∈ Finset.range 200, stT172 (i+1)) + stT172 201 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 200
    simpa using h
  have hprev := st172_p200
  have hstep := st172_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p202 : ((11695507150351/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT172 (i+1))
      = (∑ i ∈ Finset.range 201, stT172 (i+1)) + stT172 202 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 201
    simpa using h
  have hprev := st172_p201
  have hstep := st172_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p203 : ((14480688615043/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT172 (i+1))
      = (∑ i ∈ Finset.range 202, stT172 (i+1)) + stT172 203 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 202
    simpa using h
  have hprev := st172_p202
  have hstep := st172_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p204 : ((3577164767589/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT172 (i+1))
      = (∑ i ∈ Finset.range 203, stT172 (i+1)) + stT172 204 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 203
    simpa using h
  have hprev := st172_p203
  have hstep := st172_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p205 : ((56873204524803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT172 (i+1))
      = (∑ i ∈ Finset.range 204, stT172 (i+1)) + stT172 205 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 204
    simpa using h
  have hprev := st172_p204
  have hstep := st172_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p206 : ((5707448999177/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT172 (i+1))
      = (∑ i ∈ Finset.range 205, stT172 (i+1)) + stT172 206 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 205
    simpa using h
  have hprev := st172_p205
  have hstep := st172_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p207 : ((28850945527537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT172 (i+1))
      = (∑ i ∈ Finset.range 206, stT172 (i+1)) + stT172 207 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 206
    simpa using h
  have hprev := st172_p206
  have hstep := st172_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p208 : ((29172344254537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT172 (i+1))
      = (∑ i ∈ Finset.range 207, stT172 (i+1)) + stT172 208 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 207
    simpa using h
  have hprev := st172_p207
  have hstep := st172_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p209 : ((7323675991249/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT172 (i+1))
      = (∑ i ∈ Finset.range 208, stT172 (i+1)) + stT172 209 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 208
    simpa using h
  have hprev := st172_p208
  have hstep := st172_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p210 : ((3642714369083/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT172 (i+1))
      = (∑ i ∈ Finset.range 209, stT172 (i+1)) + stT172 210 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 209
    simpa using h
  have hprev := st172_p209
  have hstep := st172_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p211 : ((57624576503597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT172 (i+1))
      = (∑ i ∈ Finset.range 210, stT172 (i+1)) + stT172 211 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 210
    simpa using h
  have hprev := st172_p210
  have hstep := st172_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p212 : ((57028138921519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT172 (i+1))
      = (∑ i ∈ Finset.range 211, stT172 (i+1)) + stT172 212 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 211
    simpa using h
  have hprev := st172_p211
  have hstep := st172_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p213 : ((56863567486743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT172 (i+1))
      = (∑ i ∈ Finset.range 212, stT172 (i+1)) + stT172 213 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 212
    simpa using h
  have hprev := st172_p212
  have hstep := st172_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p214 : ((28614226769399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT172 (i+1))
      = (∑ i ∈ Finset.range 213, stT172 (i+1)) + stT172 214 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 213
    simpa using h
  have hprev := st172_p213
  have hstep := st172_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p215 : ((14474005329929/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT172 (i+1))
      = (∑ i ∈ Finset.range 214, stT172 (i+1)) + stT172 215 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 214
    simpa using h
  have hprev := st172_p214
  have hstep := st172_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p216 : ((58460481738321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT172 (i+1))
      = (∑ i ∈ Finset.range 215, stT172 (i+1)) + stT172 216 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 215
    simpa using h
  have hprev := st172_p215
  have hstep := st172_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p217 : ((2343386126697/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT172 (i+1))
      = (∑ i ∈ Finset.range 216, stT172 (i+1)) + stT172 217 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 216
    simpa using h
  have hprev := st172_p216
  have hstep := st172_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p218 : ((58198401702627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT172 (i+1))
      = (∑ i ∈ Finset.range 217, stT172 (i+1)) + stT172 218 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 217
    simpa using h
  have hprev := st172_p217
  have hstep := st172_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p219 : ((57533163995409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT172 (i+1))
      = (∑ i ∈ Finset.range 218, stT172 (i+1)) + stT172 219 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 218
    simpa using h
  have hprev := st172_p218
  have hstep := st172_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p220 : ((56979289143609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT172 (i+1))
      = (∑ i ∈ Finset.range 219, stT172 (i+1)) + stT172 220 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 219
    simpa using h
  have hprev := st172_p219
  have hstep := st172_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p221 : ((56856216891529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT172 (i+1))
      = (∑ i ∈ Finset.range 220, stT172 (i+1)) + stT172 221 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 220
    simpa using h
  have hprev := st172_p220
  have hstep := st172_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p222 : ((2289240716773/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT172 (i+1))
      = (∑ i ∈ Finset.range 221, stT172 (i+1)) + stT172 222 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 221
    simpa using h
  have hprev := st172_p221
  have hstep := st172_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p223 : ((7235823108813/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT172 (i+1))
      = (∑ i ∈ Finset.range 222, stT172 (i+1)) + stT172 223 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 222
    simpa using h
  have hprev := st172_p222
  have hstep := st172_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p224 : ((14612771489827/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT172 (i+1))
      = (∑ i ∈ Finset.range 223, stT172 (i+1)) + stT172 224 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 223
    simpa using h
  have hprev := st172_p223
  have hstep := st172_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p225 : ((14652421450177/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT172 (i+1))
      = (∑ i ∈ Finset.range 224, stT172 (i+1)) + stT172 225 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 224
    simpa using h
  have hprev := st172_p224
  have hstep := st172_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p226 : ((582776969549/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT172 (i+1))
      = (∑ i ∈ Finset.range 225, stT172 (i+1)) + stT172 226 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 225
    simpa using h
  have hprev := st172_p225
  have hstep := st172_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p227 : ((14410362450263/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT172 (i+1))
      = (∑ i ∈ Finset.range 226, stT172 (i+1)) + stT172 227 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 226
    simpa using h
  have hprev := st172_p226
  have hstep := st172_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p228 : ((57050100338213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT172 (i+1))
      = (∑ i ∈ Finset.range 227, stT172 (i+1)) + stT172 228 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 227
    simpa using h
  have hprev := st172_p227
  have hstep := st172_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p229 : ((7102861945897/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT172 (i+1))
      = (∑ i ∈ Finset.range 228, stT172 (i+1)) + stT172 229 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 228
    simpa using h
  have hprev := st172_p228
  have hstep := st172_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p230 : ((7134842535277/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT172 (i+1))
      = (∑ i ∈ Finset.range 229, stT172 (i+1)) + stT172 230 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 229
    simpa using h
  have hprev := st172_p229
  have hstep := st172_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p231 : ((14419459062341/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT172 (i+1))
      = (∑ i ∈ Finset.range 230, stT172 (i+1)) + stT172 231 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 230
    simpa using h
  have hprev := st172_p230
  have hstep := st172_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p232 : ((3643852713239/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT172 (i+1))
      = (∑ i ∈ Finset.range 231, stT172 (i+1)) + stT172 232 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 231
    simpa using h
  have hprev := st172_p231
  have hstep := st172_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p233 : ((7327971128501/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT172 (i+1))
      = (∑ i ∈ Finset.range 232, stT172 (i+1)) + stT172 233 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 232
    simpa using h
  have hprev := st172_p232
  have hstep := st172_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p234 : ((58479467308189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT172 (i+1))
      = (∑ i ∈ Finset.range 233, stT172 (i+1)) + stT172 234 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 233
    simpa using h
  have hprev := st172_p233
  have hstep := st172_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p235 : ((57946553654929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT172 (i+1))
      = (∑ i ∈ Finset.range 234, stT172 (i+1)) + stT172 235 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 234
    simpa using h
  have hprev := st172_p234
  have hstep := st172_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p236 : ((57299917910829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT172 (i+1))
      = (∑ i ∈ Finset.range 235, stT172 (i+1)) + stT172 236 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 235
    simpa using h
  have hprev := st172_p235
  have hstep := st172_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p237 : ((56867693383259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT172 (i+1))
      = (∑ i ∈ Finset.range 236, stT172 (i+1)) + stT172 237 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 236
    simpa using h
  have hprev := st172_p236
  have hstep := st172_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p238 : ((56865225022427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT172 (i+1))
      = (∑ i ∈ Finset.range 237, stT172 (i+1)) + stT172 238 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 237
    simpa using h
  have hprev := st172_p237
  have hstep := st172_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p239 : ((11458091410981/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT172 (i+1))
      = (∑ i ∈ Finset.range 238, stT172 (i+1)) + stT172 239 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 238
    simpa using h
  have hprev := st172_p238
  have hstep := st172_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p240 : ((7241253791117/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT172 (i+1))
      = (∑ i ∈ Finset.range 239, stT172 (i+1)) + stT172 240 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 239
    simpa using h
  have hprev := st172_p239
  have hstep := st172_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p241 : ((3654301358251/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT172 (i+1))
      = (∑ i ∈ Finset.range 240, stT172 (i+1)) + stT172 241 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 240
    simpa using h
  have hprev := st172_p240
  have hstep := st172_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p242 : ((7330697300559/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT172 (i+1))
      = (∑ i ∈ Finset.range 241, stT172 (i+1)) + stT172 242 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 241
    simpa using h
  have hprev := st172_p241
  have hstep := st172_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p243 : ((11675546883289/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT172 (i+1))
      = (∑ i ∈ Finset.range 242, stT172 (i+1)) + stT172 243 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 242
    simpa using h
  have hprev := st172_p242
  have hstep := st172_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p244 : ((2311872146387/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT172 (i+1))
      = (∑ i ∈ Finset.range 243, stT172 (i+1)) + stT172 244 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 243
    simpa using h
  have hprev := st172_p243
  have hstep := st172_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p245 : ((57180991397129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT172 (i+1))
      = (∑ i ∈ Finset.range 244, stT172 (i+1)) + stT172 245 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 244
    simpa using h
  have hprev := st172_p244
  have hstep := st172_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p246 : ((28410355011773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT172 (i+1))
      = (∑ i ∈ Finset.range 245, stT172 (i+1)) + stT172 246 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 245
    simpa using h
  have hprev := st172_p245
  have hstep := st172_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p247 : ((28441245963689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT172 (i+1))
      = (∑ i ∈ Finset.range 246, stT172 (i+1)) + stT172 247 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 246
    simpa using h
  have hprev := st172_p246
  have hstep := st172_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p248 : ((28667269451189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT172 (i+1))
      = (∑ i ∈ Finset.range 247, stT172 (i+1)) + stT172 248 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 247
    simpa using h
  have hprev := st172_p247
  have hstep := st172_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p249 : ((28982933712829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT172 (i+1))
      = (∑ i ∈ Finset.range 248, stT172 (i+1)) + stT172 249 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 248
    simpa using h
  have hprev := st172_p248
  have hstep := st172_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_p250 : ((58486752936473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT172 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT172 (i+1))
      = (∑ i ∈ Finset.range 249, stT172 (i+1)) + stT172 250 := by
    have h := Finset.sum_range_succ (fun i => stT172 (i+1)) 249
    simpa using h
  have hprev := st172_p249
  have hstep := st172_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st172_s250 :
    |Real.sin (((172 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((32731/100000 : ℚ) : ℝ))
      - ((567109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 37687/250000) (δ := 8617/1000000000) (ψ := 32731/100000) 172 151
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 172`** (evaluated boundary). -/
theorem station_172_sign : hardyG ((((172:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 172 250 (by norm_num) (by norm_num)
    ((32731/100000 : ℚ) : ℝ)
  have hchain := st172_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT172 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((172 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((32731/100000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st172_c250
  have hsinb := abs_le.mp st172_s250
  have hbdy_lo : ((-15489352535173/295842500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((172 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((32731/100000 : ℚ) : ℝ))) / 2
          - ((((172:ℕ)):ℝ))
            * Real.sin (((172 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((32731/100000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((172:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((172:ℝ) * Real.log (250:ℝ) - ((32731/100000 : ℚ) : ℝ))) / 2
        - ((172:ℝ)) * Real.sin ((172:ℝ) * Real.log (250:ℝ) - ((32731/100000 : ℚ) : ℝ))
        ≥ ((-195926389/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((172:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-195926389/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-195926389/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-195926389/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((172:ℕ)):ℝ))+1) * (((((172:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((209386496407/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((58486752936473/10000000000000 : ℚ) : ℝ) + ((-15489352535173/295842500000000 : ℚ) : ℝ)
      - ((209386496407/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((32731/100000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((172:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((32731/100000 : ℚ) : ℝ)
        * (riemannZeta (line ((((172:ℕ)):ℝ)))).re
      - Real.sin ((32731/100000 : ℚ) : ℝ)
        * (riemannZeta (line ((((172:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((172:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((172:ℕ)):ℝ))
      = (((((172:ℕ)):ℝ)) * (Real.log ((((172:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((172:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_172
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
  have hθwin : |(((32731/100000 : ℚ) : ℝ) + ((32:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((172:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((172:ℕ)):ℝ)))
    (φ := ((32731/100000 : ℚ) : ℝ) + ((32:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((32731/100000 : ℚ) : ℝ) + ((32:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((32731/100000 : ℚ)) : ℝ) - Real.pi) + ((32:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((32731/100000 : ℚ)) : ℝ) - Real.pi) 32).1,
    (cos_sin_shift ((((32731/100000 : ℚ)) : ℝ) - Real.pi) 32).2]
  exact cos_sin_flip ((32731/100000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_172_sign
end AxiomAudit
