import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 207` (rung-217.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT207 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((207 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((28259/125000 : ℚ) : ℝ))

theorem st207_c1 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((487277/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28259/500000) (δ := 1/1000000000) (ψ := 28259/125000) 207 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t1 : ((121813/125000 : ℚ) : ℝ) ≤ stT207 1 := by
  have hc : ((121813/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121813/125000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((121813/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c2 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((962/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -628937/2000000) (δ := 10367/1000000000) (ψ := 28259/125000) 207 23
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t2 : ((217640371193/1000000000000 : ℚ) : ℝ) ≤ stT207 2 := by
  have hc : ((30779/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217640371193/1000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((30779/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c3 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((547023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1239991/5000000) (δ := 523/50000000) (ψ := 28259/125000) 207 36
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t3 : ((1578974854723/5000000000000 : ℚ) : ℝ) ≤ stT207 3 := by
  have hc : ((546973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1578974854723/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((546973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c4 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-329267/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1431041/2500000) (δ := 163/15625000) (ψ := 28259/125000) 207 46
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t4 : ((-411615082323/1250000000000 : ℚ) : ℝ) ≤ stT207 4 := by
  have hc : ((-82323/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-411615082323/1250000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-82323/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c5 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((498351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -101547/5000000) (δ := 5191/500000000) (ψ := 28259/125000) 207 53
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t5 : ((222858114601/500000000000 : ℚ) : ℝ) ≤ stT207 5 := by
  have hc : ((249163/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222858114601/500000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((249163/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c6 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((124901/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -99497/10000000) (δ := 421/40000000) (ψ := 28259/125000) 207 59
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t6 : ((1019761137539/2500000000000 : ℚ) : ℝ) ≤ stT207 6 := by
  have hc : ((499579/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1019761137539/2500000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((499579/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c7 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((898933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1133673/10000000) (δ := 5271/500000000) (ψ := 28259/125000) 207 64
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t7 : ((849364434413/2500000000000 : ℚ) : ℝ) ≤ stT207 7 := by
  have hc : ((898883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((849364434413/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((898883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c8 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-245967/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 46277/62500) (δ := 1039/100000000) (ψ := 28259/125000) 207 68
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t8 : ((-869668885553/2500000000000 : ℚ) : ℝ) ≤ stT207 8 := by
  have hc : ((-491959/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-869668885553/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-491959/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c9 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-596611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5525169/10000000) (δ := 2097/200000000) (ψ := 28259/125000) 207 72
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t9 : ((-994435198887/5000000000000 : ℚ) : ℝ) ≤ stT207 9 := by
  have hc : ((-596661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-994435198887/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-596661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c10 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((55241/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -22261/80000) (δ := 2589/250000000) (ψ := 28259/125000) 207 76
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t10 : ((698670318103/5000000000000 : ℚ) : ℝ) ≤ stT207 10 := by
  have hc : ((220939/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((698670318103/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((220939/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c11 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((972887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -291743/5000000) (δ := 10469/1000000000) (ψ := 28259/125000) 207 79
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t11 : ((2933213485581/10000000000000 : ℚ) : ℝ) ≤ stT207 11 := by
  have hc : ((972837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2933213485581/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((972837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c12 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((59841/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2678977/10000000) (δ := 10513/1000000000) (ψ := 28259/125000) 207 82
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t12 : ((690912097589/5000000000000 : ℚ) : ℝ) ≤ stT207 12 := by
  have hc : ((239339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((690912097589/5000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((239339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c13 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-488941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3663597/5000000) (δ := 5199/500000000) (ψ := 28259/125000) 207 84
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t13 : ((-678073844983/2500000000000 : ℚ) : ℝ) ≤ stT207 13 := by
  have hc : ((-244483/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-678073844983/2500000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-244483/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c14 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((837381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -722903/5000000) (δ := 10477/1000000000) (ψ := 28259/125000) 207 87
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t14 : ((559465219643/2500000000000 : ℚ) : ℝ) ≤ stT207 14 := by
  have hc : ((837331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((559465219643/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((837331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c15 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((210233/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1421047/5000000) (δ := 527/50000000) (ψ := 28259/125000) 207 89
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t15 : ((4240269793/39062500000 : ℚ) : ℝ) ≤ stT207 15 := by
  have hc : ((6569/15625 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4240269793/39062500000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((6569/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c16 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-351469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4824841/10000000) (δ := 2091/200000000) (ψ := 28259/125000) 207 91
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t16 : ((-878797851519/10000000000000 : ℚ) : ℝ) ≤ stT207 16 := by
  have hc : ((-351519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-878797851519/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-351519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c17 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-33543/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 956429/2000000) (δ := 10469/1000000000) (ψ := 28259/125000) 207 93
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t17 : ((-20341469159/250000000000 : ℚ) : ℝ) ≤ stT207 17 := by
  have hc : ((-8387/25000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20341469159/250000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-8387/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c18 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((191259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 294569/1000000) (δ := 10419/1000000000) (ψ := 28259/125000) 207 95
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t18 : ((112685686287/1250000000000 : ℚ) : ℝ) ≤ stT207 18 := by
  have hc : ((95617/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112685686287/1250000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((95617/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c19 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((490409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24523/500000) (δ := 5249/500000000) (ψ := 28259/125000) 207 97
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t19 : ((70313617893/312500000000 : ℚ) : ℝ) ≤ stT207 19 := by
  have hc : ((30649/31250 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70313617893/312500000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((30649/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c20 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-543033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -670263/1250000) (δ := 2603/250000000) (ψ := 28259/125000) 207 99
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t20 : ((-303592629411/2500000000000 : ℚ) : ℝ) ≤ stT207 20 := by
  have hc : ((-543083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-303592629411/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-543083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c21 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-50289/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4178861/10000000) (δ := 649/62500000) (ψ := 28259/125000) 207 100
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t21 : ((-54897077103/2500000000000 : ℚ) : ℝ) ≤ stT207 21 := by
  have hc : ((-25157/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54897077103/2500000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-25157/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c22 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((2407/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -632593/2000000) (δ := 5267/500000000) (ψ := 28259/125000) 207 102
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t22 : ((25654440231/400000000000 : ℚ) : ℝ) ≤ stT207 22 := by
  have hc : ((12033/40000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25654440231/400000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((12033/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c23 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-41131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2066439/5000000) (δ := 10441/1000000000) (ψ := 28259/125000) 207 103
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t23 : ((-4290811381/250000000000 : ℚ) : ℝ) ≤ stT207 23 := by
  have hc : ((-10289/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4290811381/250000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-10289/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c24 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-507763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -657307/1250000) (δ := 653/62500000) (ψ := 28259/125000) 207 105
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t24 : ((-518284611873/5000000000000 : ℚ) : ℝ) ≤ stT207 24 := by
  have hc : ((-507813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-518284611873/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-507813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c25 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((997979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 79483/5000000) (δ := 10363/1000000000) (ψ := 28259/125000) 207 106
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t25 : ((997929/5000000 : ℚ) : ℝ) ≤ stT207 25 := by
  have hc : ((997929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((997929/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((997929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c26 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-12897/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 949543/2000000) (δ := 1037/100000000) (ψ := 28259/125000) 207 107
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t26 : ((-12648514319/200000000000 : ℚ) : ℝ) ≤ stT207 26 := by
  have hc : ((-12899/40000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12648514319/200000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-12899/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c27 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-38369/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3568803/5000000) (δ := 2621/250000000) (ψ := 28259/125000) 207 109
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t27 : ((-73845027871/400000000000 : ℚ) : ℝ) ≤ stT207 27 := by
  have hc : ((-38371/40000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73845027871/400000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-38371/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c28 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-9827/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -805057/2000000) (δ := 2603/250000000) (ψ := 28259/125000) 207 110
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t28 : ((-37189826817/5000000000000 : ℚ) : ℝ) ≤ stT207 28 := by
  have hc : ((-19679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37189826817/5000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-19679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c29 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((808381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3147/20000) (δ := 5249/500000000) (ψ := 28259/125000) 207 111
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t29 : ((1501032675443/10000000000000 : ℚ) : ℝ) ≤ stT207 29 := by
  have hc : ((808331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1501032675443/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((808331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c30 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((99449/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 262563/10000000) (δ := 5253/500000000) (ψ := 28259/125000) 207 112
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t30 : ((45389747001/250000000000 : ℚ) : ℝ) ≤ stT207 30 := by
  have hc : ((24861/25000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45389747001/250000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((24861/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c31 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((820021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1523373/10000000) (δ := 10513/1000000000) (ψ := 28259/125000) 207 113
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t31 : ((1472711374463/10000000000000 : ℚ) : ℝ) ≤ stT207 31 := by
  have hc : ((819971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1472711374463/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((819971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c32 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((311531/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1122681/5000000) (δ := 263/25000000) (ψ := 28259/125000) 207 114
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t32 : ((137667428899/1250000000000 : ℚ) : ℝ) ≤ stT207 32 := by
  have hc : ((155753/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137667428899/1250000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((155753/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c33 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((553129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2461701/10000000) (δ := 2619/250000000) (ψ := 28259/125000) 207 115
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t33 : ((120348331163/1250000000000 : ℚ) : ℝ) ≤ stT207 33 := by
  have hc : ((553079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120348331163/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((553079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c34 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((636329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1101333/5000000) (δ := 5267/500000000) (ψ := 28259/125000) 207 116
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t34 : ((218241788163/2000000000000 : ℚ) : ℝ) ≤ stT207 34 := by
  have hc : ((636279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218241788163/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((636279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c35 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((413149/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 747867/5000000) (δ := 5271/500000000) (ψ := 28259/125000) 207 117
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t35 : ((43644175137/312500000000 : ℚ) : ℝ) ≤ stT207 35 := by
  have hc : ((103281/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43644175137/312500000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((103281/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c36 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((98929/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 366211/10000000) (δ := 5177/500000000) (ψ := 28259/125000) 207 118
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t36 : ((20609158423/125000000000 : ℚ) : ℝ) ≤ stT207 36 := by
  have hc : ((24731/25000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20609158423/125000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((24731/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c37 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((893773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -116277/1000000) (δ := 10447/1000000000) (ψ := 28259/125000) 207 119
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t37 : ((1469270781047/10000000000000 : ℚ) : ℝ) ≤ stT207 37 := by
  have hc : ((893723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1469270781047/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((893723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c38 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((67229/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -153497/500000) (δ := 527/50000000) (ψ := 28259/125000) 207 120
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t38 : ((54521801433/1000000000000 : ℚ) : ℝ) ≤ stT207 38 := by
  have hc : ((67219/200000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54521801433/1000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((67219/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c39 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-106819/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2667791/5000000) (δ := 10533/1000000000) (ψ := 28259/125000) 207 121
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t39 : ((-85531677389/1000000000000 : ℚ) : ℝ) ≤ stT207 39 := by
  have hc : ((-106829/200000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85531677389/1000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-106829/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c40 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-499693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 388319/500000) (δ := 1037/100000000) (ψ := 28259/125000) 207 121
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t40 : ((-395061809401/2500000000000 : ℚ) : ℝ) ≤ stT207 40 := by
  have hc : ((-249859/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-395061809401/2500000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-249859/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c41 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-355957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4836837/10000000) (δ := 5213/500000000) (ψ := 28259/125000) 207 122
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t41 : ((-277994830083/5000000000000 : ℚ) : ℝ) ≤ stT207 41 := by
  have hc : ((-356007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277994830083/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-356007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c42 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((802243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 799691/5000000) (δ := 2077/200000000) (ψ := 28259/125000) 207 123
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t42 : ((1237810271369/10000000000000 : ℚ) : ℝ) ≤ stT207 42 := by
  have hc : ((802193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1237810271369/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((802193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c43 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((143217/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -482887/2500000) (δ := 10511/1000000000) (ψ := 28259/125000) 207 124
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t43 : ((43677705379/400000000000 : ℚ) : ℝ) ≤ stT207 43 := by
  have hc : ((143207/200000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43677705379/400000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((143207/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c44 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-664019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1148489/2000000) (δ := 1313/125000000) (ψ := 28259/125000) 207 125
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t44 : ((-1001121869433/10000000000000 : ℚ) : ℝ) ≤ stT207 44 := by
  have hc : ((-664069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1001121869433/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-664069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c45 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-141237/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5887229/10000000) (δ := 1313/125000000) (ψ := 28259/125000) 207 125
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t45 : ((-26319824733/250000000000 : ℚ) : ℝ) ≤ stT207 45 := by
  have hc : ((-141247/200000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26319824733/250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-141247/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c46 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((8131/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1553347/10000000) (δ := 5203/500000000) (ψ := 28259/125000) 207 126
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t46 : ((23975527359/200000000000 : ℚ) : ℝ) ≤ stT207 46 := by
  have hc : ((16261/20000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23975527359/200000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((16261/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c47 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((17649/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1512553/5000000) (δ := 10413/1000000000) (ψ := 28259/125000) 207 127
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t47 : ((51480099157/1000000000000 : ℚ) : ℝ) ≤ stT207 47 := by
  have hc : ((35293/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51480099157/1000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((35293/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c48 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-999979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1567587/2000000) (δ := 10383/1000000000) (ψ := 28259/125000) 207 128
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t48 : ((-90213616119/625000000000 : ℚ) : ℝ) ≤ stT207 48 := by
  have hc : ((-1000029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90213616119/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-1000029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c49 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((52993/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2832501/10000000) (δ := 10383/1000000000) (ψ := 28259/125000) 207 128
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t49 : ((302781337737/5000000000000 : ℚ) : ℝ) ≤ stT207 49 := by
  have hc : ((211947/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((302781337737/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((211947/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c50 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((566779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2420513/10000000) (δ := 2607/250000000) (ψ := 28259/125000) 207 129
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t50 : ((801475519277/10000000000000 : ℚ) : ℝ) ≤ stT207 50 := by
  have hc : ((566729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((801475519277/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((566729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c51 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-999943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1956833/2500000) (δ := 419/40000000) (ψ := 28259/125000) 207 129
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t51 : ((-1400271198033/10000000000000 : ℚ) : ℝ) ≤ stT207 51 := by
  have hc : ((-999993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1400271198033/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-999993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c52 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((161723/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 542059/2500000) (δ := 2087/200000000) (ψ := 28259/125000) 207 130
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t52 : ((1794016287/20000000000 : ℚ) : ℝ) ≤ stT207 52 := by
  have hc : ((323421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1794016287/20000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((323421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c53 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((48863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -920571/2500000) (δ := 10361/1000000000) (ψ := 28259/125000) 207 131
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t53 : ((6708412099/500000000000 : ℚ) : ℝ) ≤ stT207 53 := by
  have hc : ((24419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6708412099/500000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((24419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c54 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-183731/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2995439/5000000) (δ := 5221/500000000) (ψ := 28259/125000) 207 131
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t54 : ((-125021649809/1250000000000 : ℚ) : ℝ) ≤ stT207 54 := by
  have hc : ((-367487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125021649809/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-367487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c55 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((12451/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -110713/5000000) (δ := 10449/1000000000) (ψ := 28259/125000) 207 132
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t55 : ((134304585597/1000000000000 : ℚ) : ℝ) ≤ stT207 55 := by
  have hc : ((99603/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134304585597/1000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((99603/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c56 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-877743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -412801/625000) (δ := 10447/1000000000) (ψ := 28259/125000) 207 133
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t56 : ((-1173000930451/10000000000000 : ℚ) : ℝ) ≤ stT207 56 := by
  have hc : ((-877793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1173000930451/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-877793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c57 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((260877/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2554727/10000000) (δ := 10447/1000000000) (ψ := 28259/125000) 207 133
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t57 : ((21594176329/312500000000 : ℚ) : ℝ) ≤ stT207 57 := by
  have hc : ((65213/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21594176329/312500000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((65213/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c58 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-90273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -207649/500000) (δ := 10539/1000000000) (ψ := 28259/125000) 207 134
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t58 : ((-23719993999/2000000000000 : ℚ) : ℝ) ≤ stT207 58 := by
  have hc : ((-90323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23719993999/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-90323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c59 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-150887/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1173343/2500000) (δ := 10539/1000000000) (ψ := 28259/125000) 207 134
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t59 : ((-153492831/3906250000 : ℚ) : ℝ) ≤ stT207 59 := by
  have hc : ((-4716/15625 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153492831/3906250000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-4716/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c60 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((600423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2316917/10000000) (δ := 2633/250000000) (ψ := 28259/125000) 207 135
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t60 : ((387538970381/5000000000000 : ℚ) : ℝ) ≤ stT207 60 := by
  have hc : ((600373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((387538970381/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((600373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c61 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-39901/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1559249/2500000) (δ := 163/15625000) (ψ := 28259/125000) 207 135
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t61 : ((-102182408783/1000000000000 : ℚ) : ℝ) ≤ stT207 61 := by
  have hc : ((-79807/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102182408783/1000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-79807/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c62 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((456041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -528079/5000000) (δ := 5239/500000000) (ψ := 28259/125000) 207 136
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t62 : ((36196298501/312500000000 : ℚ) : ℝ) ≤ stT207 62 := by
  have hc : ((28501/31250 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36196298501/312500000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((28501/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c63 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-484211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7224049/10000000) (δ := 5239/500000000) (ψ := 28259/125000) 207 136
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t63 : ((-76260027519/625000000000 : ℚ) : ℝ) ≤ stT207 63 := by
  have hc : ((-121059/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76260027519/625000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-121059/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c64 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((24777/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -334169/10000000) (δ := 2097/200000000) (ψ := 28259/125000) 207 137
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t64 : ((99103/800000 : ℚ) : ℝ) ≤ stT207 64 := by
  have hc : ((99103/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99103/800000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((99103/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c65 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-99783/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3844627/5000000) (δ := 5209/500000000) (ψ := 28259/125000) 207 137
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t65 : ((-7735740389/62500000000 : ℚ) : ℝ) ≤ stT207 65 := by
  have hc : ((-24947/25000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7735740389/62500000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-24947/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c66 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((99889/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58889/5000000) (δ := 10411/1000000000) (ψ := 28259/125000) 207 138
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t66 : ((15368576747/125000000000 : ℚ) : ℝ) ≤ stT207 66 := by
  have hc : ((24971/25000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15368576747/125000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((24971/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c67 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-249281/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1532867/2000000) (δ := 10511/1000000000) (ψ := 28259/125000) 207 138
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t67 : ((-121824248993/1000000000000 : ℚ) : ℝ) ≤ stT207 67 := by
  have hc : ((-498587/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121824248993/1000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-498587/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c68 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((494331/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -188407/5000000) (δ := 1313/125000000) (ψ := 28259/125000) 207 139
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t68 : ((149858502867/1250000000000 : ℚ) : ℝ) ≤ stT207 68 := by
  have hc : ((247153/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149858502867/1250000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((247153/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c69 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-963673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1435613/2000000) (δ := 1313/125000000) (ψ := 28259/125000) 207 139
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t69 : ((-1160186607057/10000000000000 : ℚ) : ℝ) ≤ stT207 69 := by
  have hc : ((-963723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1160186607057/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-963723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c70 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((453751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -541873/5000000) (δ := 41/3906250) (ψ := 28259/125000) 207 140
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t70 : ((67788252441/625000000000 : ℚ) : ℝ) ≤ stT207 70 := by
  have hc : ((226863/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67788252441/625000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((226863/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c71 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-160553/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1251357/2000000) (δ := 10407/1000000000) (ψ := 28259/125000) 207 140
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t71 : ((-95276639133/1000000000000 : ℚ) : ℝ) ≤ stT207 71 := by
  have hc : ((-160563/200000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95276639133/1000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-160563/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c72 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((158263/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -553317/2500000) (δ := 5207/500000000) (ψ := 28259/125000) 207 141
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t72 : ((372999910011/5000000000000 : ℚ) : ℝ) ≤ stT207 72 := by
  have hc : ((316501/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((372999910011/5000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((316501/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c73 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-194299/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 984953/2000000) (δ := 5257/500000000) (ψ := 28259/125000) 207 141
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t73 : ((-14214946343/312500000000 : ℚ) : ℝ) ≤ stT207 73 := by
  have hc : ((-48581/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14214946343/312500000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-48581/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c74 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((73809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3742301/10000000) (δ := 5241/500000000) (ψ := 28259/125000) 207 142
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t74 : ((21435766821/2500000000000 : ℚ) : ℝ) ≤ stT207 74 := by
  have hc : ((73759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21435766821/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((73759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c75 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((285123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1602077/5000000) (δ := 10521/1000000000) (ψ := 28259/125000) 207 142
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t75 : ((3291737931/100000000000 : ℚ) : ℝ) ≤ stT207 75 := by
  have hc : ((285073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3291737931/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((285073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c76 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-635743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5649419/10000000) (δ := 419/40000000) (ψ := 28259/125000) 207 143
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t76 : ((-729304798647/10000000000000 : ℚ) : ℝ) ≤ stT207 76 := by
  have hc : ((-635793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-729304798647/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-635793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c77 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((28191/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1115393/10000000) (δ := 83/8000000) (ψ := 28259/125000) 207 143
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t77 : ((102799436551/1000000000000 : ℚ) : ℝ) ≤ stT207 77 := by
  have hc : ((451031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102799436551/1000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((451031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c78 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-499851/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7792903/10000000) (δ := 329/31250000) (ψ := 28259/125000) 207 143
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t78 : ((-70749824691/625000000000 : ℚ) : ℝ) ≤ stT207 78 := by
  have hc : ((-124969/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70749824691/625000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-124969/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c79 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((431643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -330657/2500000) (δ := 2087/200000000) (ψ := 28259/125000) 207 144
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t79 : ((242803900383/2500000000000 : ℚ) : ℝ) ≤ stT207 79 := by
  have hc : ((215809/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242803900383/2500000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((215809/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c80 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-482901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5186901/10000000) (δ := 2087/200000000) (ψ := 28259/125000) 207 144
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t80 : ((-269977819167/5000000000000 : ℚ) : ℝ) ≤ stT207 80 := by
  have hc : ((-482951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-269977819167/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-482951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c81 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-66123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4092419/10000000) (δ := 523/50000000) (ψ := 28259/125000) 207 145
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t81 : ((-9190701797/1250000000000 : ℚ) : ℝ) ≤ stT207 81 := by
  have hc : ((-66173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9190701797/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-66173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c82 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((309651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1128679/5000000) (δ := 259/25000000) (ψ := 28259/125000) 207 145
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t82 : ((34192463619/500000000000 : ℚ) : ℝ) ≤ stT207 82 := by
  have hc : ((154813/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34192463619/500000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((154813/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c83 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-963643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7177781/10000000) (δ := 10453/1000000000) (ψ := 28259/125000) 207 146
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t83 : ((-1057790875599/10000000000000 : ℚ) : ℝ) ≤ stT207 83 := by
  have hc : ((-963693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1057790875599/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-963693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c84 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((28879/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -980123/10000000) (δ := 83/4000000) (ψ := 28259/125000) 207 146
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t84 : ((504125670471/5000000000000 : ℚ) : ℝ) ≤ stT207 84 := by
  have hc : ((462039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((504125670471/5000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((462039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c85 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-116969/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1028841/2000000) (δ := 209/20000000) (ψ := 28259/125000) 207 146
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t85 : ((-253768669839/5000000000000 : ℚ) : ℝ) ≤ stT207 85 := by
  have hc : ((-233963/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253768669839/5000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-233963/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c86 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-57879/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4511079/10000000) (δ := 5273/500000000) (ψ := 28259/125000) 207 147
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t86 : ((-15606506353/625000000000 : ℚ) : ℝ) ≤ stT207 86 := by
  have hc : ((-115783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15606506353/625000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-115783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c87 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((831677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1471687/10000000) (δ := 5223/500000000) (ψ := 28259/125000) 207 147
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t87 : ((55724830389/625000000000 : ℚ) : ℝ) ≤ stT207 87 := by
  have hc : ((831627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55724830389/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((831627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c88 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-982533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7386039/10000000) (δ := 5273/500000000) (ψ := 28259/125000) 207 147
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t88 : ((-261859352083/2500000000000 : ℚ) : ℝ) ≤ stT207 88 := by
  have hc : ((-982583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-261859352083/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-982583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c89 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((548879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2474433/10000000) (δ := 10539/1000000000) (ψ := 28259/125000) 207 148
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t89 : ((581757093513/10000000000000 : ℚ) : ℝ) ≤ stT207 89 := by
  have hc : ((548829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((581757093513/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((548829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c90 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((245171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13231/40000) (δ := 10439/1000000000) (ψ := 28259/125000) 207 148
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t90 : ((64595021283/2500000000000 : ℚ) : ℝ) ≤ stT207 90 := by
  have hc : ((245121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64595021283/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((245121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c91 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-892099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1670479/2500000) (δ := 651/31250000) (ψ := 28259/125000) 207 149
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t91 : ((-187045282893/2000000000000 : ℚ) : ℝ) ≤ stT207 91 := by
  have hc : ((-892149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187045282893/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-892149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c92 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((45847/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -256533/2500000) (δ := 10471/1000000000) (ψ := 28259/125000) 207 149
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t92 : ((23898096027/250000000000 : ℚ) : ℝ) ≤ stT207 92 := by
  have hc : ((91689/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23898096027/250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((91689/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c93 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-1269/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1142127/2500000) (δ := 2633/250000000) (ψ := 28259/125000) 207 149
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t93 : ((-658075663/25000000000 : ℚ) : ℝ) ≤ stT207 93 := by
  have hc : ((-5077/20000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-658075663/25000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-5077/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c94 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-124363/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5604637/10000000) (δ := 5189/500000000) (ψ := 28259/125000) 207 150
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t94 : ((-64140524203/1000000000000 : ℚ) : ℝ) ≤ stT207 94 := by
  have hc : ((-124373/200000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64140524203/1000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-124373/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c95 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((998681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -321/25000) (δ := 5239/500000000) (ψ := 28259/125000) 207 150
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t95 : ((512286718059/5000000000000 : ℚ) : ℝ) ≤ stT207 95 := by
  have hc : ((998631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((512286718059/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((998631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c96 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-259381/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5290497/10000000) (δ := 421/40000000) (ψ := 28259/125000) 207 150
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t96 : ((-132377605563/2500000000000 : ℚ) : ℝ) ≤ stT207 96 := by
  have hc : ((-129703/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132377605563/2500000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-129703/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c97 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-435947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5054717/10000000) (δ := 10417/1000000000) (ψ := 28259/125000) 207 151
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t97 : ((-442688245959/10000000000000 : ℚ) : ℝ) ≤ stT207 97 := by
  have hc : ((-435997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-442688245959/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-435997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c98 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((994883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126511/5000000) (δ := 5193/500000000) (ψ := 28259/125000) 207 151
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t98 : ((125616568077/1250000000000 : ℚ) : ℝ) ≤ stT207 98 := by
  have hc : ((994833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125616568077/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((994833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c99 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-590727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5506889/10000000) (δ := 5193/500000000) (ψ := 28259/125000) 207 151
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t99 : ((-296876667263/5000000000000 : ℚ) : ℝ) ≤ stT207 99 := by
  have hc : ((-590777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-296876667263/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-590777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c100 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-416163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1250011/2500000) (δ := 10393/1000000000) (ψ := 28259/125000) 207 152
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t100 : ((-416213/10000000 : ℚ) : ℝ) ≤ stT207 100 := by
  have hc : ((-416213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-416213/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-416213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c101 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((499109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18661/1250000) (δ := 10393/1000000000) (ψ := 28259/125000) 207 152
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t101 : ((124151761527/1250000000000 : ℚ) : ℝ) ≤ stT207 101 := by
  have hc : ((124771/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124151761527/1250000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((124771/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c102 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-100821/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5247853/10000000) (δ := 1041/100000000) (ψ := 28259/125000) 207 152
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t102 : ((-24959403247/500000000000 : ℚ) : ℝ) ≤ stT207 102 := by
  have hc : ((-100831/200000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24959403247/500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-100831/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c103 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-559461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42276/78125) (δ := 21/2000000) (ψ := 28259/125000) 207 153
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t103 : ((-55130297363/1000000000000 : ℚ) : ℝ) ≤ stT207 103 := by
  have hc : ((-559511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55130297363/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-559511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c104 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((986497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -82259/2000000) (δ := 13/1250000) (ψ := 28259/125000) 207 153
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t104 : ((48364509963/500000000000 : ℚ) : ℝ) ≤ stT207 104 := by
  have hc : ((986447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48364509963/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((986447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c105 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-243111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4540921/10000000) (δ := 10403/1000000000) (ψ := 28259/125000) 207 153
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t105 : ((-237301063061/10000000000000 : ℚ) : ℝ) ≤ stT207 105 := by
  have hc : ((-243161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237301063061/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-243161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c106 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-803963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1252363/2000000) (δ := 2599/250000000) (ψ := 28259/125000) 207 154
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t106 : ((-390463285359/5000000000000 : ℚ) : ℝ) ≤ stT207 106 := by
  have hc : ((-804013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-390463285359/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-804013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c107 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((52919/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1402593/10000000) (δ := 10507/1000000000) (ψ := 28259/125000) 207 154
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t107 : ((25577840667/312500000000 : ℚ) : ℝ) ≤ stT207 107 := by
  have hc : ((423327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25577840667/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((423327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c108 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((102389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3411399/10000000) (δ := 10507/1000000000) (ψ := 28259/125000) 207 154
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t108 : ((98499759/5000000000 : ℚ) : ℝ) ≤ stT207 108 := by
  have hc : ((25591/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98499759/5000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((25591/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c109 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-991457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3763487/5000000) (δ := 5207/500000000) (ψ := 28259/125000) 207 155
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t109 : ((-949692175289/10000000000000 : ℚ) : ℝ) ≤ stT207 109 := by
  have hc : ((-991507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-949692175289/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-991507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c110 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((435357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -560181/2000000) (δ := 5257/500000000) (ψ := 28259/125000) 207 155
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t110 : ((207524341417/5000000000000 : ℚ) : ℝ) ≤ stT207 110 := by
  have hc : ((435307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((207524341417/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((435307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c111 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((729663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 941209/5000000) (δ := 5207/500000000) (ψ := 28259/125000) 207 155
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t111 : ((692517286241/10000000000000 : ℚ) : ℝ) ≤ stT207 111 := by
  have hc : ((729613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((692517286241/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((729613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c112 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-861731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1630917/2500000) (δ := 10489/1000000000) (ψ := 28259/125000) 207 155
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t112 : ((-50894200517/625000000000 : ℚ) : ℝ) ≤ stT207 112 := by
  have hc : ((-861781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50894200517/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-861781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c113 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-259881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4584237/10000000) (δ := 5261/500000000) (ψ := 28259/125000) 207 156
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t113 : ((-244522550251/10000000000000 : ℚ) : ℝ) ≤ stT207 113 := by
  have hc : ((-259931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244522550251/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-259931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c114 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((999951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1547/625000) (δ := 10381/1000000000) (ψ := 28259/125000) 207 156
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t114 : ((187298455617/2000000000000 : ℚ) : ℝ) ≤ stT207 114 := by
  have hc : ((999901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187298455617/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((999901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c115 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-22523/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2247469/5000000) (δ := 5211/500000000) (ψ := 28259/125000) 207 156
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t115 : ((-2051511/97656250 : ℚ) : ℝ) ≤ stT207 115 := by
  have hc : ((-704/3125 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2051511/97656250 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-704/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c116 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-45053/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -673251/1000000) (δ := 10529/1000000000) (ψ := 28259/125000) 207 157
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t116 : ((-83665990947/1000000000000 : ℚ) : ℝ) ≤ stT207 116 := by
  have hc : ((-90111/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83665990947/1000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-90111/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c117 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((608873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1145197/5000000) (δ := 5187/500000000) (ψ := 28259/125000) 207 157
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t117 : ((1125713727/20000000000 : ℚ) : ℝ) ≤ stT207 117 := by
  have hc : ((608823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1125713727/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((608823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c118 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((331657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2113893/10000000) (δ := 5237/500000000) (ψ := 28259/125000) 207 157
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t118 : ((9540368649/156250000000 : ℚ) : ℝ) ≤ stT207 118 := by
  have hc : ((20727/31250 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9540368649/156250000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((20727/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c119 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-42647/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1620243/2500000) (δ := 5237/500000000) (ψ := 28259/125000) 207 157
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t119 : ((-78193508001/1000000000000 : ℚ) : ℝ) ≤ stT207 119 := by
  have hc : ((-85299/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78193508001/1000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-85299/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c120 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-189059/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1224099/2500000) (δ := 10467/1000000000) (ψ := 28259/125000) 207 158
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t120 : ((-43152325041/1250000000000 : ℚ) : ℝ) ≤ stT207 120 := by
  have hc : ((-47271/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43152325041/1250000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-47271/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c121 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((97117/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -601767/10000000) (δ := 10467/1000000000) (ψ := 28259/125000) 207 158
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t121 : ((1103544351/12500000000 : ℚ) : ℝ) ≤ stT207 121 := by
  have hc : ((12139/12500 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1103544351/12500000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((12139/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c122 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((107581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3657517/10000000) (δ := 10367/1000000000) (ψ := 28259/125000) 207 158
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t122 : ((97353943567/10000000000000 : ℚ) : ℝ) ≤ stT207 122 := by
  have hc : ((107531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97353943567/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((107531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c123 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-999937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3912969/5000000) (δ := 10543/1000000000) (ψ := 28259/125000) 207 159
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t123 : ((-90165827829/1000000000000 : ℚ) : ℝ) ≤ stT207 123 := by
  have hc : ((-999987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90165827829/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-999987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c124 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((58139/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3635637/10000000) (δ := 10543/1000000000) (ψ := 28259/125000) 207 159
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t124 : ((13046970741/1250000000000 : ℚ) : ℝ) ≤ stT207 124 := by
  have hc : ((29057/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13046970741/1250000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((29057/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c125 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((978361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 260513/5000000) (δ := 259/25000000) (ψ := 28259/125000) 207 159
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t125 : ((875027772797/10000000000000 : ℚ) : ℝ) ≤ stT207 125 := by
  have hc : ((978311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((875027772797/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((978311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c126 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-283107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 464457/1000000) (δ := 10543/1000000000) (ψ := 28259/125000) 207 159
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t126 : ((-252256359747/10000000000000 : ℚ) : ℝ) ≤ stT207 126 := by
  have hc : ((-283157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252256359747/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-283157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c127 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-938481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -871563/1250000) (δ := 211/20000000) (ψ := 28259/125000) 207 160
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t127 : ((-832812052567/10000000000000 : ℚ) : ℝ) ≤ stT207 127 := by
  have hc : ((-938531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-832812052567/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-938531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c128 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((394329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -182103/625000) (δ := 211/20000000) (ψ := 28259/125000) 207 160
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t128 : ((348496505357/10000000000000 : ℚ) : ℝ) ≤ stT207 128 := by
  have hc : ((394279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348496505357/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((394279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c129 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((451207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27841/250000) (δ := 10353/1000000000) (ψ := 28259/125000) 207 160
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t129 : ((3972431919/50000000000 : ℚ) : ℝ) ≤ stT207 129 := by
  have hc : ((225591/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3972431919/50000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((225591/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c130 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-22783/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 204391/400000) (δ := 10353/1000000000) (ψ := 28259/125000) 207 160
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t130 : ((-39968455689/1000000000000 : ℚ) : ℝ) ≤ stT207 130 := by
  have hc : ((-45571/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39968455689/1000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-45571/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c131 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-44151/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3316319/5000000) (δ := 5273/500000000) (ψ := 28259/125000) 207 161
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t131 : ((-15430853487/200000000000 : ℚ) : ℝ) ≤ stT207 131 := by
  have hc : ((-88307/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15430853487/200000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-88307/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c132 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((59037/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2697257/10000000) (δ := 10357/1000000000) (ψ := 28259/125000) 207 161
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t132 : ((51379656431/1250000000000 : ℚ) : ℝ) ≤ stT207 132 := by
  have hc : ((236123/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51379656431/1250000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((236123/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c133 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((177087/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1208419/10000000) (δ := 10357/1000000000) (ψ := 28259/125000) 207 161
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t133 : ((153545060393/2000000000000 : ℚ) : ℝ) ≤ stT207 133 := by
  have hc : ((177077/200000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153545060393/2000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((177077/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c134 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-111689/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 508483/1000000) (δ := 10423/500000000) (ψ := 28259/125000) 207 161
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t134 : ((-192990926207/5000000000000 : ℚ) : ℝ) ≤ stT207 134 := by
  have hc : ((-223403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192990926207/5000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-223403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c135 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-113549/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3387773/5000000) (δ := 2093/200000000) (ψ := 28259/125000) 207 162
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t135 : ((-390931208523/5000000000000 : ℚ) : ℝ) ≤ stT207 135 := by
  have hc : ((-454221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-390931208523/5000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-454221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c136 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((378577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -591269/2000000) (δ := 5269/500000000) (ψ := 28259/125000) 207 162
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t136 : ((81145968571/2500000000000 : ℚ) : ℝ) ≤ stT207 136 := by
  have hc : ((378527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81145968571/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((378527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c137 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((3779/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26091/312500) (δ := 5219/500000000) (ψ := 28259/125000) 207 162
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t137 : ((8071110579/100000000000 : ℚ) : ℝ) ≤ stT207 137 := by
  have hc : ((9447/10000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8071110579/100000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((9447/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c138 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-265399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2299267/5000000) (δ := 5269/500000000) (ψ := 28259/125000) 207 162
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t138 : ((-225965319393/10000000000000 : ℚ) : ℝ) ≤ stT207 138 := by
  have hc : ((-265449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225965319393/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-265449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c139 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-122693/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1843231/2500000) (δ := 10531/1000000000) (ψ := 28259/125000) 207 163
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t139 : ((-416288616633/5000000000000 : ℚ) : ℝ) ≤ stT207 139 := by
  have hc : ((-490797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-416288616633/5000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-490797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c140 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((105311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -146529/400000) (δ := 10431/1000000000) (ψ := 28259/125000) 207 163
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t140 : ((44480877597/5000000000000 : ℚ) : ℝ) ≤ stT207 140 := by
  have hc : ((105261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44480877597/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((105261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c141 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((31249/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2003/1000000) (δ := 1309/125000000) (ψ := 28259/125000) 207 163
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t141 : ((421040971809/5000000000000 : ℚ) : ℝ) ≤ stT207 141 := by
  have hc : ((499959/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((421040971809/5000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((499959/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c142 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((24927/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1838653/5000000) (δ := 1309/125000000) (ψ := 28259/125000) 207 163
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t142 : ((41815550049/5000000000000 : ℚ) : ℝ) ≤ stT207 142 := by
  have hc : ((49829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41815550049/5000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((49829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c143 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-488163/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3654457/5000000) (δ := 1309/125000000) (ψ := 28259/125000) 207 163
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t143 : ((-102060949421/1250000000000 : ℚ) : ℝ) ≤ stT207 143 := by
  have hc : ((-122047/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102060949421/1250000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-122047/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c144 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-169721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4792799/10000000) (δ := 10379/1000000000) (ψ := 28259/125000) 207 164
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t144 : ((-35363778291/1250000000000 : ℚ) : ℝ) ≤ stT207 144 := by
  have hc : ((-84873/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35363778291/1250000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-84873/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c145 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((884873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15143/125000) (δ := 10479/1000000000) (ψ := 28259/125000) 207 164
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t145 : ((367402399821/5000000000000 : ℚ) : ℝ) ≤ stT207 145 := by
  have hc : ((884823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((367402399821/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((884823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c146 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((59131/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 469057/2000000) (δ := 2631/250000000) (ψ := 28259/125000) 207 164
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t146 : ((4893297323/100000000000 : ℚ) : ℝ) ≤ stT207 146 := by
  have hc : ((29563/50000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4893297323/100000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((29563/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c147 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-351739/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5877689/10000000) (δ := 10479/1000000000) (ψ := 28259/125000) 207 164
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t147 : ((-72532593567/1250000000000 : ℚ) : ℝ) ≤ stT207 147 := by
  have hc : ((-87941/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72532593567/1250000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-87941/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c148 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-408997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -316089/500000) (δ := 10417/1000000000) (ψ := 28259/125000) 207 165
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t148 : ((-33621403889/500000000000 : ℚ) : ℝ) ≤ stT207 148 := by
  have hc : ((-204511/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33621403889/500000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-204511/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c149 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((105589/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2836883/10000000) (δ := 5193/500000000) (ψ := 28259/125000) 207 165
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t149 : ((172983083343/5000000000000 : ℚ) : ℝ) ≤ stT207 149 := by
  have hc : ((211153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172983083343/5000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((211153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c150 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((19379/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 624623/10000000) (δ := 5243/500000000) (ψ := 28259/125000) 207 165
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t150 : ((494439359/6250000000 : ℚ) : ℝ) ≤ stT207 150 := by
  have hc : ((9689/10000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((494439359/6250000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((9689/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c151 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-27229/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4063203/10000000) (δ := 10417/1000000000) (ψ := 28259/125000) 207 165
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t151 : ((-11089502703/2500000000000 : ℚ) : ℝ) ≤ stT207 151 := by
  have hc : ((-13627/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11089502703/2500000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-13627/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c152 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-123597/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1495813/2000000) (δ := 10517/1000000000) (ψ := 28259/125000) 207 165
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t152 : ((-100255584901/1250000000000 : ℚ) : ℝ) ≤ stT207 152 := by
  have hc : ((-494413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100255584901/1250000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-494413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c153 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-88859/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4835443/10000000) (δ := 10493/1000000000) (ψ := 28259/125000) 207 166
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t153 : ((-143696861579/5000000000000 : ℚ) : ℝ) ≤ stT207 153 := by
  have hc : ((-177743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143696861579/5000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-177743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c154 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((416681/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -732043/5000000) (δ := 10393/1000000000) (ψ := 28259/125000) 207 166
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t154 : ((10492205351/156250000000 : ℚ) : ℝ) ≤ stT207 154 := by
  have hc : ((26041/31250 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10492205351/156250000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((26041/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c155 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((364419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1885433/10000000) (δ := 10493/1000000000) (ψ := 28259/125000) 207 166
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t155 : ((146344092143/2500000000000 : ℚ) : ℝ) ≤ stT207 155 := by
  have hc : ((182197/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146344092143/2500000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((182197/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c156 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-492163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5213423/10000000) (δ := 1051/100000000) (ψ := 28259/125000) 207 166
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t156 : ((-394085908533/10000000000000 : ℚ) : ℝ) ≤ stT207 156 := by
  have hc : ((-492213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-394085908533/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-492213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c157 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-241177/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3593909/5000000) (δ := 21/2000000) (ψ := 28259/125000) 207 167
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t157 : ((-384980408973/5000000000000 : ℚ) : ℝ) ≤ stT207 157 := by
  have hc : ((-482379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-384980408973/5000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-482379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c158 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((9953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3902107/10000000) (δ := 21/2000000) (ψ := 28259/125000) 207 167
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t158 : ((7878400971/10000000000000 : ℚ) : ℝ) ≤ stT207 158 := by
  have hc : ((9903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7878400971/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((9903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c159 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((120963/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -79637/1250000) (δ := 21/2000000) (ψ := 28259/125000) 207 167
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t159 : ((383699486177/5000000000000 : ℚ) : ℝ) ≤ stT207 159 := by
  have hc : ((483827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((383699486177/5000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((483827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c160 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((251829/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1303711/5000000) (δ := 21/2000000) (ψ := 28259/125000) 207 167
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t160 : ((49767109119/1250000000000 : ℚ) : ℝ) ≤ stT207 160 := by
  have hc : ((62951/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49767109119/1250000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((62951/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c161 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-690287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1166341/2000000) (δ := 10503/1000000000) (ψ := 28259/125000) 207 167
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t161 : ((-544062183407/10000000000000 : ℚ) : ℝ) ≤ stT207 161 := by
  have hc : ((-690337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-544062183407/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-690337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c162 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-890281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3335949/5000000) (δ := 2079/200000000) (ψ := 28259/125000) 207 168
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t162 : ((-27980432337/400000000000 : ℚ) : ℝ) ≤ stT207 162 := by
  have hc : ((-890331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27980432337/400000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-890331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c163 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((174989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -697451/2000000) (δ := 2099/200000000) (ψ := 28259/125000) 207 168
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t163 : ((6851136057/500000000000 : ℚ) : ℝ) ≤ stT207 163 := by
  have hc : ((174939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6851136057/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((174939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c164 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((991711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -322121/10000000) (δ := 1301/125000000) (ψ := 28259/125000) 207 168
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t164 : ((193589085437/2500000000000 : ℚ) : ℝ) ≤ stT207 164 := by
  have hc : ((991661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193589085437/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((991661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c165 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((106777/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2823761/10000000) (δ := 2099/200000000) (ψ := 28259/125000) 207 168
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t165 : ((83115949721/2500000000000 : ℚ) : ℝ) ≤ stT207 165 := by
  have hc : ((213529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83115949721/2500000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((213529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c166 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-361959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1487663/2500000) (δ := 2627/250000000) (ψ := 28259/125000) 207 168
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t166 : ((-548738757/9765625000 : ℚ) : ℝ) ≤ stT207 166 := by
  have hc : ((-11312/15625 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-548738757/9765625000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-11312/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c167 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-443051/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1329831/2000000) (δ := 2597/250000000) (ψ := 28259/125000) 207 169
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t167 : ((-1339307979/19531250000 : ℚ) : ℝ) ≤ stT207 167 := by
  have hc : ((-110769/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1339307979/19531250000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-110769/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c168 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((146417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -889907/2500000) (δ := 2083/200000000) (ψ := 28259/125000) 207 169
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t168 : ((28231120593/2500000000000 : ℚ) : ℝ) ≤ stT207 168 := by
  have hc : ((146367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28231120593/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((146367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c169 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((49049/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -488369/10000000) (δ := 2083/200000000) (ψ := 28259/125000) 207 169
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t169 : ((7545607839/100000000000 : ℚ) : ℝ) ≤ stT207 169 := by
  have hc : ((98093/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7545607839/100000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((98093/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c170 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((259169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1282363/5000000) (δ := 2103/200000000) (ψ := 28259/125000) 207 169
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t170 : ((6211066213/156250000000 : ℚ) : ℝ) ≤ stT207 170 := by
  have hc : ((32393/62500 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6211066213/156250000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((32393/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c171 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-124067/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1119983/2000000) (δ := 2083/200000000) (ψ := 28259/125000) 207 169
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t171 : ((-1186052043/25000000000 : ℚ) : ℝ) ≤ stT207 171 := by
  have hc : ((-124077/200000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1186052043/25000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-124077/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c172 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-119217/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3545279/5000000) (δ := 10481/1000000000) (ψ := 28259/125000) 207 170
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t172 : ((-363627574249/5000000000000 : ℚ) : ℝ) ≤ stT207 172 := by
  have hc : ((-476893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-363627574249/5000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-476893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c173 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-3269/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2045279/5000000) (δ := 5261/500000000) (ψ := 28259/125000) 207 170
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t173 : ((-2487275649/500000000000 : ℚ) : ℝ) ≤ stT207 173 := by
  have hc : ((-6543/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2487275649/500000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-6543/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c174 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((903411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -276961/2500000) (δ := 10481/1000000000) (ψ := 28259/125000) 207 170
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t174 : ((342418083689/5000000000000 : ℚ) : ℝ) ≤ stT207 174 := by
  have hc : ((903361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((342418083689/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((903361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c175 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((736363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 928897/5000000) (δ := 5261/500000000) (ψ := 28259/125000) 207 170
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t175 : ((69574951683/1250000000000 : ℚ) : ℝ) ≤ stT207 175 := by
  have hc : ((736313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69574951683/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((736313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c176 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-68919/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4806509/10000000) (δ := 5261/500000000) (ψ := 28259/125000) 207 170
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t176 : ((-51957232691/2000000000000 : ℚ) : ℝ) ≤ stT207 176 := by
  have hc : ((-68929/200000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51957232691/2000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-68929/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c177 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-499467/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24183/31250) (δ := 10381/1000000000) (ψ := 28259/125000) 207 170
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t177 : ((-93860415831/1250000000000 : ℚ) : ℝ) ≤ stT207 177 := by
  have hc : ((-124873/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93860415831/1250000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-124873/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c178 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-435657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -631739/1250000) (δ := 5237/500000000) (ψ := 28259/125000) 207 171
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t178 : ((-81644084781/2500000000000 : ℚ) : ℝ) ≤ stT207 178 := by
  have hc : ((-435707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81644084781/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-435707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c179 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((130201/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2154721/10000000) (δ := 10529/1000000000) (ψ := 28259/125000) 207 171
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t179 : ((19461862017/400000000000 : ℚ) : ℝ) ≤ stT207 179 := by
  have hc : ((130191/200000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19461862017/400000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((130191/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c180 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((957869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 728271/10000000) (δ := 5187/500000000) (ψ := 28259/125000) 207 171
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t180 : ((142783036149/2000000000000 : ℚ) : ℝ) ≤ stT207 180 := by
  have hc : ((957819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142783036149/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((957819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c181 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((66139/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143813/400000) (δ := 10529/1000000000) (ψ := 28259/125000) 207 171
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t181 : ((12285534879/1250000000000 : ℚ) : ℝ) ≤ stT207 181 := by
  have hc : ((33057/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12285534879/1250000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((33057/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c182 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-845671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6446543/10000000) (δ := 10529/1000000000) (ψ := 28259/125000) 207 171
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t182 : ((-501512553/8000000000 : ℚ) : ℝ) ≤ stT207 182 := by
  have hc : ((-845721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-501512553/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-845721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c183 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-841209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6425779/10000000) (δ := 1317/125000000) (ψ := 28259/125000) 207 172
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t183 : ((-310938580249/5000000000000 : ℚ) : ℝ) ≤ stT207 183 := by
  have hc : ((-841259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-310938580249/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-841259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c184 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((64099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3605611/10000000) (δ := 1317/125000000) (ψ := 28259/125000) 207 172
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t184 : ((23617964733/2500000000000 : ℚ) : ℝ) ≤ stT207 184 := by
  have hc : ((32037/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23617964733/2500000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((32037/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c185 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((474573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -80071/1000000) (δ := 10467/1000000000) (ψ := 28259/125000) 207 172
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t185 : ((43611791659/625000000000 : ℚ) : ℝ) ≤ stT207 185 := by
  have hc : ((118637/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43611791659/625000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((118637/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c186 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((87481/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1989029/10000000) (δ := 10467/1000000000) (ψ := 28259/125000) 207 172
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t186 : ((51311638653/1000000000000 : ℚ) : ℝ) ≤ stT207 186 := by
  have hc : ((349899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51311638653/1000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((349899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c187 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-82133/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 595483/1250000) (δ := 10467/1000000000) (ψ := 28259/125000) 207 172
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t187 : ((-120141572443/5000000000000 : ℚ) : ℝ) ≤ stT207 187 := by
  have hc : ((-164291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120141572443/5000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-164291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c188 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-495647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7523847/10000000) (δ := 10367/1000000000) (ψ := 28259/125000) 207 172
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t188 : ((-1807529907/25000000000 : ℚ) : ℝ) ≤ stT207 188 := by
  have hc : ((-61959/62500 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1807529907/25000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-61959/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c189 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-568511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5438727/10000000) (δ := 10359/1000000000) (ψ := 28259/125000) 207 173
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t189 : ((-413567291473/10000000000000 : ℚ) : ℝ) ≤ stT207 189 := by
  have hc : ((-568561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-413567291473/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-568561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c190 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((234273/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2707879/10000000) (δ := 659/62500000) (ψ := 28259/125000) 207 173
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t190 : ((5310665689/156250000000 : ℚ) : ℝ) ≤ stT207 190 := by
  have hc : ((29281/62500 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5310665689/156250000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((29281/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c191 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((499997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1737/2000000) (δ := 10359/1000000000) (ψ := 28259/125000) 207 173
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t191 : ((45220842491/625000000000 : ℚ) : ℝ) ≤ stT207 191 := by
  have hc : ((124993/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45220842491/625000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((124993/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c192 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((467437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1355509/5000000) (δ := 10459/1000000000) (ψ := 28259/125000) 207 173
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t192 : ((337307121869/10000000000000 : ℚ) : ℝ) ≤ stT207 192 := by
  have hc : ((467387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((337307121869/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((467387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c193 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-22219/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5399327/10000000) (δ := 10459/1000000000) (ψ := 28259/125000) 207 173
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t193 : ((-1999378917/50000000000 : ℚ) : ℝ) ≤ stT207 193 := by
  have hc : ((-22221/40000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1999378917/50000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-22221/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c194 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-498069/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1908549/2500000) (δ := 647/62500000) (ψ := 28259/125000) 207 174
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t194 : ((-178805535073/2500000000000 : ℚ) : ℝ) ≤ stT207 194 := by
  have hc : ((-249047/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178805535073/2500000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-249047/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c195 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-406493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4973521/10000000) (δ := 10551/1000000000) (ψ := 28259/125000) 207 174
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t195 : ((-58226308089/2000000000000 : ℚ) : ℝ) ≤ stT207 195 := by
  have hc : ((-406543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58226308089/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-406543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c196 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((597367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2326457/10000000) (δ := 10451/1000000000) (ψ := 28259/125000) 207 174
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t196 : ((85330914669/2000000000000 : ℚ) : ℝ) ≤ stT207 196 := by
  have hc : ((597317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85330914669/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((597317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c197 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((496231/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19197/625000) (δ := 647/62500000) (ψ := 28259/125000) 207 174
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t197 : ((17676594441/250000000000 : ℚ) : ℝ) ≤ stT207 197 := by
  have hc : ((248103/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17676594441/250000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((248103/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c198 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((24329/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 292741/1000000) (δ := 10451/1000000000) (ψ := 28259/125000) 207 174
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t198 : ((138301162083/5000000000000 : ℚ) : ℝ) ≤ stT207 198 := by
  have hc : ((194607/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138301162083/5000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((194607/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c199 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-599593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5534471/10000000) (δ := 2613/250000000) (ψ := 28259/125000) 207 174
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t199 : ((-212538064563/5000000000000 : ℚ) : ℝ) ≤ stT207 199 := by
  have hc : ((-599643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-212538064563/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-599643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c200 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-49699/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7579523/10000000) (δ := 5229/500000000) (ψ := 28259/125000) 207 175
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t200 : ((-70288557121/1000000000000 : ℚ) : ℝ) ≤ stT207 200 := by
  have hc : ((-99403/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70288557121/1000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-99403/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c201 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-415579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -124961/250000) (δ := 5229/500000000) (ψ := 28259/125000) 207 175
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t201 : ((-146581126317/5000000000000 : ℚ) : ℝ) ≤ stT207 201 := by
  have hc : ((-415629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146581126317/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-415629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c202 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((35223/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2430243/10000000) (δ := 5179/500000000) (ψ := 28259/125000) 207 175
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t202 : ((198244787123/5000000000000 : ℚ) : ℝ) ≤ stT207 202 := by
  have hc : ((281759/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198244787123/5000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((281759/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c203 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((124843/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 125327/10000000) (δ := 2089/200000000) (ψ := 28259/125000) 207 175
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t203 : ((175236342057/2500000000000 : ℚ) : ℝ) ≤ stT207 203 := by
  have hc : ((499347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175236342057/2500000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((499347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c204 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((241233/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1334161/5000000) (δ := 2089/200000000) (ψ := 28259/125000) 207 175
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t204 : ((1055496057/31250000000 : ℚ) : ℝ) ≤ stT207 204 := by
  have hc : ((30151/62500 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1055496057/31250000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((30151/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c205 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-487097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5198897/10000000) (δ := 2089/200000000) (ψ := 28259/125000) 207 175
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t205 : ((-340238566357/10000000000000 : ℚ) : ℝ) ≤ stT207 205 := by
  have hc : ((-487147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-340238566357/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-487147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c206 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-998503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1929289/2500000) (δ := 5229/500000000) (ψ := 28259/125000) 207 175
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t206 : ((-347862912951/5000000000000 : ℚ) : ℝ) ≤ stT207 206 := by
  have hc : ((-998553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-347862912951/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-998553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c207 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-291781/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2742381/5000000) (δ := 2073/200000000) (ψ := 28259/125000) 207 176
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t207 : ((-101409734247/2500000000000 : ℚ) : ℝ) ≤ stT207 207 := by
  have hc : ((-145903/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101409734247/2500000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-145903/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c208 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((73159/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1495387/5000000) (δ := 2093/200000000) (ψ := 28259/125000) 207 176
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t208 : ((405757503/16000000000 : ℚ) : ℝ) ≤ stT207 208 := by
  have hc : ((73149/200000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((405757503/16000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((73149/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c209 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((489683/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -508741/10000000) (δ := 5219/500000000) (ψ := 28259/125000) 207 176
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t209 : ((84675823453/1250000000000 : ℚ) : ℝ) ≤ stT207 209 := by
  have hc : ((244829/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84675823453/1250000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((244829/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c210 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((707687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 980721/5000000) (δ := 2073/200000000) (ψ := 28259/125000) 207 176
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t210 : ((97663105281/2000000000000 : ℚ) : ℝ) ≤ stT207 210 := by
  have hc : ((707637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97663105281/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((707637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c211 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-4897/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4419877/10000000) (δ := 5269/500000000) (ψ := 28259/125000) 207 176
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t211 : ((-13488389397/1000000000000 : ℚ) : ℝ) ≤ stT207 211 := by
  have hc : ((-19593/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13488389397/1000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-19593/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c212 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-36921/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6866669/10000000) (δ := 5219/500000000) (ψ := 28259/125000) 207 176
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t212 : ((-25358827169/400000000000 : ℚ) : ℝ) ≤ stT207 212 := by
  have hc : ((-36923/40000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25358827169/400000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-36923/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c213 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-836903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6405991/10000000) (δ := 10431/1000000000) (ψ := 28259/125000) 207 177
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t213 : ((-573470989117/10000000000000 : ℚ) : ℝ) ≤ stT207 213 := by
  have hc : ((-836953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-573470989117/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-836953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c214 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-22031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3982073/10000000) (δ := 10531/1000000000) (ψ := 28259/125000) 207 177
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t214 : ((-7547131233/5000000000000 : ℚ) : ℝ) ≤ stT207 214 := by
  have hc : ((-22081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7547131233/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-22081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c215 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((202331/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -98093/625000) (δ := 10531/1000000000) (ψ := 28259/125000) 207 177
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t215 : ((137980003089/2500000000000 : ℚ) : ℝ) ≤ stT207 215 := by
  have hc : ((404637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137980003089/2500000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((404637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c216 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((472571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 831919/10000000) (δ := 10531/1000000000) (ψ := 28259/125000) 207 177
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t216 : ((160763220749/2500000000000 : ℚ) : ℝ) ≤ stT207 216 := by
  have hc : ((236273/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160763220749/2500000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((236273/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c217 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((278197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16111/50000) (δ := 10431/1000000000) (ψ := 28259/125000) 207 177
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t217 : ((47204605517/2500000000000 : ℚ) : ℝ) ≤ stT207 217 := by
  have hc : ((278147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47204605517/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((278147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c218 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-124167/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 560151/1000000) (δ := 2593/250000000) (ψ := 28259/125000) 207 177
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t218 : ((-42051671811/1000000000000 : ℚ) : ℝ) ≤ stT207 218 := by
  have hc : ((-124177/200000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42051671811/1000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-124177/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c219 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-249731/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7738011/10000000) (δ := 10379/1000000000) (ψ := 28259/125000) 207 178
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t219 : ((-168761173203/2500000000000 : ℚ) : ℝ) ≤ stT207 219 := by
  have hc : ((-499487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168761173203/2500000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-499487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c220 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-549159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1076077/2000000) (δ := 2631/250000000) (ψ := 28259/125000) 207 178
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t220 : ((-1851383539/50000000000 : ℚ) : ℝ) ≤ stT207 220 := by
  have hc : ((-549209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1851383539/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-549209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c221 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((349867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3033419/10000000) (δ := 2631/250000000) (ψ := 28259/125000) 207 178
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t221 : ((7353503157/312500000000 : ℚ) : ℝ) ≤ stT207 221 := by
  have hc : ((349817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7353503157/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((349817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c222 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((480687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -697113/10000000) (δ := 10379/1000000000) (ψ := 28259/125000) 207 178
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t222 : ((40324898159/625000000000 : ℚ) : ℝ) ≤ stT207 222 := by
  have hc : ((240331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40324898159/625000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((240331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c223 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((397589/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1628739/10000000) (δ := 10379/1000000000) (ψ := 28259/125000) 207 178
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t223 : ((66557083759/1250000000000 : ℚ) : ℝ) ≤ stT207 223 := by
  have hc : ((99391/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66557083759/1250000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((99391/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c224 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-6879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3944189/10000000) (δ := 1303/125000000) (ψ := 28259/125000) 207 178
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t224 : ((-2314819533/5000000000000 : ℚ) : ℝ) ≤ stT207 224 := by
  have hc : ((-6929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2314819533/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-6929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c225 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-400493/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6249341/10000000) (δ := 1303/125000000) (ψ := 28259/125000) 207 178
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t225 : ((-133506066753/2500000000000 : ℚ) : ℝ) ≤ stT207 225 := by
  have hc : ((-200259/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133506066753/2500000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-200259/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c226 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-962127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3581871/5000000) (δ := 20887/1000000000) (ψ := 28259/125000) 207 179
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t226 : ((-640031480807/10000000000000 : ℚ) : ℝ) ≤ stT207 226 := by
  have hc : ((-962177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-640031480807/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-962177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c227 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-7433/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2439477/5000000) (δ := 10387/1000000000) (ψ := 28259/125000) 207 179
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t227 : ((-616765527/25000000000 : ℚ) : ℝ) ≤ stT207 227 := by
  have hc : ((-3717/10000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-616765527/25000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-3717/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c228 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((12619/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2604231/10000000) (δ := 10387/1000000000) (ψ := 28259/125000) 207 179
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t228 : ((16712613643/500000000000 : ℚ) : ℝ) ≤ stT207 228 := by
  have hc : ((50471/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16712613643/500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((50471/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c229 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((247699/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -84861/2500000) (δ := 10387/1000000000) (ψ := 28259/125000) 207 179
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t229 : ((163675697557/2500000000000 : ℚ) : ℝ) ≤ stT207 229 := by
  have hc : ((495373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163675697557/2500000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((495373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c230 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((360281/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1915459/10000000) (δ := 10487/1000000000) (ψ := 28259/125000) 207 179
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t230 : ((185582501/3906250000 : ℚ) : ℝ) ≤ stT207 230 := by
  have hc : ((11258/15625 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185582501/3906250000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((11258/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c231 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-933/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4160581/10000000) (δ := 10487/1000000000) (ψ := 28259/125000) 207 179
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t231 : ((-38387387/6250000000 : ℚ) : ℝ) ≤ stT207 231 := by
  have hc : ((-1867/20000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38387387/6250000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-1867/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c232 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-834703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3197987/5000000) (δ := 10487/1000000000) (ψ := 28259/125000) 207 179
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t232 : ((-548042891349/10000000000000 : ℚ) : ℝ) ≤ stT207 232 := by
  have hc : ((-834753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-548042891349/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-834753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c233 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-953207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -708617/1000000) (δ := 5247/500000000) (ψ := 28259/125000) 207 180
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t233 : ((-312249816177/5000000000000 : ℚ) : ℝ) ≤ stT207 233 := by
  have hc : ((-953257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-312249816177/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-953257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c234 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-14731/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4869873/10000000) (δ := 5197/500000000) (ψ := 28259/125000) 207 180
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t234 : ((-9631271493/400000000000 : ℚ) : ℝ) ≤ stT207 234 := by
  have hc : ((-14733/40000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9631271493/400000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-14733/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c235 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((484313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1331523/5000000) (δ := 5197/500000000) (ψ := 28259/125000) 207 180
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t235 : ((39487289283/1250000000000 : ℚ) : ℝ) ≤ stT207 235 := by
  have hc : ((484263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39487289283/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((484263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c236 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((245677/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -232793/5000000) (δ := 10409/1000000000) (ψ := 28259/125000) 207 180
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t236 : ((4997307259/78125000000 : ℚ) : ℝ) ≤ stT207 236 := by
  have hc : ((491329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4997307259/78125000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((491329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c237 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((771867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1722559/10000000) (δ := 10509/1000000000) (ψ := 28259/125000) 207 180
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t237 : ((501348396873/10000000000000 : ℚ) : ℝ) ≤ stT207 237 := by
  have hc : ((771817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((501348396873/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((771817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c238 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((10199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3901493/10000000) (δ := 10409/1000000000) (ψ := 28259/125000) 207 180
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t238 : ((6578612247/10000000000000 : ℚ) : ℝ) ≤ stT207 238 := by
  have hc : ((10149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6578612247/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((10149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c239 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-18909/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6071319/10000000) (δ := 5197/500000000) (ψ := 28259/125000) 207 180
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t239 : ((-48928153927/1000000000000 : ℚ) : ℝ) ≤ stT207 239 := by
  have hc : ((-75641/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48928153927/1000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-75641/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c240 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-197717/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -59807/80000) (δ := 5201/500000000) (ψ := 28259/125000) 207 181
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t240 : ((-63816191523/1000000000000 : ℚ) : ℝ) ≤ stT207 240 := by
  have hc : ((-197727/200000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63816191523/1000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-197727/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c241 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-53021/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -532411/1000000) (δ := 5201/500000000) (ψ := 28259/125000) 207 181
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t241 : ((-17078534541/500000000000 : ℚ) : ℝ) ≤ stT207 241 := by
  have hc : ((-26513/50000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17078534541/500000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-26513/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c242 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((146947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1590623/5000000) (δ := 5201/500000000) (ψ := 28259/125000) 207 181
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t242 : ((5902811733/312500000000 : ℚ) : ℝ) ≤ stT207 242 := by
  have hc : ((73461/250000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5902811733/312500000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((73461/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c243 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((45677/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1047231/10000000) (δ := 10401/1000000000) (ψ := 28259/125000) 207 181
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t243 : ((117200767/2000000000 : ℚ) : ℝ) ≤ stT207 243 := by
  have hc : ((91349/100000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117200767/2000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((91349/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c244 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((454229/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 539019/5000000) (δ := 10401/1000000000) (ψ := 28259/125000) 207 181
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t244 : ((9086691673/156250000000 : ℚ) : ℝ) ≤ stT207 244 := by
  have hc : ((113551/125000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9086691673/156250000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((113551/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c245 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((288789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3194587/10000000) (δ := 10351/500000000) (ψ := 28259/125000) 207 181
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t245 : ((46117104341/2500000000000 : ℚ) : ℝ) ≤ stT207 245 := by
  have hc : ((288739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46117104341/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((288739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c246 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-522877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2651273/5000000) (δ := 10501/1000000000) (ψ := 28259/125000) 207 181
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t246 : ((-333406227879/10000000000000 : ℚ) : ℝ) ≤ stT207 246 := by
  have hc : ((-522927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333406227879/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-522927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c247 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-983697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 370097/500000) (δ := 10501/1000000000) (ψ := 28259/125000) 207 181
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t247 : ((-125188691979/2000000000000 : ℚ) : ℝ) ≤ stT207 247 := by
  have hc : ((-983747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125188691979/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-983747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c248 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-158543/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6215117/10000000) (δ := 2099/200000000) (ψ := 28259/125000) 207 182
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t248 : ((-100681313553/2000000000000 : ℚ) : ℝ) ≤ stT207 248 := by
  have hc : ((-158553/200000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100681313553/2000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-158553/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c249 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-82169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -826529/2000000) (δ := 2079/200000000) (ψ := 28259/125000) 207 182
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t249 : ((-2084169431/400000000000 : ℚ) : ℝ) ≤ stT207 249 := by
  have hc : ((-82219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2084169431/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-82219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_c250 :
    |Real.cos (((207 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((135949/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2058453/10000000) (δ := 1301/125000000) (ψ := 28259/125000) 207 182
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st207_t250 : ((17195060049/400000000000 : ℚ) : ℝ) ≤ stT207 250 := by
  have hc : ((135939/200000 : ℚ) : ℝ)
      ≤ Real.cos (((207 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((28259/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st207_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17195060049/400000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((135939/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st207_p1 : ((121813/125000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT207 (i+1) := by
  rw [Finset.sum_range_one]
  exact st207_t1

theorem st207_p2 : ((1192144371193/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT207 (i+1))
      = (∑ i ∈ Finset.range 1, stT207 (i+1)) + stT207 2 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 1
    simpa using h
  have hprev := st207_p1
  have hstep := st207_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p3 : ((235615522209/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT207 (i+1))
      = (∑ i ∈ Finset.range 2, stT207 (i+1)) + stT207 3 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 2
    simpa using h
  have hprev := st207_p2
  have hstep := st207_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p4 : ((1473309095349/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT207 (i+1))
      = (∑ i ∈ Finset.range 3, stT207 (i+1)) + stT207 4 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 3
    simpa using h
  have hprev := st207_p3
  have hstep := st207_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p5 : ((4060908763703/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT207 (i+1))
      = (∑ i ∈ Finset.range 4, stT207 (i+1)) + stT207 5 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 4
    simpa using h
  have hprev := st207_p4
  have hstep := st207_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p6 : ((2540334950621/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT207 (i+1))
      = (∑ i ∈ Finset.range 5, stT207 (i+1)) + stT207 6 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 5
    simpa using h
  have hprev := st207_p5
  have hstep := st207_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p7 : ((1186006867131/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT207 (i+1))
      = (∑ i ∈ Finset.range 6, stT207 (i+1)) + stT207 7 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 6
    simpa using h
  have hprev := st207_p6
  have hstep := st207_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p8 : ((2530182725051/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT207 (i+1))
      = (∑ i ∈ Finset.range 7, stT207 (i+1)) + stT207 8 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 7
    simpa using h
  have hprev := st207_p7
  have hstep := st207_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p9 : ((9126295701317/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT207 (i+1))
      = (∑ i ∈ Finset.range 8, stT207 (i+1)) + stT207 9 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 8
    simpa using h
  have hprev := st207_p8
  have hstep := st207_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p10 : ((491248300971/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT207 (i+1))
      = (∑ i ∈ Finset.range 9, stT207 (i+1)) + stT207 10 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 9
    simpa using h
  have hprev := st207_p9
  have hstep := st207_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p11 : ((22583145524421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT207 (i+1))
      = (∑ i ∈ Finset.range 10, stT207 (i+1)) + stT207 11 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 10
    simpa using h
  have hprev := st207_p10
  have hstep := st207_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p12 : ((23964969719599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT207 (i+1))
      = (∑ i ∈ Finset.range 11, stT207 (i+1)) + stT207 12 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 11
    simpa using h
  have hprev := st207_p11
  have hstep := st207_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p13 : ((21252674339667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT207 (i+1))
      = (∑ i ∈ Finset.range 12, stT207 (i+1)) + stT207 13 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 12
    simpa using h
  have hprev := st207_p12
  have hstep := st207_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p14 : ((23490535218239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT207 (i+1))
      = (∑ i ∈ Finset.range 13, stT207 (i+1)) + stT207 14 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 13
    simpa using h
  have hprev := st207_p13
  have hstep := st207_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p15 : ((24576044285247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT207 (i+1))
      = (∑ i ∈ Finset.range 14, stT207 (i+1)) + stT207 15 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 14
    simpa using h
  have hprev := st207_p14
  have hstep := st207_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p16 : ((370269475527/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT207 (i+1))
      = (∑ i ∈ Finset.range 15, stT207 (i+1)) + stT207 16 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 15
    simpa using h
  have hprev := st207_p15
  have hstep := st207_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p17 : ((2860448458421/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT207 (i+1))
      = (∑ i ∈ Finset.range 16, stT207 (i+1)) + stT207 17 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 16
    simpa using h
  have hprev := st207_p16
  have hstep := st207_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p18 : ((743283536177/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT207 (i+1))
      = (∑ i ∈ Finset.range 17, stT207 (i+1)) + stT207 18 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 17
    simpa using h
  have hprev := st207_p17
  have hstep := st207_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p19 : ((81359715407/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT207 (i+1))
      = (∑ i ∈ Finset.range 18, stT207 (i+1)) + stT207 19 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 18
    simpa using h
  have hprev := st207_p18
  have hstep := st207_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p20 : ((6205184603149/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT207 (i+1))
      = (∑ i ∈ Finset.range 19, stT207 (i+1)) + stT207 20 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 19
    simpa using h
  have hprev := st207_p19
  have hstep := st207_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p21 : ((3075143763023/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT207 (i+1))
      = (∑ i ∈ Finset.range 20, stT207 (i+1)) + stT207 21 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 20
    simpa using h
  have hprev := st207_p20
  have hstep := st207_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p22 : ((25242511109959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT207 (i+1))
      = (∑ i ∈ Finset.range 21, stT207 (i+1)) + stT207 22 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 21
    simpa using h
  have hprev := st207_p21
  have hstep := st207_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p23 : ((25070878654719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT207 (i+1))
      = (∑ i ∈ Finset.range 22, stT207 (i+1)) + stT207 23 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 22
    simpa using h
  have hprev := st207_p22
  have hstep := st207_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p24 : ((24034309430973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT207 (i+1))
      = (∑ i ∈ Finset.range 23, stT207 (i+1)) + stT207 24 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 23
    simpa using h
  have hprev := st207_p23
  have hstep := st207_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p25 : ((26030167430973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT207 (i+1))
      = (∑ i ∈ Finset.range 24, stT207 (i+1)) + stT207 25 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 24
    simpa using h
  have hprev := st207_p24
  have hstep := st207_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p26 : ((25397741715023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT207 (i+1))
      = (∑ i ∈ Finset.range 25, stT207 (i+1)) + stT207 26 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 25
    simpa using h
  have hprev := st207_p25
  have hstep := st207_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p27 : ((2943952002281/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT207 (i+1))
      = (∑ i ∈ Finset.range 26, stT207 (i+1)) + stT207 27 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 26
    simpa using h
  have hprev := st207_p26
  have hstep := st207_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p28 : ((11738618182307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT207 (i+1))
      = (∑ i ∈ Finset.range 27, stT207 (i+1)) + stT207 28 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 27
    simpa using h
  have hprev := st207_p27
  have hstep := st207_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p29 : ((24978269040057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT207 (i+1))
      = (∑ i ∈ Finset.range 28, stT207 (i+1)) + stT207 29 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 28
    simpa using h
  have hprev := st207_p28
  have hstep := st207_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p30 : ((26793858920097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT207 (i+1))
      = (∑ i ∈ Finset.range 29, stT207 (i+1)) + stT207 30 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 29
    simpa using h
  have hprev := st207_p29
  have hstep := st207_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p31 : ((176666064341/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT207 (i+1))
      = (∑ i ∈ Finset.range 30, stT207 (i+1)) + stT207 31 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 30
    simpa using h
  have hprev := st207_p30
  have hstep := st207_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p32 : ((3670988715719/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT207 (i+1))
      = (∑ i ∈ Finset.range 31, stT207 (i+1)) + stT207 32 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 31
    simpa using h
  have hprev := st207_p31
  have hstep := st207_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p33 : ((1895668523441/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT207 (i+1))
      = (∑ i ∈ Finset.range 32, stT207 (i+1)) + stT207 33 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 32
    simpa using h
  have hprev := st207_p32
  have hstep := st207_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p34 : ((31421905315871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT207 (i+1))
      = (∑ i ∈ Finset.range 33, stT207 (i+1)) + stT207 34 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 33
    simpa using h
  have hprev := st207_p33
  have hstep := st207_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p35 : ((6563703784051/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT207 (i+1))
      = (∑ i ∈ Finset.range 34, stT207 (i+1)) + stT207 35 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 34
    simpa using h
  have hprev := st207_p34
  have hstep := st207_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p36 : ((6893450318819/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT207 (i+1))
      = (∑ i ∈ Finset.range 35, stT207 (i+1)) + stT207 36 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 35
    simpa using h
  have hprev := st207_p35
  have hstep := st207_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p37 : ((17968261187571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT207 (i+1))
      = (∑ i ∈ Finset.range 36, stT207 (i+1)) + stT207 37 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 36
    simpa using h
  have hprev := st207_p36
  have hstep := st207_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p38 : ((1140054387171/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT207 (i+1))
      = (∑ i ∈ Finset.range 37, stT207 (i+1)) + stT207 38 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 37
    simpa using h
  have hprev := st207_p37
  have hstep := st207_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p39 : ((17813211807791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT207 (i+1))
      = (∑ i ∈ Finset.range 38, stT207 (i+1)) + stT207 39 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 38
    simpa using h
  have hprev := st207_p38
  have hstep := st207_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p40 : ((17023088188989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT207 (i+1))
      = (∑ i ∈ Finset.range 39, stT207 (i+1)) + stT207 40 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 39
    simpa using h
  have hprev := st207_p39
  have hstep := st207_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p41 : ((8372546679453/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT207 (i+1))
      = (∑ i ∈ Finset.range 40, stT207 (i+1)) + stT207 41 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 40
    simpa using h
  have hprev := st207_p40
  have hstep := st207_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p42 : ((34727996989181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT207 (i+1))
      = (∑ i ∈ Finset.range 41, stT207 (i+1)) + stT207 42 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 41
    simpa using h
  have hprev := st207_p41
  have hstep := st207_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p43 : ((4477492452957/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT207 (i+1))
      = (∑ i ∈ Finset.range 42, stT207 (i+1)) + stT207 43 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 42
    simpa using h
  have hprev := st207_p42
  have hstep := st207_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p44 : ((34818817754223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT207 (i+1))
      = (∑ i ∈ Finset.range 43, stT207 (i+1)) + stT207 44 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 43
    simpa using h
  have hprev := st207_p43
  have hstep := st207_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p45 : ((33766024764903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT207 (i+1))
      = (∑ i ∈ Finset.range 44, stT207 (i+1)) + stT207 45 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 44
    simpa using h
  have hprev := st207_p44
  have hstep := st207_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p46 : ((34964801132853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT207 (i+1))
      = (∑ i ∈ Finset.range 45, stT207 (i+1)) + stT207 46 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 45
    simpa using h
  have hprev := st207_p45
  have hstep := st207_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p47 : ((35479602124423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT207 (i+1))
      = (∑ i ∈ Finset.range 46, stT207 (i+1)) + stT207 47 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 46
    simpa using h
  have hprev := st207_p46
  have hstep := st207_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p48 : ((34036184266519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT207 (i+1))
      = (∑ i ∈ Finset.range 47, stT207 (i+1)) + stT207 48 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 47
    simpa using h
  have hprev := st207_p47
  have hstep := st207_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p49 : ((34641746941993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT207 (i+1))
      = (∑ i ∈ Finset.range 48, stT207 (i+1)) + stT207 49 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 48
    simpa using h
  have hprev := st207_p48
  have hstep := st207_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p50 : ((3544322246127/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT207 (i+1))
      = (∑ i ∈ Finset.range 49, stT207 (i+1)) + stT207 50 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 49
    simpa using h
  have hprev := st207_p49
  have hstep := st207_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p51 : ((34042951263237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT207 (i+1))
      = (∑ i ∈ Finset.range 50, stT207 (i+1)) + stT207 51 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 50
    simpa using h
  have hprev := st207_p50
  have hstep := st207_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p52 : ((34939959406737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT207 (i+1))
      = (∑ i ∈ Finset.range 51, stT207 (i+1)) + stT207 52 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 51
    simpa using h
  have hprev := st207_p51
  have hstep := st207_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p53 : ((35074127648717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT207 (i+1))
      = (∑ i ∈ Finset.range 52, stT207 (i+1)) + stT207 53 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 52
    simpa using h
  have hprev := st207_p52
  have hstep := st207_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p54 : ((6814790890049/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT207 (i+1))
      = (∑ i ∈ Finset.range 53, stT207 (i+1)) + stT207 54 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 53
    simpa using h
  have hprev := st207_p53
  have hstep := st207_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p55 : ((7083400061243/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT207 (i+1))
      = (∑ i ∈ Finset.range 54, stT207 (i+1)) + stT207 55 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 54
    simpa using h
  have hprev := st207_p54
  have hstep := st207_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p56 : ((8560999843941/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT207 (i+1))
      = (∑ i ∈ Finset.range 55, stT207 (i+1)) + stT207 56 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 55
    simpa using h
  have hprev := st207_p55
  have hstep := st207_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p57 : ((8733753254573/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT207 (i+1))
      = (∑ i ∈ Finset.range 56, stT207 (i+1)) + stT207 57 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 56
    simpa using h
  have hprev := st207_p56
  have hstep := st207_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p58 : ((34816413048297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT207 (i+1))
      = (∑ i ∈ Finset.range 57, stT207 (i+1)) + stT207 58 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 57
    simpa using h
  have hprev := st207_p57
  have hstep := st207_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p59 : ((34423471400937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT207 (i+1))
      = (∑ i ∈ Finset.range 58, stT207 (i+1)) + stT207 59 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 58
    simpa using h
  have hprev := st207_p58
  have hstep := st207_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p60 : ((35198549341699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT207 (i+1))
      = (∑ i ∈ Finset.range 59, stT207 (i+1)) + stT207 60 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 59
    simpa using h
  have hprev := st207_p59
  have hstep := st207_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p61 : ((34176725253869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT207 (i+1))
      = (∑ i ∈ Finset.range 60, stT207 (i+1)) + stT207 61 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 60
    simpa using h
  have hprev := st207_p60
  have hstep := st207_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p62 : ((35335006805901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT207 (i+1))
      = (∑ i ∈ Finset.range 61, stT207 (i+1)) + stT207 62 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 61
    simpa using h
  have hprev := st207_p61
  have hstep := st207_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p63 : ((34114846365597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT207 (i+1))
      = (∑ i ∈ Finset.range 62, stT207 (i+1)) + stT207 63 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 62
    simpa using h
  have hprev := st207_p62
  have hstep := st207_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p64 : ((35353633865597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT207 (i+1))
      = (∑ i ∈ Finset.range 63, stT207 (i+1)) + stT207 64 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 63
    simpa using h
  have hprev := st207_p63
  have hstep := st207_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p65 : ((34115915403357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT207 (i+1))
      = (∑ i ∈ Finset.range 64, stT207 (i+1)) + stT207 65 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 64
    simpa using h
  have hprev := st207_p64
  have hstep := st207_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p66 : ((35345401543117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT207 (i+1))
      = (∑ i ∈ Finset.range 65, stT207 (i+1)) + stT207 66 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 65
    simpa using h
  have hprev := st207_p65
  have hstep := st207_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p67 : ((34127159053187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT207 (i+1))
      = (∑ i ∈ Finset.range 66, stT207 (i+1)) + stT207 67 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 66
    simpa using h
  have hprev := st207_p66
  have hstep := st207_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p68 : ((35326027076123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT207 (i+1))
      = (∑ i ∈ Finset.range 67, stT207 (i+1)) + stT207 68 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 67
    simpa using h
  have hprev := st207_p67
  have hstep := st207_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p69 : ((17082920234533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT207 (i+1))
      = (∑ i ∈ Finset.range 68, stT207 (i+1)) + stT207 69 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 68
    simpa using h
  have hprev := st207_p68
  have hstep := st207_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p70 : ((17625226254061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT207 (i+1))
      = (∑ i ∈ Finset.range 69, stT207 (i+1)) + stT207 70 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 69
    simpa using h
  have hprev := st207_p69
  have hstep := st207_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p71 : ((4287210764599/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT207 (i+1))
      = (∑ i ∈ Finset.range 70, stT207 (i+1)) + stT207 71 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 70
    simpa using h
  have hprev := st207_p70
  have hstep := st207_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p72 : ((17521842968407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT207 (i+1))
      = (∑ i ∈ Finset.range 71, stT207 (i+1)) + stT207 72 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 71
    simpa using h
  have hprev := st207_p71
  have hstep := st207_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p73 : ((17294403826919/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT207 (i+1))
      = (∑ i ∈ Finset.range 72, stT207 (i+1)) + stT207 73 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 72
    simpa using h
  have hprev := st207_p72
  have hstep := st207_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p74 : ((17337275360561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT207 (i+1))
      = (∑ i ∈ Finset.range 73, stT207 (i+1)) + stT207 74 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 73
    simpa using h
  have hprev := st207_p73
  have hstep := st207_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p75 : ((17501862257111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT207 (i+1))
      = (∑ i ∈ Finset.range 74, stT207 (i+1)) + stT207 75 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 74
    simpa using h
  have hprev := st207_p74
  have hstep := st207_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p76 : ((1370976788623/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT207 (i+1))
      = (∑ i ∈ Finset.range 75, stT207 (i+1)) + stT207 76 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 75
    simpa using h
  have hprev := st207_p75
  have hstep := st207_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p77 : ((7060482816217/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT207 (i+1))
      = (∑ i ∈ Finset.range 76, stT207 (i+1)) + stT207 77 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 76
    simpa using h
  have hprev := st207_p76
  have hstep := st207_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p78 : ((34170416886029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT207 (i+1))
      = (∑ i ∈ Finset.range 77, stT207 (i+1)) + stT207 78 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 77
    simpa using h
  have hprev := st207_p77
  have hstep := st207_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p79 : ((35141632487561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT207 (i+1))
      = (∑ i ∈ Finset.range 78, stT207 (i+1)) + stT207 79 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 78
    simpa using h
  have hprev := st207_p78
  have hstep := st207_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p80 : ((34601676849227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT207 (i+1))
      = (∑ i ∈ Finset.range 79, stT207 (i+1)) + stT207 80 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 79
    simpa using h
  have hprev := st207_p79
  have hstep := st207_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p81 : ((34528151234851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT207 (i+1))
      = (∑ i ∈ Finset.range 80, stT207 (i+1)) + stT207 81 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 80
    simpa using h
  have hprev := st207_p80
  have hstep := st207_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p82 : ((35212000507231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT207 (i+1))
      = (∑ i ∈ Finset.range 81, stT207 (i+1)) + stT207 82 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 81
    simpa using h
  have hprev := st207_p81
  have hstep := st207_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p83 : ((2134638101977/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT207 (i+1))
      = (∑ i ∈ Finset.range 82, stT207 (i+1)) + stT207 83 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 82
    simpa using h
  have hprev := st207_p82
  have hstep := st207_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p84 : ((17581230486287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT207 (i+1))
      = (∑ i ∈ Finset.range 83, stT207 (i+1)) + stT207 84 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 83
    simpa using h
  have hprev := st207_p83
  have hstep := st207_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p85 : ((135370795441/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT207 (i+1))
      = (∑ i ∈ Finset.range 84, stT207 (i+1)) + stT207 85 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 84
    simpa using h
  have hprev := st207_p84
  have hstep := st207_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p86 : ((2150326220703/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT207 (i+1))
      = (∑ i ∈ Finset.range 85, stT207 (i+1)) + stT207 86 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 85
    simpa using h
  have hprev := st207_p85
  have hstep := st207_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p87 : ((551512762773/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT207 (i+1))
      = (∑ i ∈ Finset.range 86, stT207 (i+1)) + stT207 87 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 86
    simpa using h
  have hprev := st207_p86
  have hstep := st207_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p88 : ((1712468970457/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT207 (i+1))
      = (∑ i ∈ Finset.range 87, stT207 (i+1)) + stT207 88 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 87
    simpa using h
  have hprev := st207_p87
  have hstep := st207_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p89 : ((34831136502653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT207 (i+1))
      = (∑ i ∈ Finset.range 88, stT207 (i+1)) + stT207 89 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 88
    simpa using h
  have hprev := st207_p88
  have hstep := st207_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p90 : ((7017903317557/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT207 (i+1))
      = (∑ i ∈ Finset.range 89, stT207 (i+1)) + stT207 90 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 89
    simpa using h
  have hprev := st207_p89
  have hstep := st207_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p91 : ((853857254333/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT207 (i+1))
      = (∑ i ∈ Finset.range 90, stT207 (i+1)) + stT207 91 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 90
    simpa using h
  have hprev := st207_p90
  have hstep := st207_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p92 : ((21943883759/6250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT207 (i+1))
      = (∑ i ∈ Finset.range 91, stT207 (i+1)) + stT207 92 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 91
    simpa using h
  have hprev := st207_p91
  have hstep := st207_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p93 : ((87117459373/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT207 (i+1))
      = (∑ i ∈ Finset.range 92, stT207 (i+1)) + stT207 93 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 92
    simpa using h
  have hprev := st207_p92
  have hstep := st207_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p94 : ((3420557850717/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT207 (i+1))
      = (∑ i ∈ Finset.range 93, stT207 (i+1)) + stT207 94 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 93
    simpa using h
  have hprev := st207_p93
  have hstep := st207_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p95 : ((4403768992911/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT207 (i+1))
      = (∑ i ∈ Finset.range 94, stT207 (i+1)) + stT207 95 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 94
    simpa using h
  have hprev := st207_p94
  have hstep := st207_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p96 : ((8675160380259/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT207 (i+1))
      = (∑ i ∈ Finset.range 95, stT207 (i+1)) + stT207 96 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 95
    simpa using h
  have hprev := st207_p95
  have hstep := st207_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p97 : ((34257953275077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT207 (i+1))
      = (∑ i ∈ Finset.range 96, stT207 (i+1)) + stT207 97 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 96
    simpa using h
  have hprev := st207_p96
  have hstep := st207_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p98 : ((35262885819693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT207 (i+1))
      = (∑ i ∈ Finset.range 97, stT207 (i+1)) + stT207 98 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 97
    simpa using h
  have hprev := st207_p97
  have hstep := st207_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p99 : ((34669132485167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT207 (i+1))
      = (∑ i ∈ Finset.range 98, stT207 (i+1)) + stT207 99 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 98
    simpa using h
  have hprev := st207_p98
  have hstep := st207_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p100 : ((34252919485167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT207 (i+1))
      = (∑ i ∈ Finset.range 99, stT207 (i+1)) + stT207 100 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 99
    simpa using h
  have hprev := st207_p99
  have hstep := st207_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p101 : ((35246133577383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT207 (i+1))
      = (∑ i ∈ Finset.range 100, stT207 (i+1)) + stT207 101 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 100
    simpa using h
  have hprev := st207_p100
  have hstep := st207_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p102 : ((34746945512443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT207 (i+1))
      = (∑ i ∈ Finset.range 101, stT207 (i+1)) + stT207 102 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 101
    simpa using h
  have hprev := st207_p101
  have hstep := st207_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p103 : ((34195642538813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT207 (i+1))
      = (∑ i ∈ Finset.range 102, stT207 (i+1)) + stT207 103 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 102
    simpa using h
  have hprev := st207_p102
  have hstep := st207_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p104 : ((35162932738073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT207 (i+1))
      = (∑ i ∈ Finset.range 103, stT207 (i+1)) + stT207 104 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 103
    simpa using h
  have hprev := st207_p103
  have hstep := st207_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p105 : ((8731407918753/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT207 (i+1))
      = (∑ i ∈ Finset.range 104, stT207 (i+1)) + stT207 105 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 104
    simpa using h
  have hprev := st207_p104
  have hstep := st207_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p106 : ((17072352552147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT207 (i+1))
      = (∑ i ∈ Finset.range 105, stT207 (i+1)) + stT207 106 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 105
    simpa using h
  have hprev := st207_p105
  have hstep := st207_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p107 : ((17481598002819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT207 (i+1))
      = (∑ i ∈ Finset.range 106, stT207 (i+1)) + stT207 107 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 106
    simpa using h
  have hprev := st207_p106
  have hstep := st207_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p108 : ((17580097761819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT207 (i+1))
      = (∑ i ∈ Finset.range 107, stT207 (i+1)) + stT207 108 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 107
    simpa using h
  have hprev := st207_p107
  have hstep := st207_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p109 : ((34210503348349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT207 (i+1))
      = (∑ i ∈ Finset.range 108, stT207 (i+1)) + stT207 109 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 108
    simpa using h
  have hprev := st207_p108
  have hstep := st207_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p110 : ((34625552031183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT207 (i+1))
      = (∑ i ∈ Finset.range 109, stT207 (i+1)) + stT207 110 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 109
    simpa using h
  have hprev := st207_p109
  have hstep := st207_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p111 : ((2207379332339/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT207 (i+1))
      = (∑ i ∈ Finset.range 110, stT207 (i+1)) + stT207 111 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 110
    simpa using h
  have hprev := st207_p110
  have hstep := st207_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p112 : ((1078242565911/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT207 (i+1))
      = (∑ i ∈ Finset.range 111, stT207 (i+1)) + stT207 112 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 111
    simpa using h
  have hprev := st207_p111
  have hstep := st207_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p113 : ((34259239558901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT207 (i+1))
      = (∑ i ∈ Finset.range 112, stT207 (i+1)) + stT207 113 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 112
    simpa using h
  have hprev := st207_p112
  have hstep := st207_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p114 : ((17597865918493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT207 (i+1))
      = (∑ i ∈ Finset.range 113, stT207 (i+1)) + stT207 114 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 113
    simpa using h
  have hprev := st207_p113
  have hstep := st207_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p115 : ((17492828555293/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT207 (i+1))
      = (∑ i ∈ Finset.range 114, stT207 (i+1)) + stT207 115 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 114
    simpa using h
  have hprev := st207_p114
  have hstep := st207_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p116 : ((8537249300279/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT207 (i+1))
      = (∑ i ∈ Finset.range 115, stT207 (i+1)) + stT207 116 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 115
    simpa using h
  have hprev := st207_p115
  have hstep := st207_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p117 : ((4338981758077/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT207 (i+1))
      = (∑ i ∈ Finset.range 116, stT207 (i+1)) + stT207 117 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 116
    simpa using h
  have hprev := st207_p116
  have hstep := st207_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p118 : ((4415304707269/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT207 (i+1))
      = (∑ i ∈ Finset.range 117, stT207 (i+1)) + stT207 118 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 117
    simpa using h
  have hprev := st207_p117
  have hstep := st207_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p119 : ((17270251289071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT207 (i+1))
      = (∑ i ∈ Finset.range 118, stT207 (i+1)) + stT207 119 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 118
    simpa using h
  have hprev := st207_p118
  have hstep := st207_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p120 : ((17097641988907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT207 (i+1))
      = (∑ i ∈ Finset.range 119, stT207 (i+1)) + stT207 120 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 119
    simpa using h
  have hprev := st207_p119
  have hstep := st207_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p121 : ((17539059729307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT207 (i+1))
      = (∑ i ∈ Finset.range 120, stT207 (i+1)) + stT207 121 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 120
    simpa using h
  have hprev := st207_p120
  have hstep := st207_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p122 : ((35175473402181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT207 (i+1))
      = (∑ i ∈ Finset.range 121, stT207 (i+1)) + stT207 122 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 121
    simpa using h
  have hprev := st207_p121
  have hstep := st207_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p123 : ((34273815123891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT207 (i+1))
      = (∑ i ∈ Finset.range 122, stT207 (i+1)) + stT207 123 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 122
    simpa using h
  have hprev := st207_p122
  have hstep := st207_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p124 : ((34378190889819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT207 (i+1))
      = (∑ i ∈ Finset.range 123, stT207 (i+1)) + stT207 124 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 123
    simpa using h
  have hprev := st207_p123
  have hstep := st207_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p125 : ((4406652332827/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT207 (i+1))
      = (∑ i ∈ Finset.range 124, stT207 (i+1)) + stT207 125 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 124
    simpa using h
  have hprev := st207_p124
  have hstep := st207_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p126 : ((35000962302869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT207 (i+1))
      = (∑ i ∈ Finset.range 125, stT207 (i+1)) + stT207 126 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 125
    simpa using h
  have hprev := st207_p125
  have hstep := st207_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p127 : ((17084075125151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT207 (i+1))
      = (∑ i ∈ Finset.range 126, stT207 (i+1)) + stT207 127 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 126
    simpa using h
  have hprev := st207_p126
  have hstep := st207_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p128 : ((34516646755659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT207 (i+1))
      = (∑ i ∈ Finset.range 127, stT207 (i+1)) + stT207 128 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 127
    simpa using h
  have hprev := st207_p127
  have hstep := st207_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p129 : ((35311133139459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT207 (i+1))
      = (∑ i ∈ Finset.range 128, stT207 (i+1)) + stT207 129 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 128
    simpa using h
  have hprev := st207_p128
  have hstep := st207_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p130 : ((34911448582569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT207 (i+1))
      = (∑ i ∈ Finset.range 129, stT207 (i+1)) + stT207 130 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 129
    simpa using h
  have hprev := st207_p129
  have hstep := st207_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p131 : ((34139905908219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT207 (i+1))
      = (∑ i ∈ Finset.range 130, stT207 (i+1)) + stT207 131 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 130
    simpa using h
  have hprev := st207_p130
  have hstep := st207_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p132 : ((34550943159667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT207 (i+1))
      = (∑ i ∈ Finset.range 131, stT207 (i+1)) + stT207 132 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 131
    simpa using h
  have hprev := st207_p131
  have hstep := st207_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p133 : ((551854194713/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT207 (i+1))
      = (∑ i ∈ Finset.range 132, stT207 (i+1)) + stT207 133 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 132
    simpa using h
  have hprev := st207_p132
  have hstep := st207_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p134 : ((17466343304609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT207 (i+1))
      = (∑ i ∈ Finset.range 133, stT207 (i+1)) + stT207 134 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 133
    simpa using h
  have hprev := st207_p133
  have hstep := st207_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p135 : ((8537706048043/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT207 (i+1))
      = (∑ i ∈ Finset.range 134, stT207 (i+1)) + stT207 135 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 134
    simpa using h
  have hprev := st207_p134
  have hstep := st207_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p136 : ((4309426008307/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT207 (i+1))
      = (∑ i ∈ Finset.range 135, stT207 (i+1)) + stT207 136 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 135
    simpa using h
  have hprev := st207_p135
  have hstep := st207_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p137 : ((8820629781089/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT207 (i+1))
      = (∑ i ∈ Finset.range 136, stT207 (i+1)) + stT207 137 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 136
    simpa using h
  have hprev := st207_p136
  have hstep := st207_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p138 : ((35056553804963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT207 (i+1))
      = (∑ i ∈ Finset.range 137, stT207 (i+1)) + stT207 138 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 137
    simpa using h
  have hprev := st207_p137
  have hstep := st207_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p139 : ((34223976571697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT207 (i+1))
      = (∑ i ∈ Finset.range 138, stT207 (i+1)) + stT207 139 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 138
    simpa using h
  have hprev := st207_p138
  have hstep := st207_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p140 : ((34312938326891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT207 (i+1))
      = (∑ i ∈ Finset.range 139, stT207 (i+1)) + stT207 140 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 139
    simpa using h
  have hprev := st207_p139
  have hstep := st207_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p141 : ((35155020270509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT207 (i+1))
      = (∑ i ∈ Finset.range 140, stT207 (i+1)) + stT207 141 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 140
    simpa using h
  have hprev := st207_p140
  have hstep := st207_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p142 : ((35238651370607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT207 (i+1))
      = (∑ i ∈ Finset.range 141, stT207 (i+1)) + stT207 142 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 141
    simpa using h
  have hprev := st207_p141
  have hstep := st207_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p143 : ((34422163775239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT207 (i+1))
      = (∑ i ∈ Finset.range 142, stT207 (i+1)) + stT207 143 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 142
    simpa using h
  have hprev := st207_p142
  have hstep := st207_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p144 : ((34139253548911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT207 (i+1))
      = (∑ i ∈ Finset.range 143, stT207 (i+1)) + stT207 144 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 143
    simpa using h
  have hprev := st207_p143
  have hstep := st207_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p145 : ((34874058348553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT207 (i+1))
      = (∑ i ∈ Finset.range 144, stT207 (i+1)) + stT207 145 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 144
    simpa using h
  have hprev := st207_p144
  have hstep := st207_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p146 : ((35363388080853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT207 (i+1))
      = (∑ i ∈ Finset.range 145, stT207 (i+1)) + stT207 146 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 145
    simpa using h
  have hprev := st207_p145
  have hstep := st207_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p147 : ((34783127332317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT207 (i+1))
      = (∑ i ∈ Finset.range 146, stT207 (i+1)) + stT207 147 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 146
    simpa using h
  have hprev := st207_p146
  have hstep := st207_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p148 : ((34110699254537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT207 (i+1))
      = (∑ i ∈ Finset.range 147, stT207 (i+1)) + stT207 148 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 147
    simpa using h
  have hprev := st207_p147
  have hstep := st207_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p149 : ((34456665421223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT207 (i+1))
      = (∑ i ∈ Finset.range 148, stT207 (i+1)) + stT207 149 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 148
    simpa using h
  have hprev := st207_p148
  have hstep := st207_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p150 : ((35247768395623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT207 (i+1))
      = (∑ i ∈ Finset.range 149, stT207 (i+1)) + stT207 150 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 149
    simpa using h
  have hprev := st207_p149
  have hstep := st207_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p151 : ((35203410384811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT207 (i+1))
      = (∑ i ∈ Finset.range 150, stT207 (i+1)) + stT207 151 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 150
    simpa using h
  have hprev := st207_p150
  have hstep := st207_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p152 : ((34401365705603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT207 (i+1))
      = (∑ i ∈ Finset.range 151, stT207 (i+1)) + stT207 152 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 151
    simpa using h
  have hprev := st207_p151
  have hstep := st207_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p153 : ((6822794396489/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT207 (i+1))
      = (∑ i ∈ Finset.range 152, stT207 (i+1)) + stT207 153 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 152
    simpa using h
  have hprev := st207_p152
  have hstep := st207_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p154 : ((34785473124909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT207 (i+1))
      = (∑ i ∈ Finset.range 153, stT207 (i+1)) + stT207 154 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 153
    simpa using h
  have hprev := st207_p153
  have hstep := st207_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p155 : ((35370849493481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT207 (i+1))
      = (∑ i ∈ Finset.range 154, stT207 (i+1)) + stT207 155 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 154
    simpa using h
  have hprev := st207_p154
  have hstep := st207_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p156 : ((8744190896237/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT207 (i+1))
      = (∑ i ∈ Finset.range 155, stT207 (i+1)) + stT207 156 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 155
    simpa using h
  have hprev := st207_p155
  have hstep := st207_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p157 : ((17103401383501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT207 (i+1))
      = (∑ i ∈ Finset.range 156, stT207 (i+1)) + stT207 157 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 156
    simpa using h
  have hprev := st207_p156
  have hstep := st207_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p158 : ((34214681167973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT207 (i+1))
      = (∑ i ∈ Finset.range 157, stT207 (i+1)) + stT207 158 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 157
    simpa using h
  have hprev := st207_p157
  have hstep := st207_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p159 : ((34982080140327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT207 (i+1))
      = (∑ i ∈ Finset.range 158, stT207 (i+1)) + stT207 159 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 158
    simpa using h
  have hprev := st207_p158
  have hstep := st207_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p160 : ((35380217013279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT207 (i+1))
      = (∑ i ∈ Finset.range 159, stT207 (i+1)) + stT207 160 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 159
    simpa using h
  have hprev := st207_p159
  have hstep := st207_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p161 : ((2177259676867/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT207 (i+1))
      = (∑ i ∈ Finset.range 160, stT207 (i+1)) + stT207 161 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 160
    simpa using h
  have hprev := st207_p160
  have hstep := st207_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p162 : ((34136644021447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT207 (i+1))
      = (∑ i ∈ Finset.range 161, stT207 (i+1)) + stT207 162 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 161
    simpa using h
  have hprev := st207_p161
  have hstep := st207_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p163 : ((34273666742587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT207 (i+1))
      = (∑ i ∈ Finset.range 162, stT207 (i+1)) + stT207 163 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 162
    simpa using h
  have hprev := st207_p162
  have hstep := st207_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p164 : ((7009604616867/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT207 (i+1))
      = (∑ i ∈ Finset.range 163, stT207 (i+1)) + stT207 164 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 163
    simpa using h
  have hprev := st207_p163
  have hstep := st207_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p165 : ((35380486883219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT207 (i+1))
      = (∑ i ∈ Finset.range 164, stT207 (i+1)) + stT207 165 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 164
    simpa using h
  have hprev := st207_p164
  have hstep := st207_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p166 : ((34818578396051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT207 (i+1))
      = (∑ i ∈ Finset.range 165, stT207 (i+1)) + stT207 166 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 165
    simpa using h
  have hprev := st207_p165
  have hstep := st207_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p167 : ((34132852710803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT207 (i+1))
      = (∑ i ∈ Finset.range 166, stT207 (i+1)) + stT207 167 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 166
    simpa using h
  have hprev := st207_p166
  have hstep := st207_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p168 : ((1369831087727/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT207 (i+1))
      = (∑ i ∈ Finset.range 167, stT207 (i+1)) + stT207 168 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 167
    simpa using h
  have hprev := st207_p167
  have hstep := st207_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p169 : ((1400013519083/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT207 (i+1))
      = (∑ i ∈ Finset.range 168, stT207 (i+1)) + stT207 169 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 168
    simpa using h
  have hprev := st207_p168
  have hstep := st207_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p170 : ((35397846214707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT207 (i+1))
      = (∑ i ∈ Finset.range 169, stT207 (i+1)) + stT207 170 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 169
    simpa using h
  have hprev := st207_p169
  have hstep := st207_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p171 : ((34923425397507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT207 (i+1))
      = (∑ i ∈ Finset.range 170, stT207 (i+1)) + stT207 171 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 170
    simpa using h
  have hprev := st207_p170
  have hstep := st207_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p172 : ((34196170249009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT207 (i+1))
      = (∑ i ∈ Finset.range 171, stT207 (i+1)) + stT207 172 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 171
    simpa using h
  have hprev := st207_p171
  have hstep := st207_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p173 : ((34146424736029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT207 (i+1))
      = (∑ i ∈ Finset.range 172, stT207 (i+1)) + stT207 173 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 172
    simpa using h
  have hprev := st207_p172
  have hstep := st207_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p174 : ((34831260903407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT207 (i+1))
      = (∑ i ∈ Finset.range 173, stT207 (i+1)) + stT207 174 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 173
    simpa using h
  have hprev := st207_p173
  have hstep := st207_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p175 : ((35387860516871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT207 (i+1))
      = (∑ i ∈ Finset.range 174, stT207 (i+1)) + stT207 175 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 174
    simpa using h
  have hprev := st207_p174
  have hstep := st207_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p176 : ((4391009294177/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT207 (i+1))
      = (∑ i ∈ Finset.range 175, stT207 (i+1)) + stT207 176 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 175
    simpa using h
  have hprev := st207_p175
  have hstep := st207_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p177 : ((2148574439173/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT207 (i+1))
      = (∑ i ∈ Finset.range 176, stT207 (i+1)) + stT207 177 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 176
    simpa using h
  have hprev := st207_p176
  have hstep := st207_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p178 : ((8512653671911/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT207 (i+1))
      = (∑ i ∈ Finset.range 177, stT207 (i+1)) + stT207 178 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 177
    simpa using h
  have hprev := st207_p177
  have hstep := st207_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p179 : ((34537161238069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT207 (i+1))
      = (∑ i ∈ Finset.range 178, stT207 (i+1)) + stT207 179 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 178
    simpa using h
  have hprev := st207_p178
  have hstep := st207_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p180 : ((17625538209407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT207 (i+1))
      = (∑ i ∈ Finset.range 179, stT207 (i+1)) + stT207 180 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 179
    simpa using h
  have hprev := st207_p179
  have hstep := st207_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p181 : ((17674680348923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT207 (i+1))
      = (∑ i ∈ Finset.range 180, stT207 (i+1)) + stT207 181 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 180
    simpa using h
  have hprev := st207_p180
  have hstep := st207_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p182 : ((8680617501649/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT207 (i+1))
      = (∑ i ∈ Finset.range 181, stT207 (i+1)) + stT207 182 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 181
    simpa using h
  have hprev := st207_p181
  have hstep := st207_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p183 : ((17050296423049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT207 (i+1))
      = (∑ i ∈ Finset.range 182, stT207 (i+1)) + stT207 183 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 182
    simpa using h
  have hprev := st207_p182
  have hstep := st207_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p184 : ((3419506470503/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT207 (i+1))
      = (∑ i ∈ Finset.range 183, stT207 (i+1)) + stT207 184 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 183
    simpa using h
  have hprev := st207_p183
  have hstep := st207_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p185 : ((17446426685787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT207 (i+1))
      = (∑ i ∈ Finset.range 184, stT207 (i+1)) + stT207 185 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 184
    simpa using h
  have hprev := st207_p184
  have hstep := st207_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p186 : ((4425746219763/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT207 (i+1))
      = (∑ i ∈ Finset.range 185, stT207 (i+1)) + stT207 186 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 185
    simpa using h
  have hprev := st207_p185
  have hstep := st207_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p187 : ((17582843306609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT207 (i+1))
      = (∑ i ∈ Finset.range 186, stT207 (i+1)) + stT207 187 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 186
    simpa using h
  have hprev := st207_p186
  have hstep := st207_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p188 : ((17221337325209/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT207 (i+1))
      = (∑ i ∈ Finset.range 187, stT207 (i+1)) + stT207 188 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 187
    simpa using h
  have hprev := st207_p187
  have hstep := st207_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p189 : ((6805821471789/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT207 (i+1))
      = (∑ i ∈ Finset.range 188, stT207 (i+1)) + stT207 189 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 188
    simpa using h
  have hprev := st207_p188
  have hstep := st207_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p190 : ((34368989963041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT207 (i+1))
      = (∑ i ∈ Finset.range 189, stT207 (i+1)) + stT207 190 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 189
    simpa using h
  have hprev := st207_p189
  have hstep := st207_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p191 : ((35092523442897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT207 (i+1))
      = (∑ i ∈ Finset.range 190, stT207 (i+1)) + stT207 191 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 190
    simpa using h
  have hprev := st207_p190
  have hstep := st207_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p192 : ((17714915282383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT207 (i+1))
      = (∑ i ∈ Finset.range 191, stT207 (i+1)) + stT207 192 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 191
    simpa using h
  have hprev := st207_p191
  have hstep := st207_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p193 : ((17514977390683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT207 (i+1))
      = (∑ i ∈ Finset.range 192, stT207 (i+1)) + stT207 193 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 192
    simpa using h
  have hprev := st207_p192
  have hstep := st207_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p194 : ((17157366320537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT207 (i+1))
      = (∑ i ∈ Finset.range 193, stT207 (i+1)) + stT207 194 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 193
    simpa using h
  have hprev := st207_p193
  have hstep := st207_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p195 : ((34023601100629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT207 (i+1))
      = (∑ i ∈ Finset.range 194, stT207 (i+1)) + stT207 195 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 194
    simpa using h
  have hprev := st207_p194
  have hstep := st207_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p196 : ((17225127836987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT207 (i+1))
      = (∑ i ∈ Finset.range 195, stT207 (i+1)) + stT207 196 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 195
    simpa using h
  have hprev := st207_p195
  have hstep := st207_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p197 : ((17578659725807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT207 (i+1))
      = (∑ i ∈ Finset.range 196, stT207 (i+1)) + stT207 197 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 196
    simpa using h
  have hprev := st207_p196
  have hstep := st207_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p198 : ((1771696088789/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT207 (i+1))
      = (∑ i ∈ Finset.range 197, stT207 (i+1)) + stT207 198 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 197
    simpa using h
  have hprev := st207_p197
  have hstep := st207_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p199 : ((17504422823327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT207 (i+1))
      = (∑ i ∈ Finset.range 198, stT207 (i+1)) + stT207 199 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 198
    simpa using h
  have hprev := st207_p198
  have hstep := st207_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p200 : ((8576490018861/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT207 (i+1))
      = (∑ i ∈ Finset.range 199, stT207 (i+1)) + stT207 200 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 199
    simpa using h
  have hprev := st207_p199
  have hstep := st207_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p201 : ((3401279782281/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT207 (i+1))
      = (∑ i ∈ Finset.range 200, stT207 (i+1)) + stT207 201 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 200
    simpa using h
  have hprev := st207_p200
  have hstep := st207_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p202 : ((537645115579/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT207 (i+1))
      = (∑ i ∈ Finset.range 201, stT207 (i+1)) + stT207 202 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 201
    simpa using h
  have hprev := st207_p201
  have hstep := st207_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p203 : ((8777558191321/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT207 (i+1))
      = (∑ i ∈ Finset.range 202, stT207 (i+1)) + stT207 203 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 202
    simpa using h
  have hprev := st207_p202
  have hstep := st207_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p204 : ((8861997875881/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT207 (i+1))
      = (∑ i ∈ Finset.range 203, stT207 (i+1)) + stT207 204 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 203
    simpa using h
  have hprev := st207_p203
  have hstep := st207_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p205 : ((35107752937167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT207 (i+1))
      = (∑ i ∈ Finset.range 204, stT207 (i+1)) + stT207 205 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 204
    simpa using h
  have hprev := st207_p204
  have hstep := st207_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p206 : ((6882405422253/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT207 (i+1))
      = (∑ i ∈ Finset.range 205, stT207 (i+1)) + stT207 206 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 205
    simpa using h
  have hprev := st207_p205
  have hstep := st207_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p207 : ((34006388174277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT207 (i+1))
      = (∑ i ∈ Finset.range 206, stT207 (i+1)) + stT207 207 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 206
    simpa using h
  have hprev := st207_p206
  have hstep := st207_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p208 : ((8564996653413/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT207 (i+1))
      = (∑ i ∈ Finset.range 207, stT207 (i+1)) + stT207 208 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 207
    simpa using h
  have hprev := st207_p207
  have hstep := st207_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p209 : ((8734348300319/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT207 (i+1))
      = (∑ i ∈ Finset.range 208, stT207 (i+1)) + stT207 209 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 208
    simpa using h
  have hprev := st207_p208
  have hstep := st207_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p210 : ((35425708727681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT207 (i+1))
      = (∑ i ∈ Finset.range 209, stT207 (i+1)) + stT207 210 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 209
    simpa using h
  have hprev := st207_p209
  have hstep := st207_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p211 : ((35290824833711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT207 (i+1))
      = (∑ i ∈ Finset.range 210, stT207 (i+1)) + stT207 211 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 210
    simpa using h
  have hprev := st207_p210
  have hstep := st207_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p212 : ((17328427077243/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT207 (i+1))
      = (∑ i ∈ Finset.range 211, stT207 (i+1)) + stT207 212 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 211
    simpa using h
  have hprev := st207_p211
  have hstep := st207_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p213 : ((34083383165369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT207 (i+1))
      = (∑ i ∈ Finset.range 212, stT207 (i+1)) + stT207 213 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 212
    simpa using h
  have hprev := st207_p212
  have hstep := st207_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p214 : ((34068288902903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT207 (i+1))
      = (∑ i ∈ Finset.range 213, stT207 (i+1)) + stT207 214 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 213
    simpa using h
  have hprev := st207_p213
  have hstep := st207_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p215 : ((34620208915259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT207 (i+1))
      = (∑ i ∈ Finset.range 214, stT207 (i+1)) + stT207 215 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 214
    simpa using h
  have hprev := st207_p214
  have hstep := st207_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p216 : ((7052652359651/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT207 (i+1))
      = (∑ i ∈ Finset.range 215, stT207 (i+1)) + stT207 216 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 215
    simpa using h
  have hprev := st207_p215
  have hstep := st207_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p217 : ((35452080220323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT207 (i+1))
      = (∑ i ∈ Finset.range 216, stT207 (i+1)) + stT207 217 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 216
    simpa using h
  have hprev := st207_p216
  have hstep := st207_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p218 : ((35031563502213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT207 (i+1))
      = (∑ i ∈ Finset.range 217, stT207 (i+1)) + stT207 218 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 217
    simpa using h
  have hprev := st207_p217
  have hstep := st207_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p219 : ((34356518809401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT207 (i+1))
      = (∑ i ∈ Finset.range 218, stT207 (i+1)) + stT207 219 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 218
    simpa using h
  have hprev := st207_p218
  have hstep := st207_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p220 : ((33986242101601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT207 (i+1))
      = (∑ i ∈ Finset.range 219, stT207 (i+1)) + stT207 220 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 219
    simpa using h
  have hprev := st207_p219
  have hstep := st207_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p221 : ((273772433621/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT207 (i+1))
      = (∑ i ∈ Finset.range 220, stT207 (i+1)) + stT207 221 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 220
    simpa using h
  have hprev := st207_p220
  have hstep := st207_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p222 : ((34866752573169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT207 (i+1))
      = (∑ i ∈ Finset.range 221, stT207 (i+1)) + stT207 222 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 221
    simpa using h
  have hprev := st207_p221
  have hstep := st207_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p223 : ((35399209243241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT207 (i+1))
      = (∑ i ∈ Finset.range 222, stT207 (i+1)) + stT207 223 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 222
    simpa using h
  have hprev := st207_p222
  have hstep := st207_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p224 : ((1415783184167/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT207 (i+1))
      = (∑ i ∈ Finset.range 223, stT207 (i+1)) + stT207 224 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 223
    simpa using h
  have hprev := st207_p223
  have hstep := st207_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p225 : ((34860555337163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT207 (i+1))
      = (∑ i ∈ Finset.range 224, stT207 (i+1)) + stT207 225 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 224
    simpa using h
  have hprev := st207_p224
  have hstep := st207_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p226 : ((8555130964089/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT207 (i+1))
      = (∑ i ∈ Finset.range 225, stT207 (i+1)) + stT207 226 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 225
    simpa using h
  have hprev := st207_p225
  have hstep := st207_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p227 : ((8493454411389/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT207 (i+1))
      = (∑ i ∈ Finset.range 226, stT207 (i+1)) + stT207 227 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 226
    simpa using h
  have hprev := st207_p226
  have hstep := st207_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p228 : ((2144254369901/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT207 (i+1))
      = (∑ i ∈ Finset.range 227, stT207 (i+1)) + stT207 228 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 227
    simpa using h
  have hprev := st207_p227
  have hstep := st207_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p229 : ((8740693177161/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT207 (i+1))
      = (∑ i ∈ Finset.range 228, stT207 (i+1)) + stT207 229 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 228
    simpa using h
  have hprev := st207_p228
  have hstep := st207_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p230 : ((8859465977801/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT207 (i+1))
      = (∑ i ∈ Finset.range 229, stT207 (i+1)) + stT207 230 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 229
    simpa using h
  have hprev := st207_p229
  have hstep := st207_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p231 : ((8844111023001/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT207 (i+1))
      = (∑ i ∈ Finset.range 230, stT207 (i+1)) + stT207 231 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 230
    simpa using h
  have hprev := st207_p230
  have hstep := st207_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p232 : ((6965680240131/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT207 (i+1))
      = (∑ i ∈ Finset.range 231, stT207 (i+1)) + stT207 232 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 231
    simpa using h
  have hprev := st207_p231
  have hstep := st207_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p233 : ((34203901568301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT207 (i+1))
      = (∑ i ∈ Finset.range 232, stT207 (i+1)) + stT207 233 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 232
    simpa using h
  have hprev := st207_p232
  have hstep := st207_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p234 : ((2122694986311/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT207 (i+1))
      = (∑ i ∈ Finset.range 233, stT207 (i+1)) + stT207 234 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 233
    simpa using h
  have hprev := st207_p233
  have hstep := st207_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p235 : ((856975452381/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT207 (i+1))
      = (∑ i ∈ Finset.range 234, stT207 (i+1)) + stT207 235 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 234
    simpa using h
  have hprev := st207_p234
  have hstep := st207_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p236 : ((4364834178049/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT207 (i+1))
      = (∑ i ∈ Finset.range 235, stT207 (i+1)) + stT207 236 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 235
    simpa using h
  have hprev := st207_p235
  have hstep := st207_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p237 : ((7084004364253/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT207 (i+1))
      = (∑ i ∈ Finset.range 236, stT207 (i+1)) + stT207 237 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 236
    simpa using h
  have hprev := st207_p236
  have hstep := st207_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p238 : ((4428325054189/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT207 (i+1))
      = (∑ i ∈ Finset.range 237, stT207 (i+1)) + stT207 238 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 237
    simpa using h
  have hprev := st207_p237
  have hstep := st207_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p239 : ((17468659447121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT207 (i+1))
      = (∑ i ∈ Finset.range 238, stT207 (i+1)) + stT207 239 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 238
    simpa using h
  have hprev := st207_p238
  have hstep := st207_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p240 : ((8574789244753/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT207 (i+1))
      = (∑ i ∈ Finset.range 239, stT207 (i+1)) + stT207 240 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 239
    simpa using h
  have hprev := st207_p239
  have hstep := st207_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p241 : ((530587285753/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT207 (i+1))
      = (∑ i ∈ Finset.range 240, stT207 (i+1)) + stT207 241 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 240
    simpa using h
  have hprev := st207_p240
  have hstep := st207_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p242 : ((1067077383239/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT207 (i+1))
      = (∑ i ∈ Finset.range 241, stT207 (i+1)) + stT207 242 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 241
    simpa using h
  have hprev := st207_p241
  have hstep := st207_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p243 : ((4341560012331/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT207 (i+1))
      = (∑ i ∈ Finset.range 242, stT207 (i+1)) + stT207 243 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 242
    simpa using h
  have hprev := st207_p242
  have hstep := st207_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p244 : ((882850709143/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT207 (i+1))
      = (∑ i ∈ Finset.range 243, stT207 (i+1)) + stT207 244 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 243
    simpa using h
  have hprev := st207_p243
  have hstep := st207_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p245 : ((8874624195771/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT207 (i+1))
      = (∑ i ∈ Finset.range 244, stT207 (i+1)) + stT207 245 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 244
    simpa using h
  have hprev := st207_p244
  have hstep := st207_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p246 : ((7033018111041/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT207 (i+1))
      = (∑ i ∈ Finset.range 245, stT207 (i+1)) + stT207 246 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 245
    simpa using h
  have hprev := st207_p245
  have hstep := st207_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p247 : ((3453914709531/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT207 (i+1))
      = (∑ i ∈ Finset.range 246, stT207 (i+1)) + stT207 247 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 246
    simpa using h
  have hprev := st207_p246
  have hstep := st207_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p248 : ((6807148105509/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT207 (i+1))
      = (∑ i ∈ Finset.range 247, stT207 (i+1)) + stT207 248 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 247
    simpa using h
  have hprev := st207_p247
  have hstep := st207_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p249 : ((3398363629177/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT207 (i+1))
      = (∑ i ∈ Finset.range 248, stT207 (i+1)) + stT207 249 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 248
    simpa using h
  have hprev := st207_p248
  have hstep := st207_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_p250 : ((6882702558599/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT207 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT207 (i+1))
      = (∑ i ∈ Finset.range 249, stT207 (i+1)) + stT207 250 := by
    have h := Finset.sum_range_succ (fun i => stT207 (i+1)) 249
    simpa using h
  have hprev := st207_p249
  have hstep := st207_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st207_s250 :
    |Real.sin (((207 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((28259/125000 : ℚ) : ℝ))
      - ((-91681/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -2058453/10000000) (δ := 1301/125000000) (ψ := 28259/125000) 207 182
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 207`** (evaluated boundary). -/
theorem station_207_sign : 0 < hardyG ((((207:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 207 250 (by norm_num) (by norm_num)
    ((28259/125000 : ℚ) : ℝ)
  have hchain := st207_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT207 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((207 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((28259/125000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st207_c250
  have hsinb := abs_le.mp st207_s250
  have hbdy_lo : ((38320066067707/685588000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((207 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((28259/125000 : ℚ) : ℝ))) / 2
          - ((((207:ℕ)):ℝ))
            * Real.sin (((207 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((28259/125000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((207:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((207:ℝ) * Real.log (250:ℝ) - ((28259/125000 : ℚ) : ℝ))) / 2
        - ((207:ℝ)) * Real.sin ((207:ℝ) * Real.log (250:ℝ) - ((28259/125000 : ℚ) : ℝ))
        ≥ ((302946977/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((207:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((302946977/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((302946977/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((302946977/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((207:ℕ)):ℝ))+1) * (((((207:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((55874562491/58593750000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((6882702558599/2000000000000 : ℚ) : ℝ) + ((38320066067707/685588000000000 : ℚ) : ℝ)
      - ((55874562491/58593750000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((28259/125000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((207:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((28259/125000 : ℚ) : ℝ)
        * (riemannZeta (line ((((207:ℕ)):ℝ)))).re
      - Real.sin ((28259/125000 : ℚ) : ℝ)
        * (riemannZeta (line ((((207:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((207:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((207:ℕ)):ℝ))
      = (((((207:ℕ)):ℝ)) * (Real.log ((((207:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((207:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_207
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
  have hθwin : |(((28259/125000 : ℚ) : ℝ) + ((41:ℤ)) * (2*Real.pi)) - theta ((((207:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((207:ℕ)):ℝ)))
    (φ := ((28259/125000 : ℚ) : ℝ) + ((41:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((28259/125000 : ℚ)) : ℝ) 41).1,
    (cos_sin_shift (((28259/125000 : ℚ)) : ℝ) 41).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_207_sign
end AxiomAudit
