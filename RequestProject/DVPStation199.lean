import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 199` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT199 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((199 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-221723/200000 : ℚ) : ℝ))

theorem st199_c1 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((222951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2771537/10000000) (δ := 201/1000000000) (ψ := -221723/200000) 199 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t1 : ((111463/250000 : ℚ) : ℝ) ≤ stT199 1 := by
  have hc : ((111463/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111463/250000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((111463/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c2 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((342999/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2037053/10000000) (δ := 10059/1000000000) (ψ := -221723/200000) 199 22
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t2 : ((1212596066629/2500000000000 : ℚ) : ℝ) ≤ stT199 2 := by
  have hc : ((171487/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1212596066629/2500000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((171487/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c3 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((61501/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -447583/10000000) (δ := 203/20000000) (ψ := -221723/200000) 199 35
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t3 : ((1420232417233/2500000000000 : ℚ) : ℝ) ≤ stT199 3 := by
  have hc : ((491983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1420232417233/2500000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((491983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c4 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((867303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1302593/10000000) (δ := 10017/1000000000) (ψ := -221723/200000) 199 44
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t4 : ((867253/2000000 : ℚ) : ℝ) ≤ stT199 4 := by
  have hc : ((867253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((867253/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((867253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c5 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((586297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2360791/10000000) (δ := 623/62500000) (ψ := -221723/200000) 199 51
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t5 : ((524355145469/2000000000000 : ℚ) : ℝ) ≤ stT199 5 := by
  have hc : ((586247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((524355145469/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((586247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c6 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((890289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -591021/5000000) (δ := 10111/1000000000) (ψ := -221723/200000) 199 57
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t6 : ((1817192346599/5000000000000 : ℚ) : ℝ) ≤ stT199 6 := by
  have hc : ((890239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1817192346599/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((890239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c7 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((350441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -606377/2000000) (δ := 10147/1000000000) (ψ := -221723/200000) 199 62
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t7 : ((331088310201/2500000000000 : ℚ) : ℝ) ≤ stT199 7 := by
  have hc : ((350391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((331088310201/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((350391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c8 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((974289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 568133/10000000) (δ := 399/40000000) (ψ := -221723/200000) 199 66
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t8 : ((3444454134387/10000000000000 : ℚ) : ℝ) ≤ stT199 8 := by
  have hc : ((974239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3444454134387/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((974239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c9 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((103937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1833339/5000000) (δ := 10099/1000000000) (ψ := -221723/200000) 199 70
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t9 : ((346289965371/10000000000000 : ℚ) : ℝ) ≤ stT199 9 := by
  have hc : ((103887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((346289965371/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((103887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c10 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((397887/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1626281/10000000) (δ := 10077/1000000000) (ψ := -221723/200000) 199 73
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t10 : ((629074925887/2500000000000 : ℚ) : ℝ) ≤ stT199 10 := by
  have hc : ((198931/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((629074925887/2500000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((198931/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c11 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((719519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119951/625000) (δ := 2489/250000000) (ψ := -221723/200000) 199 76
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t11 : ((2169280334997/10000000000000 : ℚ) : ℝ) ≤ stT199 11 := by
  have hc : ((719469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2169280334997/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((719469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c12 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((720273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -958251/5000000) (δ := 10069/1000000000) (ψ := -221723/200000) 199 79
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t12 : ((2079104465473/10000000000000 : ℚ) : ℝ) ≤ stT199 12 := by
  have hc : ((720223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2079104465473/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((720223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c13 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-427287/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3244407/5000000) (δ := 253/25000000) (ψ := -221723/200000) 199 81
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t13 : ((-74071891207/312500000000 : ℚ) : ℝ) ≤ stT199 13 := by
  have hc : ((-26707/31250 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74071891207/312500000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-26707/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c14 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((32107/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -753269/2000000) (δ := 2021/200000000) (ψ := -221723/200000) 199 84
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t14 : ((10717842273/625000000000 : ℚ) : ℝ) ≤ stT199 14 := by
  have hc : ((16041/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10717842273/625000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((16041/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c15 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((470821/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13411/156250) (δ := 10019/1000000000) (ψ := -221723/200000) 199 86
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t15 : ((75974351403/312500000000 : ℚ) : ℝ) ≤ stT199 15 := by
  have hc : ((117699/125000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75974351403/312500000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((117699/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c16 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((249447/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -166327/10000000) (δ := 997/100000000) (ψ := -221723/200000) 199 88
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t16 : ((498869/2000000 : ℚ) : ℝ) ≤ stT199 16 := by
  have hc : ((498869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((498869/2000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((498869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c17 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((210663/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -284303/2000000) (δ := 1991/200000000) (ψ := -221723/200000) 199 90
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t17 : ((255451227039/1250000000000 : ℚ) : ℝ) ≤ stT199 17 := by
  have hc : ((421301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((255451227039/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((421301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c18 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-47131/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2200569/5000000) (δ := 10141/1000000000) (ψ := -221723/200000) 199 92
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t18 : ((-222236627601/5000000000000 : ℚ) : ℝ) ≤ stT199 18 := by
  have hc : ((-94287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222236627601/5000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-94287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c19 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-227671/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6789331/10000000) (δ := 5017/500000000) (ψ := -221723/200000) 199 93
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t19 : ((-522341922993/2500000000000 : ℚ) : ℝ) ≤ stT199 19 := by
  have hc : ((-455367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-522341922993/2500000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-455367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c20 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((234261/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 891821/10000000) (δ := 10119/1000000000) (ψ := -221723/200000) 199 95
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t20 : ((1047590681299/5000000000000 : ℚ) : ℝ) ≤ stT199 20 := by
  have hc : ((468497/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1047590681299/5000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((468497/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c21 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-400689/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6250981/10000000) (δ := 2021/200000000) (ψ := -221723/200000) 199 97
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t21 : ((-437214837903/2500000000000 : ℚ) : ℝ) ≤ stT199 21 := by
  have hc : ((-200357/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-437214837903/2500000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-200357/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c22 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((444897/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 296189/2500000) (δ := 4999/500000000) (ψ := -221723/200000) 199 98
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t22 : ((118558777263/625000000000 : ℚ) : ℝ) ≤ stT199 22 := by
  have hc : ((55609/62500 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118558777263/625000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((55609/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c23 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-15539/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7591563/10000000) (δ := 10091/1000000000) (ψ := -221723/200000) 199 99
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t23 : ((-207377261917/1000000000000 : ℚ) : ℝ) ≤ stT199 23 := by
  have hc : ((-497273/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207377261917/1000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-497273/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c24 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((61067/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1325481/5000000) (δ := 10027/1000000000) (ψ := -221723/200000) 199 101
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t24 : ((498558825563/5000000000000 : ℚ) : ℝ) ≤ stT199 24 := by
  have hc : ((244243/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((498558825563/5000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((244243/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c25 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((177727/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97501/500000) (δ := 5067/500000000) (ψ := -221723/200000) 199 102
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t25 : ((355429/2500000 : ℚ) : ℝ) ≤ stT199 25 := by
  have hc : ((355429/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((355429/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((355429/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c26 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-333787/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1150871/2000000) (δ := 10141/1000000000) (ψ := -221723/200000) 199 103
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t26 : ((-81832426193/625000000000 : ℚ) : ℝ) ≤ stT199 26 := by
  have hc : ((-83453/125000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81832426193/625000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-83453/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c27 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-462969/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6885773/10000000) (δ := 157/15625000) (ψ := -221723/200000) 199 105
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t27 : ((-445516207997/2500000000000 : ℚ) : ℝ) ≤ stT199 27 := by
  have hc : ((-231497/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-445516207997/2500000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-231497/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c28 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-56879/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -900161/2000000) (δ := 10063/1000000000) (ψ := -221723/200000) 199 106
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t28 : ((-215029730409/5000000000000 : ℚ) : ℝ) ≤ stT199 28 := by
  have hc : ((-113783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215029730409/5000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-113783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c29 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((226647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2750847/10000000) (δ := 10033/1000000000) (ψ := -221723/200000) 199 107
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t29 : ((210413201383/2500000000000 : ℚ) : ℝ) ≤ stT199 29 := by
  have hc : ((113311/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210413201383/2500000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((113311/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c30 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((803809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -796407/5000000) (δ := 5013/500000000) (ψ := -221723/200000) 199 108
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t30 : ((1467455760419/10000000000000 : ℚ) : ℝ) ≤ stT199 30 := by
  have hc : ((803759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1467455760419/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((803759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c31 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((18459/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -493901/5000000) (δ := 10019/1000000000) (ψ := -221723/200000) 199 109
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t31 : ((16575773137/100000000000 : ℚ) : ℝ) ≤ stT199 31 := by
  have hc : ((9229/10000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16575773137/100000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((9229/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c32 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((467893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -900787/10000000) (δ := 2503/250000000) (ψ := -221723/200000) 199 110
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t32 : ((103385142861/625000000000 : ℚ) : ℝ) ≤ stT199 32 := by
  have hc : ((116967/125000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103385142861/625000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((116967/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c33 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((867843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1299879/10000000) (δ := 4999/500000000) (ψ := -221723/200000) 199 111
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t33 : ((188829153421/1250000000000 : ℚ) : ℝ) ≤ stT199 33 := by
  have hc : ((867793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188829153421/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((867793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c34 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((10166/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -86239/400000) (δ := 9997/1000000000) (ψ := -221723/200000) 199 112
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t34 : ((111572465139/1000000000000 : ℚ) : ℝ) ≤ stT199 34 := by
  have hc : ((325287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111572465139/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((325287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c35 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((48131/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3442657/10000000) (δ := 999/100000000) (ψ := -221723/200000) 199 113
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t35 : ((40667542749/1250000000000 : ℚ) : ℝ) ≤ stT199 35 := by
  have hc : ((96237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40667542749/1250000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((96237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c36 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-46483/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5135597/10000000) (δ := 253/25000000) (ψ := -221723/200000) 199 114
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t36 : ((-9685001937/125000000000 : ℚ) : ℝ) ≤ stT199 36 := by
  have hc : ((-5811/12500 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9685001937/125000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-5811/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c37 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-483633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3606279/5000000) (δ := 10027/1000000000) (ψ := -221723/200000) 199 115
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t37 : ((-39756445771/250000000000 : ℚ) : ℝ) ≤ stT199 37 := by
  have hc : ((-241829/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39756445771/250000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-241829/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c38 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-18801/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6054871/10000000) (δ := 2519/250000000) (ψ := -221723/200000) 199 115
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t38 : ((-24401033587/200000000000 : ℚ) : ℝ) ≤ stT199 38 := by
  have hc : ((-75209/100000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24401033587/200000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-75209/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c39 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((25989/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3269719/10000000) (δ := 10069/1000000000) (ψ := -221723/200000) 199 116
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t39 : ((325060043/7812500000 : ℚ) : ℝ) ≤ stT199 39 := by
  have hc : ((812/3125 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((325060043/7812500000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((812/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c40 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((49901/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 78681/5000000) (δ := 5071/500000000) (ψ := -221723/200000) 199 117
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t40 : ((78896414493/500000000000 : ℚ) : ℝ) ≤ stT199 40 := by
  have hc : ((99797/100000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78896414493/500000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((99797/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c41 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((130657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3266033/10000000) (δ := 10049/1000000000) (ψ := -221723/200000) 199 118
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t41 : ((25501603473/625000000000 : ℚ) : ℝ) ≤ stT199 41 := by
  have hc : ((16329/62500 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25501603473/625000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((16329/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c42 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-29383/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6985441/10000000) (δ := 10147/1000000000) (ψ := -221723/200000) 199 119
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t42 : ((-362731032101/2500000000000 : ℚ) : ℝ) ≤ stT199 42 := by
  have hc : ((-470153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-362731032101/2500000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-470153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c43 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-62457/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4720983/10000000) (δ := 10047/1000000000) (ψ := -221723/200000) 199 119
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t43 : ((-47630650231/1000000000000 : ℚ) : ℝ) ≤ stT199 43 := by
  have hc : ((-62467/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47630650231/1000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-62467/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c44 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((491911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56287/1250000) (δ := 251/25000000) (ψ := -221723/200000) 199 120
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t44 : ((92693211327/625000000000 : ℚ) : ℝ) ≤ stT199 44 := by
  have hc : ((245943/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92693211327/625000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((245943/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c45 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-60147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4077449/10000000) (δ := 997/100000000) (ψ := -221723/200000) 199 121
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t45 : ((-11217048783/1250000000000 : ℚ) : ℝ) ≤ stT199 45 := by
  have hc : ((-60197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11217048783/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-60197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c46 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-921539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3428527/5000000) (δ := 1007/100000000) (ψ := -221723/200000) 199 121
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t46 : ((-67940462669/500000000000 : ℚ) : ℝ) ≤ stT199 46 := by
  have hc : ((-921589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67940462669/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-921589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c47 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((2309/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73939/400000) (δ := 10077/1000000000) (ψ := -221723/200000) 199 122
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t47 : ((107769364067/1000000000000 : ℚ) : ℝ) ≤ stT199 47 := by
  have hc : ((73883/100000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107769364067/1000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((73883/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c48 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((214937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1692711/5000000) (δ := 1997/200000000) (ψ := -221723/200000) 199 123
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t48 : ((2481300189/80000000000 : ℚ) : ℝ) ≤ stT199 48 := by
  have hc : ((214887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2481300189/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((214887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c49 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-46197/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 687263/1000000) (δ := 1997/200000000) (ψ := -221723/200000) 199 123
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t49 : ((-32999656057/250000000000 : ℚ) : ℝ) ≤ stT199 49 := by
  have hc : ((-92399/100000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32999656057/250000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-92399/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c50 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((110513/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30389/250000) (δ := 2523/250000000) (ψ := -221723/200000) 199 124
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t50 : ((625120329751/5000000000000 : ℚ) : ℝ) ≤ stT199 50 := by
  have hc : ((442027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((625120329751/5000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((442027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c51 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-281587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -464061/1000000) (δ := 9999/1000000000) (ψ := -221723/200000) 199 125
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t51 : ((-394370939997/10000000000000 : ℚ) : ℝ) ≤ stT199 51 := by
  have hc : ((-281637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-394370939997/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-281637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c52 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-42337/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1003979/2000000) (δ := 10099/1000000000) (ψ := -221723/200000) 199 125
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t52 : ((-29358905421/500000000000 : ℚ) : ℝ) ≤ stT199 52 := by
  have hc : ((-21171/50000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29358905421/500000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-21171/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c53 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((176969/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1211589/10000000) (δ := 5003/500000000) (ψ := -221723/200000) 199 126
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t53 : ((48614353439/400000000000 : ℚ) : ℝ) ≤ stT199 53 := by
  have hc : ((176959/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48614353439/400000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((176959/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c54 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-62227/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7620233/10000000) (δ := 1009/100000000) (ψ := -221723/200000) 199 127
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t54 : ((-169368993087/1250000000000 : ℚ) : ℝ) ≤ stT199 54 := by
  have hc : ((-497841/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169368993087/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-497841/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c55 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((12866/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 301689/2000000) (δ := 10113/1000000000) (ψ := -221723/200000) 199 127
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t55 : ((555118339113/5000000000000 : ℚ) : ℝ) ≤ stT199 55 := by
  have hc : ((411687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((555118339113/5000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((411687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c56 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-499767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1047063/2000000) (δ := 9983/1000000000) (ψ := -221723/200000) 199 128
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t56 : ((-667908955819/10000000000000 : ℚ) : ℝ) ≤ stT199 56 := by
  have hc : ((-499817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-667908955819/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-499817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c57 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((71109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 892559/2500000) (δ := 9983/1000000000) (ψ := -221723/200000) 199 128
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t57 : ((5884564543/312500000000 : ℚ) : ℝ) ≤ stT199 57 := by
  have hc : ((17771/125000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5884564543/312500000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((17771/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c58 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((43939/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3485307/10000000) (δ := 403/40000000) (ψ := -221723/200000) 199 129
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t58 : ((14419576449/625000000000 : ℚ) : ℝ) ≤ stT199 58 := by
  have hc : ((87853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14419576449/625000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((87853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c59 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-211551/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5019157/10000000) (δ := 403/40000000) (ψ := -221723/200000) 199 129
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t59 : ((-3443108483/62500000000 : ℚ) : ℝ) ≤ stT199 59 := by
  have hc : ((-26447/62500 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3443108483/62500000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-26447/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c60 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((119421/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1163637/5000000) (δ := 2517/250000000) (ψ := -221723/200000) 199 130
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t60 : ((77079442267/1000000000000 : ℚ) : ℝ) ≤ stT199 60 := by
  have hc : ((119411/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77079442267/1000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((119411/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c61 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-17717/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5896053/10000000) (δ := 623/62500000) (ψ := -221723/200000) 199 130
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t61 : ((-90743592137/1000000000000 : ℚ) : ℝ) ≤ stT199 61 := by
  have hc : ((-70873/100000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90743592137/1000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-70873/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c62 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((77193/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1722311/10000000) (δ := 5071/500000000) (ψ := -221723/200000) 199 131
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t62 : ((24507209297/250000000000 : ℚ) : ℝ) ≤ stT199 62 := by
  have hc : ((19297/25000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24507209297/250000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((19297/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c63 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-159647/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97467/156250) (δ := 5071/500000000) (ψ := -221723/200000) 199 131
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t63 : ((-100574490237/1000000000000 : ℚ) : ℝ) ≤ stT199 63 := by
  have hc : ((-159657/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100574490237/1000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-159657/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c64 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((158717/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51103/312500) (δ := 10149/1000000000) (ψ := -221723/200000) 199 132
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t64 : ((158707/1600000 : ℚ) : ℝ) ≤ stT199 64 := by
  have hc : ((158707/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158707/1600000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((158707/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c65 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-758117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6078043/10000000) (δ := 4977/500000000) (ψ := -221723/200000) 199 132
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t65 : ((-235097730529/2500000000000 : ℚ) : ℝ) ≤ stT199 65 := by
  have hc : ((-758167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-235097730529/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-758167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c66 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((171697/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2034339/10000000) (δ := 2489/250000000) (ψ := -221723/200000) 199 133
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t66 : ((211328854633/2500000000000 : ℚ) : ℝ) ≤ stT199 66 := by
  have hc : ((343369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211328854633/2500000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((343369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c67 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-114247/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 680877/1250000) (δ := 10047/1000000000) (ψ := -221723/200000) 199 133
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t67 : ((-27917441123/400000000000 : ℚ) : ℝ) ≤ stT199 67 := by
  have hc : ((-114257/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27917441123/400000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-114257/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c68 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((100711/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -578087/2000000) (δ := 10039/1000000000) (ψ := -221723/200000) 199 134
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t68 : ((122114855583/2500000000000 : ℚ) : ℝ) ≤ stT199 68 := by
  have hc : ((201397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122114855583/2500000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((201397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c69 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-177249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1093117/2500000) (δ := 10039/1000000000) (ψ := -221723/200000) 199 134
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t69 : ((-213442996841/10000000000000 : ℚ) : ℝ) ≤ stT199 69 := by
  have hc : ((-177299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213442996841/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-177299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c70 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-24971/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4177117/10000000) (δ := 627/62500000) (ψ := -221723/200000) 199 135
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t70 : ((-59722007443/5000000000000 : ℚ) : ℝ) ≤ stT199 70 := by
  have hc : ((-49967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59722007443/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-49967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c71 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((406763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1439861/5000000) (δ := 10071/1000000000) (ψ := -221723/200000) 199 135
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t71 : ((482679260853/10000000000000 : ℚ) : ℝ) ≤ stT199 71 := by
  have hc : ((406713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((482679260853/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((406713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c72 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-140261/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5870057/10000000) (δ := 5039/500000000) (ψ := -221723/200000) 199 136
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t72 : ((-10331941047/125000000000 : ℚ) : ℝ) ≤ stT199 72 := by
  have hc : ((-140271/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10331941047/125000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-140271/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c73 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((461143/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 992109/10000000) (δ := 81/8000000) (ψ := -221723/200000) 199 136
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t73 : ((269848789749/2500000000000 : ℚ) : ℝ) ≤ stT199 73 := by
  have hc : ((230559/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((269848789749/2500000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((230559/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c74 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-999307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1552179/2000000) (δ := 81/8000000) (ψ := -221723/200000) 199 136
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t74 : ((-1161729527289/10000000000000 : ℚ) : ℝ) ≤ stT199 74 := by
  have hc : ((-999357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1161729527289/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-999357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c75 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((873899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -317269/2500000) (δ := 5059/500000000) (ψ := -221723/200000) 199 137
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t75 : ((10090334403/100000000000 : ℚ) : ℝ) ≤ stT199 75 := by
  have hc : ((873849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10090334403/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((873849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c76 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-264477/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5320411/10000000) (δ := 5059/500000000) (ψ := -221723/200000) 199 137
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t76 : ((-151702344829/2500000000000 : ℚ) : ℝ) ≤ stT199 76 := by
  have hc : ((-132251/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151702344829/2500000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-132251/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c77 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((17123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1942091/5000000) (δ := 1249/125000000) (ψ := -221723/200000) 199 138
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t77 : ((3891295233/2000000000000 : ℚ) : ℝ) ≤ stT199 77 := by
  have hc : ((17073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3891295233/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((17073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c78 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((528381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2535259/10000000) (δ := 10111/1000000000) (ψ := -221723/200000) 199 138
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t78 : ((598217039687/10000000000000 : ℚ) : ℝ) ≤ stT199 78 := by
  have hc : ((528331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((598217039687/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((528331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c79 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-459043/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6835051/10000000) (δ := 10099/1000000000) (ψ := -221723/200000) 199 139
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t79 : ((-4035092953/39062500000 : ℚ) : ℝ) ≤ stT199 79 := by
  have hc : ((-114767/125000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4035092953/39062500000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-114767/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c80 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((38939/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -288549/5000000) (δ := 10099/1000000000) (ψ := -221723/200000) 199 139
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t80 : ((43532850921/400000000000 : ℚ) : ℝ) ≤ stT199 80 := by
  have hc : ((38937/40000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43532850921/400000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((38937/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c81 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-155333/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1120619/2000000) (δ := 1263/125000000) (ψ := -221723/200000) 199 139
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t81 : ((-43151562299/625000000000 : ℚ) : ℝ) ≤ stT199 81 := by
  have hc : ((-310691/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43151562299/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-310691/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c82 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-29397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4000493/10000000) (δ := 10007/1000000000) (ψ := -221723/200000) 199 140
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t82 : ((-8129698313/2500000000000 : ℚ) : ℝ) ≤ stT199 82 := by
  have hc : ((-29447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8129698313/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-29447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c83 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((688077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2029903/10000000) (δ := 631/62500000) (ψ := -221723/200000) 199 140
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t83 : ((377603666167/5000000000000 : ℚ) : ℝ) ≤ stT199 83 := by
  have hc : ((688027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((377603666167/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((688027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c84 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-998563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -308797/400000) (δ := 10007/500000000) (ψ := -221723/200000) 199 141
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t84 : ((-108957665817/1000000000000 : ℚ) : ℝ) ≤ stT199 84 := by
  have hc : ((-998613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108957665817/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-998613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c85 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((185807/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -916143/5000000) (δ := 5057/500000000) (ψ := -221723/200000) 199 141
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t85 : ((100761188007/1250000000000 : ℚ) : ℝ) ≤ stT199 85 := by
  have hc : ((371589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100761188007/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((371589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c86 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-23791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1993237/5000000) (δ := 5057/500000000) (ψ := -221723/200000) 199 141
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t86 : ((-3213552231/1250000000000 : ℚ) : ℝ) ≤ stT199 86 := by
  have hc : ((-23841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3213552231/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-23841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c87 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-729219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2984971/5000000) (δ := 4991/500000000) (ψ := -221723/200000) 199 142
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t87 : ((-781858775397/10000000000000 : ℚ) : ℝ) ≤ stT199 87 := by
  have hc : ((-729269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-781858775397/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-729269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c88 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((993547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71041/2500000) (δ := 5041/500000000) (ψ := -221723/200000) 199 142
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t88 : ((1059070782491/10000000000000 : ℚ) : ℝ) ≤ stT199 88 := by
  have hc : ((993497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1059070782491/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((993497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c89 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-16709/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2668669/5000000) (δ := 10121/1000000000) (ψ := -221723/200000) 199 142
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t89 : ((-141705302631/2500000000000 : ℚ) : ℝ) ≤ stT199 89 := by
  have hc : ((-267369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141705302631/2500000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-267369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c90 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-173311/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4811909/10000000) (δ := 399/40000000) (ψ := -221723/200000) 199 143
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t90 : ((-22839033031/625000000000 : ℚ) : ℝ) ≤ stT199 90 := by
  have hc : ((-21667/62500 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22839033031/625000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-21667/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c91 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((481327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 685391/10000000) (δ := 803/40000000) (ψ := -221723/200000) 199 143
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t91 : ((63067648221/625000000000 : ℚ) : ℝ) ≤ stT199 91 := by
  have hc : ((240651/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63067648221/625000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((240651/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c92 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-769617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3061297/5000000) (δ := 2507/250000000) (ψ := -221723/200000) 199 143
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t92 : ((-802434033191/10000000000000 : ℚ) : ℝ) ≤ stT199 92 := by
  have hc : ((-769667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-802434033191/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-769667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c93 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-111749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4206947/10000000) (δ := 2517/250000000) (ψ := -221723/200000) 199 144
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t93 : ((-14491274581/1250000000000 : ℚ) : ℝ) ≤ stT199 93 := by
  have hc : ((-111799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14491274581/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-111799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c94 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((451179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 222793/2000000) (δ := 623/62500000) (ψ := -221723/200000) 199 144
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t94 : ((232664854917/2500000000000 : ℚ) : ℝ) ≤ stT199 94 := by
  have hc : ((225577/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((232664854917/2500000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((225577/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c95 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-830847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19933/31250) (δ := 2007/200000000) (ψ := -221723/200000) 199 144
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t95 : ((-852482873163/10000000000000 : ℚ) : ℝ) ≤ stT199 95 := by
  have hc : ((-830897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-852482873163/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-830897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c96 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-771/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1029983/2500000) (δ := 503/50000000) (ψ := -221723/200000) 199 145
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t96 : ((-1574818203/200000000000 : ℚ) : ℝ) ≤ stT199 96 := by
  have hc : ((-1543/20000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1574818203/200000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-1543/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c97 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((915429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1035561/10000000) (δ := 503/50000000) (ψ := -221723/200000) 199 145
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t97 : ((464713203067/5000000000000 : ℚ) : ℝ) ≤ stT199 97 := by
  have hc : ((915379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((464713203067/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((915379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c98 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-38679/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 613817/1000000) (δ := 249/25000000) (ψ := -221723/200000) 199 145
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t98 : ((-78148466539/1000000000000 : ℚ) : ℝ) ≤ stT199 98 := by
  have hc : ((-77363/100000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78148466539/1000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-77363/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c99 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-234587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2259487/5000000) (δ := 201/20000000) (ψ := -221723/200000) 199 146
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t99 : ((-117909550603/5000000000000 : ℚ) : ℝ) ≤ stT199 99 := by
  have hc : ((-234637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117909550603/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-234637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c100 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((122693/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9621/200000) (δ := 9953/1000000000) (ψ := -221723/200000) 199 146
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t100 : ((490746509253/5000000000000 : ℚ) : ℝ) ≤ stT199 100 := by
  have hc : ((490747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((490746509253/5000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((490747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c101 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-566089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2715687/5000000) (δ := 9953/1000000000) (ψ := -221723/200000) 199 146
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t101 : ((-281664909141/5000000000000 : ℚ) : ℝ) ≤ stT199 101 := by
  have hc : ((-566139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-281664909141/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-566139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c102 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-547381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -537507/1000000) (δ := 9957/1000000000) (ψ := -221723/200000) 199 147
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t102 : ((-135509427447/2500000000000 : ℚ) : ℝ) ≤ stT199 102 := by
  have hc : ((-547431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135509427447/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-547431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c103 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((978329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -52141/1000000) (δ := 10057/1000000000) (ψ := -221723/200000) 199 147
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t103 : ((963926668791/10000000000000 : ℚ) : ℝ) ≤ stT199 103 := by
  have hc : ((978279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((963926668791/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((978279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c104 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-142867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 857077/2000000) (δ := 9957/1000000000) (ψ := -221723/200000) 199 147
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t104 : ((-140141694777/10000000000000 : ℚ) : ℝ) ≤ stT199 104 := by
  have hc : ((-142917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140141694777/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-142917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c105 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-444213/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -832719/1250000) (δ := 2491/250000000) (ψ := -221723/200000) 199 148
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t105 : ((-216766154219/2500000000000 : ℚ) : ℝ) ≤ stT199 105 := by
  have hc : ((-222119/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-216766154219/2500000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-222119/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c106 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((71201/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1946099/10000000) (δ := 10039/1000000000) (ψ := -221723/200000) 199 148
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t106 : ((3457580343/50000000000 : ℚ) : ℝ) ≤ stT199 106 := by
  have hc : ((17799/25000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3457580343/50000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((17799/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c107 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((462369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2725327/10000000) (δ := 629/62500000) (ψ := -221723/200000) 199 148
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t107 : ((27933776299/625000000000 : ℚ) : ℝ) ≤ stT199 107 := by
  have hc : ((462319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27933776299/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((462319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c108 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-98001/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7353271/10000000) (δ := 629/62500000) (ψ := -221723/200000) 199 148
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t108 : ((-47153185753/500000000000 : ℚ) : ℝ) ≤ stT199 108 := by
  have hc : ((-49003/50000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47153185753/500000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-49003/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c109 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((62981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1884717/5000000) (δ := 9971/1000000000) (ψ := -221723/200000) 199 149
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t109 : ((30138474003/5000000000000 : ℚ) : ℝ) ≤ stT199 109 := by
  have hc : ((62931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30138474003/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((62931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c110 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((952457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 154797/2000000) (δ := 10071/1000000000) (ψ := -221723/200000) 199 149
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t110 : ((454041941517/5000000000000 : ℚ) : ℝ) ≤ stT199 110 := by
  have hc : ((952407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454041941517/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((952407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c111 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-256951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 527631/1000000) (δ := 9971/1000000000) (ψ := -221723/200000) 199 149
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t111 : ((-7622213319/156250000000 : ℚ) : ℝ) ≤ stT199 111 := by
  have hc : ((-16061/31250 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7622213319/156250000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-16061/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c112 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-364587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -238791/400000) (δ := 401/40000000) (ψ := -221723/200000) 199 150
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t112 : ((-5383222721/78125000000 : ℚ) : ℝ) ≤ stT199 112 := by
  have hc : ((-91153/125000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5383222721/78125000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-91153/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c113 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((40723/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1547497/10000000) (δ := 5039/500000000) (ψ := -221723/200000) 199 150
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t113 : ((957664719/12500000000 : ℚ) : ℝ) ≤ stT199 113 := by
  have hc : ((81441/100000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((957664719/12500000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((81441/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c114 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((422757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44309/156250) (δ := 401/40000000) (ψ := -221723/200000) 199 150
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t114 : ((79180207119/2000000000000 : ℚ) : ℝ) ≤ stT199 114 := by
  have hc : ((422707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79180207119/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((422707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c115 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-240991/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 897599/1250000) (δ := 4989/500000000) (ψ := -221723/200000) 199 150
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t115 : ((-89894787507/1000000000000 : ℚ) : ℝ) ≤ stT199 115 := by
  have hc : ((-482007/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89894787507/1000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-482007/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c116 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-58431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -527477/1250000) (δ := 5043/500000000) (ψ := -221723/200000) 199 151
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t116 : ((-6784381439/625000000000 : ℚ) : ℝ) ≤ stT199 116 := by
  have hc : ((-7307/62500 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6784381439/625000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-7307/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c117 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((199959/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 791/156250) (δ := 10017/1000000000) (ψ := -221723/200000) 199 151
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t117 : ((369705701/4000000000 : ℚ) : ℝ) ≤ stT199 117 := by
  have hc : ((199949/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((369705701/4000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((199949/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c118 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-28519/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4284697/10000000) (δ := 10117/1000000000) (ψ := -221723/200000) 199 151
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t118 : ((-1050523367/80000000000 : ℚ) : ℝ) ≤ stT199 118 := by
  have hc : ((-28529/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1050523367/80000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-28529/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c119 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-968513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7224963/10000000) (δ := 1001/100000000) (ψ := -221723/200000) 199 152
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t119 : ((-887880733537/10000000000000 : ℚ) : ℝ) ≤ stT199 119 := by
  have hc : ((-968563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-887880733537/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-968563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c120 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((169617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1530867/5000000) (δ := 1011/100000000) (ψ := -221723/200000) 199 152
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t120 : ((1935193113/62500000000 : ℚ) : ℝ) ≤ stT199 120 := by
  have hc : ((21199/62500 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1935193113/62500000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((21199/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c121 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((227577/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1066919/10000000) (δ := 1011/100000000) (ψ := -221723/200000) 199 152
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t121 : ((41375322261/500000000000 : ℚ) : ℝ) ≤ stT199 121 := by
  have hc : ((455129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41375322261/500000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((455129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c122 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-474011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5161593/10000000) (δ := 1001/100000000) (ψ := -221723/200000) 199 152
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t122 : ((-214597459419/5000000000000 : ℚ) : ℝ) ≤ stT199 122 := by
  have hc : ((-474061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-214597459419/5000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-474061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c123 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-853807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -810641/1250000) (δ := 101/10000000) (ψ := -221723/200000) 199 153
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t123 : ((-76989724119/1000000000000 : ℚ) : ℝ) ≤ stT199 123 := by
  have hc : ((-853857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76989724119/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-853857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c124 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((554771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2456771/10000000) (δ := 101/10000000) (ψ := -221723/200000) 199 153
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t124 : ((249076940373/5000000000000 : ℚ) : ℝ) ≤ stT199 124 := by
  have hc : ((554721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249076940373/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((554721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c125 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((81637/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 96203/625000) (δ := 10003/1000000000) (ψ := -221723/200000) 199 153
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t125 : ((2281683277/31250000000 : ℚ) : ℝ) ≤ stT199 125 := by
  have hc : ((2551/3125 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2281683277/31250000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((2551/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c126 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-589609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1375857/2500000) (δ := 101/10000000) (ψ := -221723/200000) 199 153
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t126 : ((-525310102989/10000000000000 : ℚ) : ℝ) ≤ stT199 126 := by
  have hc : ((-589659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-525310102989/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-589659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c127 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-806319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1567937/2500000) (δ := 10107/1000000000) (ψ := -221723/200000) 199 154
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t127 : ((-715537176733/10000000000000 : ℚ) : ℝ) ≤ stT199 127 := by
  have hc : ((-806369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-715537176733/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-806369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c128 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((145847/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -592439/2500000) (δ := 10107/1000000000) (ψ := -221723/200000) 199 154
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t128 : ((257801270727/5000000000000 : ℚ) : ℝ) ≤ stT199 128 := by
  have hc : ((291669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((257801270727/5000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((291669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c129 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((824909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23467/156250) (δ := 2499/250000000) (ψ := -221723/200000) 199 154
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t129 : ((14524942131/200000000000 : ℚ) : ℝ) ≤ stT199 129 := by
  have hc : ((824859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14524942131/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((824859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c130 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-268399/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5343583/10000000) (δ := 2499/250000000) (ψ := -221723/200000) 199 154
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t130 : ((-29427960627/625000000000 : ℚ) : ℝ) ≤ stT199 130 := by
  have hc : ((-33553/62500 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29427960627/625000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-33553/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c131 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-433721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6552087/10000000) (δ := 5057/500000000) (ψ := -221723/200000) 199 155
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t131 : ((-37896604893/500000000000 : ℚ) : ℝ) ≤ stT199 131 := by
  have hc : ((-216873/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37896604893/500000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-216873/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c132 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((223441/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2768799/10000000) (δ := 9989/1000000000) (ψ := -221723/200000) 199 155
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t132 : ((6076831419/156250000000 : ℚ) : ℝ) ≤ stT199 132 := by
  have hc : ((27927/62500 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6076831419/156250000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((27927/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c133 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((461619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 985933/10000000) (δ := 9989/1000000000) (ψ := -221723/200000) 199 155
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t133 : ((200126155873/2500000000000 : ℚ) : ℝ) ≤ stT199 133 := by
  have hc : ((230797/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200126155873/2500000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((230797/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c134 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-309071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4712531/10000000) (δ := 20089/1000000000) (ψ := -221723/200000) 199 155
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t134 : ((-267040049149/10000000000000 : ℚ) : ℝ) ≤ stT199 134 := by
  have hc : ((-309121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-267040049149/10000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-309121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c135 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-243811/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -228017/312500) (δ := 5011/500000000) (ψ := -221723/200000) 199 156
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t135 : ((-419699729961/5000000000000 : ℚ) : ℝ) ≤ stT199 135 := by
  have hc : ((-487647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-419699729961/5000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-487647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c136 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((4821/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -226559/625000) (δ := 5061/500000000) (ψ := -221723/200000) 199 156
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t136 : ((1033063487/100000000000 : ℚ) : ℝ) ≤ stT199 136 := by
  have hc : ((4819/40000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1033063487/100000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((4819/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c137 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((999969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1979/1000000) (δ := 10081/1000000000) (ψ := -221723/200000) 199 156
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t137 : ((854287797083/10000000000000 : ℚ) : ℝ) ≤ stT199 137 := by
  have hc : ((999919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((854287797083/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((999919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c138 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((23071/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3637959/10000000) (δ := 5061/500000000) (ψ := -221723/200000) 199 156
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t138 : ((2453851827/250000000000 : ℚ) : ℝ) ≤ stT199 138 := by
  have hc : ((23061/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2453851827/250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((23061/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c139 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-969019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3615029/5000000) (δ := 5011/500000000) (ψ := -221723/200000) 199 156
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t139 : ((-821953666041/10000000000000 : ℚ) : ℝ) ≤ stT199 139 := by
  have hc : ((-969069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-821953666041/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-969069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c140 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-95933/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4911577/10000000) (δ := 5037/500000000) (ψ := -221723/200000) 199 157
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t140 : ((-32435527621/1000000000000 : ℚ) : ℝ) ≤ stT199 140 := by
  have hc : ((-191891/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32435527621/1000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-191891/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c141 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((853429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137067/1000000) (δ := 10029/1000000000) (ψ := -221723/200000) 199 157
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t141 : ((718673978229/10000000000000 : ℚ) : ℝ) ≤ stT199 141 := by
  have hc : ((853379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((718673978229/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((853379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c142 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((653873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1072631/5000000) (δ := 10029/1000000000) (ψ := -221723/200000) 199 157
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t142 : ((548675838963/10000000000000 : ℚ) : ℝ) ≤ stT199 142 := by
  have hc : ((653823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((548675838963/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((653823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c143 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-78969/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2818259/5000000) (δ := 10029/1000000000) (ψ := -221723/200000) 199 157
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t143 : ((-264169999943/5000000000000 : ℚ) : ℝ) ≤ stT199 143 := by
  have hc : ((-315901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264169999943/5000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-315901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c144 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-175539/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6604567/10000000) (δ := 9967/1000000000) (ψ := -221723/200000) 199 158
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t144 : ((-73145475183/1000000000000 : ℚ) : ℝ) ≤ stT199 144 := by
  have hc : ((-175549/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73145475183/1000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-175549/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c145 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((301389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1580809/5000000) (δ := 2509/250000000) (ψ := -221723/200000) 199 158
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t145 : ((125124088953/5000000000000 : ℚ) : ℝ) ≤ stT199 145 := by
  have hc : ((301339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125124088953/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((301339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c146 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((497347/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5153/200000) (δ := 1267/125000000) (ψ := -221723/200000) 199 158
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t146 : ((41158617381/500000000000 : ℚ) : ℝ) ≤ stT199 146 := by
  have hc : ((248661/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41158617381/500000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((248661/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c147 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((27291/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 730707/2000000) (δ := 2509/250000000) (ψ := -221723/200000) 199 158
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t147 : ((22498924901/2500000000000 : ℚ) : ℝ) ≤ stT199 147 := by
  have hc : ((54557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22498924901/2500000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((54557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c148 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-59107/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1756609/2500000) (δ := 1267/125000000) (ψ := -221723/200000) 199 158
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t148 : ((-77741163519/1000000000000 : ℚ) : ℝ) ≤ stT199 148 := by
  have hc : ((-472881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77741163519/1000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-472881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c149 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-10653/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5331313/10000000) (δ := 249/25000000) (ψ := -221723/200000) 199 159
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t149 : ((-136376527/3125000000 : ℚ) : ℝ) ≤ stT199 149 := by
  have hc : ((-5327/10000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136376527/3125000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-5327/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c150 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((695677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -400717/2000000) (δ := 10043/1000000000) (ψ := -221723/200000) 199 159
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t150 : ((35498541437/625000000000 : ℚ) : ℝ) ≤ stT199 150 := by
  have hc : ((695627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35498541437/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((695627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c151 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((867401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1302103/10000000) (δ := 503/50000000) (ψ := -221723/200000) 199 159
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t151 : ((176459958897/2500000000000 : ℚ) : ℝ) ≤ stT199 151 := by
  have hc : ((867351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176459958897/2500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((867351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c152 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-260543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143311/312500) (δ := 10143/1000000000) (ψ := -221723/200000) 199 159
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t152 : ((-52842266761/2500000000000 : ℚ) : ℝ) ≤ stT199 152 := by
  have hc : ((-260593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52842266761/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-260593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c153 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-999997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3924129/5000000) (δ := 249/25000000) (ψ := -221723/200000) 199 159
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t153 : ((-808490997291/10000000000000 : ℚ) : ℝ) ≤ stT199 153 := by
  have hc : ((-1000047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-808490997291/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-1000047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c154 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-54629/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2309321/5000000) (δ := 9953/1000000000) (ψ := -221723/200000) 199 160
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t154 : ((-44029362897/2000000000000 : ℚ) : ℝ) ≤ stT199 154 := by
  have hc : ((-54639/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44029362897/2000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-54639/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c155 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((423779/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1398573/10000000) (δ := 201/20000000) (ψ := -221723/200000) 199 160
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t155 : ((170183632063/2500000000000 : ℚ) : ℝ) ≤ stT199 155 := by
  have hc : ((211877/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170183632063/2500000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((211877/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c156 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((150319/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2251/12500) (δ := 203/20000000) (ψ := -221723/200000) 199 160
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t156 : ((188036559/3125000000 : ℚ) : ℝ) ≤ stT199 156 := by
  have hc : ((150309/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188036559/3125000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((150309/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c157 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-408759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 199189/400000) (δ := 9953/1000000000) (ψ := -221723/200000) 199 160
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t157 : ((-326265148383/10000000000000 : ℚ) : ℝ) ≤ stT199 157 := by
  have hc : ((-408809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-326265148383/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-408809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c158 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-993533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7569511/10000000) (δ := 10057/1000000000) (ψ := -221723/200000) 199 161
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t158 : ((-395226452157/5000000000000 : ℚ) : ℝ) ≤ stT199 158 := by
  have hc : ((-993583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-395226452157/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-993583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c159 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-200117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1107671/2500000) (δ := 10057/1000000000) (ψ := -221723/200000) 199 161
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t159 : ((-39685709921/2500000000000 : ℚ) : ℝ) ≤ stT199 159 := by
  have hc : ((-200167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39685709921/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-200167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c160 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((865513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -655779/5000000) (δ := 10057/1000000000) (ψ := -221723/200000) 199 161
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t160 : ((684208218447/10000000000000 : ℚ) : ℝ) ≤ stT199 160 := by
  have hc : ((865463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((684208218447/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((865463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c161 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((188733/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 357623/2000000) (δ := 5073/500000000) (ψ := -221723/200000) 199 161
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t161 : ((29746502651/500000000000 : ℚ) : ℝ) ≤ stT199 161 := by
  have hc : ((377441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29746502651/500000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((377441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c162 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-73563/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 973727/2000000) (δ := 5073/500000000) (ψ := -221723/200000) 199 161
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t162 : ((-2312178671/80000000000 : ℚ) : ℝ) ≤ stT199 162 := by
  have hc : ((-73573/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2312178671/80000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-73573/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c163 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-199907/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7777763/10000000) (δ := 5069/500000000) (ψ := -221723/200000) 199 162
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t163 : ((-156587189337/2000000000000 : ℚ) : ℝ) ≤ stT199 163 := by
  have hc : ((-199917/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156587189337/2000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-199917/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c164 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-79397/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4734953/10000000) (δ := 1993/200000000) (ψ := -221723/200000) 199 162
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t164 : ((-124016833711/5000000000000 : ℚ) : ℝ) ≤ stT199 164 := by
  have hc : ((-158819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124016833711/5000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-158819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c165 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((774887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1710651/10000000) (δ := 5069/500000000) (ψ := -221723/200000) 199 162
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t165 : ((301604527413/5000000000000 : ℚ) : ℝ) ≤ stT199 165 := by
  have hc : ((774837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((301604527413/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((774837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c166 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((868733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 647697/5000000) (δ := 2013/200000000) (ψ := -221723/200000) 199 162
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t166 : ((13484566209/200000000000 : ℚ) : ℝ) ≤ stT199 166 := by
  have hc : ((868683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13484566209/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((868683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c167 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-35523/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1070857/2500000) (δ := 5069/500000000) (ψ := -221723/200000) 199 162
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t167 : ((-859319461/78125000000 : ℚ) : ℝ) ≤ stT199 167 := by
  have hc : ((-71071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-859319461/78125000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-71071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c168 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-971297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7253553/10000000) (δ := 5019/500000000) (ψ := -221723/200000) 199 162
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t168 : ((-749410723399/10000000000000 : ℚ) : ℝ) ≤ stT199 168 := by
  have hc : ((-971347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-749410723399/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-971347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c169 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-294549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5501847/10000000) (δ := 2493/250000000) (ψ := -221723/200000) 199 163
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t169 : ((-113297726297/2500000000000 : ℚ) : ℝ) ≤ stT199 169 := by
  have hc : ((-147287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113297726297/2500000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-147287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c170 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((258823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1283373/5000000) (δ := 1259/125000000) (ψ := -221723/200000) 199 163
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t170 : ((24811093659/625000000000 : ℚ) : ℝ) ≤ stT199 170 := by
  have hc : ((129399/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24811093659/625000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((129399/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c171 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((123769/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 351141/10000000) (δ := 2493/250000000) (ψ := -221723/200000) 199 163
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t171 : ((378574905669/5000000000000 : ℚ) : ℝ) ≤ stT199 171 := by
  have hc : ((495051/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((378574905669/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((495051/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c172 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((133361/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1626007/5000000) (δ := 1259/125000000) (ψ := -221723/200000) 199 163
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t172 : ((3177113541/156250000000 : ℚ) : ℝ) ≤ stT199 172 := by
  have hc : ((16667/62500 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3177113541/156250000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((16667/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c173 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-96631/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6136071/10000000) (δ := 2493/250000000) (ψ := -221723/200000) 199 163
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t173 : ((-146943896507/2500000000000 : ℚ) : ℝ) ≤ stT199 173 := by
  have hc : ((-386549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146943896507/2500000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-386549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c174 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-112017/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1676113/2500000) (δ := 2531/250000000) (ψ := -221723/200000) 199 164
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t174 : ((-339698855207/5000000000000 : ℚ) : ℝ) ≤ stT199 174 := by
  have hc : ((-448093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-339698855207/5000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-448093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c175 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((29421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -963357/2500000) (δ := 10079/1000000000) (ψ := -221723/200000) 199 164
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t175 : ((2775295161/1250000000000 : ℚ) : ℝ) ≤ stT199 175 := by
  have hc : ((29371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2775295161/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((29371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c176 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((918127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1018673/10000000) (δ := 10079/1000000000) (ψ := -221723/200000) 199 164
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t176 : ((346013122453/5000000000000 : ℚ) : ℝ) ≤ stT199 176 := by
  have hc : ((918077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((346013122453/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((918077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c177 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((751789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 900031/5000000) (δ := 1253/125000000) (ψ := -221723/200000) 199 164
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t177 : ((282520806197/5000000000000 : ℚ) : ℝ) ≤ stT199 177 := by
  have hc : ((751739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((282520806197/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((751739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c178 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-267073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2301439/5000000) (δ := 10079/1000000000) (ψ := -221723/200000) 199 164
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t178 : ((-50054309109/2500000000000 : ℚ) : ℝ) ≤ stT199 178 := by
  have hc : ((-267123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50054309109/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-267123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c179 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-982829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3695011/5000000) (δ := 9979/1000000000) (ψ := -221723/200000) 199 164
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t179 : ((-183659787061/2500000000000 : ℚ) : ℝ) ≤ stT199 179 := by
  have hc : ((-982879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183659787061/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-982879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c180 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-120679/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5546369/10000000) (δ := 10017/1000000000) (ψ := -221723/200000) 199 165
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t180 : ((-22489067571/500000000000 : ℚ) : ℝ) ≤ stT199 180 := by
  have hc : ((-120689/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22489067571/500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-120689/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c181 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((439237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2790119/10000000) (δ := 5043/500000000) (ψ := -221723/200000) 199 165
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t181 : ((163222530989/5000000000000 : ℚ) : ℝ) ≤ stT199 181 := by
  have hc : ((439187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163222530989/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((439187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c182 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((999807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -49093/10000000) (δ := 5043/500000000) (ψ := -221723/200000) 199 165
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t182 : ((741068876493/10000000000000 : ℚ) : ℝ) ≤ stT199 182 := by
  have hc : ((999757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((741068876493/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((999757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c183 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((479437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1338479/5000000) (δ := 4993/500000000) (ψ := -221723/200000) 199 165
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t183 : ((354372937527/10000000000000 : ℚ) : ℝ) ≤ stT199 183 := by
  have hc : ((479387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((354372937527/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((479387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c184 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-551747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2694067/5000000) (δ := 4993/500000000) (ψ := -221723/200000) 199 165
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t184 : ((-40679026637/1000000000000 : ℚ) : ℝ) ≤ stT199 184 := by
  have hc : ((-551797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40679026637/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-551797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c185 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-995747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -762333/1000000) (δ := 1011/100000000) (ψ := -221723/200000) 199 166
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t185 : ((-146424978271/2000000000000 : ℚ) : ℝ) ≤ stT199 185 := by
  have hc : ((-995797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146424978271/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-995797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c186 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-394723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4941407/10000000) (δ := 1011/100000000) (ψ := -221723/200000) 199 166
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t186 : ((-72365443857/2500000000000 : ℚ) : ℝ) ≤ stT199 186 := by
  have hc : ((-394773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72365443857/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-394773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c187 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((614121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -568453/2500000) (δ := 1011/100000000) (ψ := -221723/200000) 199 166
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t187 : ((56131616039/1250000000000 : ℚ) : ℝ) ≤ stT199 187 := by
  have hc : ((614071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56131616039/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((614071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c188 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((1977/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75901/2000000) (δ := 1001/100000000) (ψ := -221723/200000) 199 166
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t188 : ((3604501539/50000000000 : ℚ) : ℝ) ≤ stT199 188 := by
  have hc : ((19769/20000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3604501539/50000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((19769/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c189 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((177671/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 377349/1250000) (δ := 1011/100000000) (ψ := -221723/200000) 199 166
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t189 : ((2019035613/78125000000 : ℚ) : ℝ) ≤ stT199 189 := by
  have hc : ((88823/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2019035613/78125000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((88823/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c190 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-6341/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56441/100000) (δ := 9993/1000000000) (ψ := -221723/200000) 199 166
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t190 : ((-9201224791/200000000000 : ℚ) : ℝ) ≤ stT199 190 := by
  have hc : ((-12683/20000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9201224791/200000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-12683/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c191 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-987119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7452287/10000000) (δ := 10003/1000000000) (ψ := -221723/200000) 199 167
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t191 : ((-28571632367/400000000000 : ℚ) : ℝ) ≤ stT199 191 := by
  have hc : ((-987169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28571632367/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-987169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c192 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-362511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -606799/1250000) (δ := 10103/1000000000) (ψ := -221723/200000) 199 167
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t192 : ((-32706990371/1250000000000 : ℚ) : ℝ) ≤ stT199 192 := by
  have hc : ((-362561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32706990371/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-362561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c193 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((61533/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2269979/10000000) (δ := 10103/1000000000) (ψ := -221723/200000) 199 167
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t193 : ((1107219433/25000000000 : ℚ) : ℝ) ≤ stT199 193 := by
  have hc : ((7691/12500 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1107219433/25000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((7691/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c194 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((248189/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 301101/10000000) (δ := 10103/1000000000) (ψ := -221723/200000) 199 167
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t194 : ((178180303587/2500000000000 : ℚ) : ℝ) ≤ stT199 194 := by
  have hc : ((496353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178180303587/2500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((496353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c195 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((20717/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 714737/2500000) (δ := 1/100000) (ψ := -221723/200000) 199 167
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t195 : ((14833943453/500000000000 : ℚ) : ℝ) ≤ stT199 195 := by
  have hc : ((41429/100000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14833943453/500000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((41429/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c196 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-139233/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 540371/1000000) (δ := 10003/1000000000) (ψ := -221723/200000) 199 167
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t196 : ((-99461111213/2500000000000 : ℚ) : ℝ) ≤ stT199 196 := by
  have hc : ((-278491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99461111213/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-278491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c197 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-249867/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3886213/5000000) (δ := 1999/200000000) (ψ := -221723/200000) 199 168
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t197 : ((-356063794489/5000000000000 : ℚ) : ℝ) ≤ stT199 197 := by
  have hc : ((-499759/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-356063794489/5000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-499759/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c198 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-506031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2626717/5000000) (δ := 1251/125000000) (ψ := -221723/200000) 199 168
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t198 : ((-35965658427/1000000000000 : ℚ) : ℝ) ≤ stT199 198 := by
  have hc : ((-506081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35965658427/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-506081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c199 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((454619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2747129/10000000) (δ := 2019/200000000) (ψ := -221723/200000) 199 168
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t199 : ((322235327289/10000000000000 : ℚ) : ℝ) ≤ stT199 199 := by
  have hc : ((454569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((322235327289/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((454569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c200 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((994867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25341/1000000) (δ := 1999/200000000) (ψ := -221723/200000) 199 168
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t200 : ((351720534801/5000000000000 : ℚ) : ℝ) ≤ stT199 200 := by
  have hc : ((994817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((351720534801/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((994817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c201 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((78563/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2227921/10000000) (δ := 1999/200000000) (ψ := -221723/200000) 199 168
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t201 : ((44327688663/1000000000000 : ℚ) : ℝ) ≤ stT199 201 := by
  have hc : ((314227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44327688663/1000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((314227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c202 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-60621/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 146777/312500) (δ := 2019/200000000) (ψ := -221723/200000) 199 168
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t202 : ((-21329925169/1000000000000 : ℚ) : ℝ) ≤ stT199 202 := by
  have hc : ((-60631/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21329925169/1000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-60631/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c203 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-961021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7153669/10000000) (δ := 2527/250000000) (ψ := -221723/200000) 199 168
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t203 : ((-674540175273/10000000000000 : ℚ) : ℝ) ≤ stT199 203 := by
  have hc : ((-961071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-674540175273/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-961071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c204 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-766283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -305479/500000) (δ := 1261/125000000) (ψ := -221723/200000) 199 169
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t204 : ((-536541152953/10000000000000 : ℚ) : ℝ) ≤ stT199 204 := by
  have hc : ((-766333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-536541152953/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-766333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c205 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((99907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -735361/2000000) (δ := 1261/125000000) (ψ := -221723/200000) 199 169
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t205 : ((6974312451/1000000000000 : ℚ) : ℝ) ≤ stT199 205 := by
  have hc : ((99857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6974312451/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((99857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c206 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((438227/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -125587/1000000) (δ := 2003/200000000) (ψ := -221723/200000) 199 169
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t206 : ((152654897033/2500000000000 : ℚ) : ℝ) ≤ stT199 206 := by
  have hc : ((219101/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152654897033/2500000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((219101/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c207 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((447731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1153323/10000000) (δ := 1261/125000000) (ψ := -221723/200000) 199 169
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t207 : ((19448572493/312500000000 : ℚ) : ℝ) ≤ stT199 207 := by
  have hc : ((223853/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19448572493/312500000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((223853/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c208 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((7493/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 142037/400000) (δ := 2497/250000000) (ψ := -221723/200000) 199 169
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t208 : ((83099607/8000000000 : ℚ) : ℝ) ≤ stT199 208 := by
  have hc : ((14981/100000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83099607/8000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((14981/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c209 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-720149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1187407/2000000) (δ := 2023/200000000) (ψ := -221723/200000) 199 169
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t209 : ((-99634490257/2000000000000 : ℚ) : ℝ) ≤ stT199 209 := by
  have hc : ((-720199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99634490257/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-720199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c210 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-983283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1849053/2500000) (δ := 9981/1000000000) (ψ := -221723/200000) 199 170
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t210 : ((-339282334989/5000000000000 : ℚ) : ℝ) ≤ stT199 210 := by
  have hc : ((-983333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-339282334989/5000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-983333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c211 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-107009/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1258197/2500000) (δ := 5061/500000000) (ψ := -221723/200000) 199 170
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t211 : ((-147353408447/5000000000000 : ℚ) : ℝ) ≤ stT199 211 := by
  have hc : ((-214043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147353408447/5000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-214043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c212 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((478173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2680559/10000000) (δ := 10081/1000000000) (ψ := -221723/200000) 199 170
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t212 : ((164187916323/5000000000000 : ℚ) : ℝ) ≤ stT199 212 := by
  have hc : ((478123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164187916323/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((478123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c213 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((2477/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -339373/10000000) (δ := 5061/500000000) (ψ := -221723/200000) 199 170
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t213 : ((678850011/10000000000 : ℚ) : ℝ) ≤ stT199 213 := by
  have hc : ((3963/4000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((678850011/10000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((3963/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c214 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((699323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1990867/10000000) (δ := 5011/500000000) (ψ := -221723/200000) 199 170
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t214 : ((95602506741/2000000000000 : ℚ) : ℝ) ≤ stT199 214 := by
  have hc : ((699273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95602506741/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((699273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c215 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-152689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1077553/2500000) (δ := 5011/500000000) (ψ := -221723/200000) 199 170
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t215 : ((-20833446861/2000000000000 : ℚ) : ℝ) ≤ stT199 215 := by
  have hc : ((-152739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20833446861/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-152739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c216 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-880411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6618811/10000000) (δ := 5011/500000000) (ψ := -221723/200000) 199 170
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t216 : ((-299538995427/5000000000000 : ℚ) : ℝ) ≤ stT199 216 := by
  have hc : ((-880461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-299538995427/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-880461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c217 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-911001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5433/8000) (δ := 5037/500000000) (ψ := -221723/200000) 199 171
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t217 : ((-123692483219/2000000000000 : ℚ) : ℝ) ≤ stT199 217 := by
  have hc : ((-911051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123692483219/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-911051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c218 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-228719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2251947/5000000) (δ := 4987/500000000) (ψ := -221723/200000) 199 171
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t218 : ((-77471020467/5000000000000 : ℚ) : ℝ) ≤ stT199 218 := by
  have hc : ((-228769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77471020467/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-228769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c219 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((125759/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1113493/5000000) (δ := 5037/500000000) (ψ := -221723/200000) 199 171
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t219 : ((84973252013/2000000000000 : ℚ) : ℝ) ≤ stT199 219 := by
  have hc : ((125749/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84973252013/2000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((125749/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c220 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((7999/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1581/400000) (δ := 10029/1000000000) (ψ := -221723/200000) 199 171
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t220 : ((26963240607/400000000000 : ℚ) : ℝ) ≤ stT199 220 := by
  have hc : ((39993/40000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26963240607/400000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((39993/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c221 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((15179/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2295787/10000000) (δ := 10029/1000000000) (ψ := -221723/200000) 199 171
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t221 : ((1276205931/31250000000 : ℚ) : ℝ) ≤ stT199 221 := by
  have hc : ((60711/100000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1276205931/31250000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((60711/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c222 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-60863/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 22709/50000) (δ := 5037/500000000) (ψ := -221723/200000) 199 171
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t222 : ((-81714035907/5000000000000 : ℚ) : ℝ) ≤ stT199 222 := by
  have hc : ((-121751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81714035907/5000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-121751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c223 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-908763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1694441/2500000) (δ := 5037/500000000) (ψ := -221723/200000) 199 171
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t223 : ((-12171732509/200000000000 : ℚ) : ℝ) ≤ stT199 223 := by
  have hc : ((-908813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12171732509/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-908813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c224 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-896097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1340847/2000000) (δ := 10067/1000000000) (ψ := -221723/200000) 199 172
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t224 : ((-299382101319/5000000000000 : ℚ) : ℝ) ≤ stT199 224 := by
  have hc : ((-896147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-299382101319/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-896147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c225 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-3478/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4488171/10000000) (δ := 10067/1000000000) (ψ := -221723/200000) 199 172
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t225 : ((-74214037107/5000000000000 : ℚ) : ℝ) ≤ stT199 225 := by
  have hc : ((-111321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74214037107/5000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-111321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c226 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((305769/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1140991/5000000) (δ := 623/31250000) (ψ := -221723/200000) 199 172
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t226 : ((1271111571/31250000000 : ℚ) : ℝ) ≤ stT199 226 := by
  have hc : ((19109/31250 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1271111571/31250000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((19109/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c227 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((199883/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17099/2000000) (δ := 10067/1000000000) (ψ := -221723/200000) 199 172
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t227 : ((132660307179/2000000000000 : ℚ) : ℝ) ≤ stT199 227 := by
  have hc : ((199873/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132660307179/2000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((199873/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c228 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((667071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 525329/2500000) (δ := 10067/1000000000) (ψ := -221723/200000) 199 172
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t228 : ((220872664793/5000000000000 : ℚ) : ℝ) ≤ stT199 228 := by
  have hc : ((667021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220872664793/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((667021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c229 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-140171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 171143/400000) (δ := 10067/1000000000) (ψ := -221723/200000) 199 172
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t229 : ((-92660700999/10000000000000 : ℚ) : ℝ) ≤ stT199 229 := by
  have hc : ((-140221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92660700999/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-140221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c230 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-422813/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1611583/2500000) (δ := 9967/1000000000) (ψ := -221723/200000) 199 172
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t230 : ((-139405671639/2500000000000 : ℚ) : ℝ) ≤ stT199 230 := by
  have hc : ((-211419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139405671639/2500000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-211419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c231 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-955253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7103277/10000000) (δ := 2511/250000000) (ψ := -221723/200000) 199 173
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t231 : ((-19641984983/312500000000 : ℚ) : ℝ) ≤ stT199 231 := by
  have hc : ((-955303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19641984983/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-955303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c232 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-399447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1238569/2500000) (δ := 2511/250000000) (ψ := -221723/200000) 199 173
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t232 : ((-262282963901/10000000000000 : ℚ) : ℝ) ≤ stT199 232 := by
  have hc : ((-399497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-262282963901/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-399497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c233 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((215231/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2814479/10000000) (δ := 9959/1000000000) (ψ := -221723/200000) 199 173
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t233 : ((70492984963/2500000000000 : ℚ) : ℝ) ≤ stT199 233 := by
  have hc : ((107603/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70492984963/2500000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((107603/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c234 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((481411/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -170959/2500000) (δ := 10059/1000000000) (ψ := -221723/200000) 199 173
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t234 : ((3933645699/62500000000 : ℚ) : ℝ) ≤ stT199 234 := by
  have hc : ((240693/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3933645699/62500000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((240693/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c235 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((209787/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1437703/10000000) (δ := 10059/1000000000) (ψ := -221723/200000) 199 173
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t235 : ((34210445009/625000000000 : ℚ) : ℝ) ≤ stT199 235 := by
  have hc : ((419549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34210445009/625000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((419549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c236 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((150131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1775119/5000000) (δ := 317/31250000) (ψ := -221723/200000) 199 173
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t236 : ((1526473851/156250000000 : ℚ) : ℝ) ≤ stT199 236 := by
  have hc : ((150081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1526473851/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((150081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c237 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-6371/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5653817/10000000) (δ := 2511/250000000) (ψ := -221723/200000) 199 173
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t237 : ((-827747051/20000000000 : ℚ) : ℝ) ≤ stT199 237 := by
  have hc : ((-12743/20000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-827747051/20000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-12743/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c238 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-999111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7748541/10000000) (δ := 317/31250000) (ψ := -221723/200000) 199 173
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t238 : ((-161915039211/2500000000000 : ℚ) : ℝ) ≤ stT199 238 := by
  have hc : ((-999161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161915039211/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-999161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c239 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-702273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1174691/2000000) (δ := 311/31250000) (ψ := -221723/200000) 199 174
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t239 : ((-454295525581/10000000000000 : ℚ) : ℝ) ≤ stT199 239 := by
  have hc : ((-702323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-454295525581/10000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-702323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c240 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((10459/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3796193/10000000) (δ := 10151/1000000000) (ψ := -221723/200000) 199 174
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t240 : ((6744798153/2000000000000 : ℚ) : ℝ) ≤ stT199 240 := by
  have hc : ((10449/200000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6744798153/2000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((10449/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c241 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((770587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -431897/2500000) (δ := 10151/1000000000) (ψ := -221723/200000) 199 174
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t241 : ((124086507943/2500000000000 : ℚ) : ℝ) ≤ stT199 241 := by
  have hc : ((770537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124086507943/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((770537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c242 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((991171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16623/500000) (δ := 10151/1000000000) (ψ := -221723/200000) 199 174
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t242 : ((79639545713/1250000000000 : ℚ) : ℝ) ≤ stT199 242 := by
  have hc : ((991121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79639545713/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((991121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c243 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((578751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 149/625) (δ := 2513/250000000) (ψ := -221723/200000) 199 174
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t243 : ((742473383/20000000000 : ℚ) : ℝ) ≤ stT199 243 := by
  have hc : ((578701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((742473383/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((578701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c244 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-7949/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4427133/10000000) (δ := 2513/250000000) (ψ := -221723/200000) 199 174
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t244 : ((-1018022187/80000000000 : ℚ) : ℝ) ≤ stT199 244 := by
  have hc : ((-7951/40000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1018022187/80000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-7951/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c245 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-84893/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6461883/10000000) (δ := 5013/250000000) (ψ := -221723/200000) 199 174
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t245 : ((-27119689773/500000000000 : ℚ) : ℝ) ≤ stT199 245 := by
  have hc : ((-42449/50000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27119689773/500000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-42449/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c246 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-120997/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1804897/2500000) (δ := 5029/500000000) (ψ := -221723/200000) 199 175
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t246 : ((-308595556501/5000000000000 : ℚ) : ℝ) ≤ stT199 246 := by
  have hc : ((-484013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-308595556501/5000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-484013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c247 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((-487947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -520133/1000000) (δ := 5029/500000000) (ψ := -221723/200000) 199 175
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t247 : ((-62101034229/2000000000000 : ℚ) : ℝ) ≤ stT199 247 := by
  have hc : ((-487997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62101034229/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-487997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c248 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((145037/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3191231/10000000) (δ := 5029/500000000) (ψ := -221723/200000) 199 175
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t248 : ((4604131/250000000 : ℚ) : ℝ) ≤ stT199 248 := by
  have hc : ((36253/125000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4604131/250000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((36253/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c249 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((444487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -594621/5000000) (δ := 2029/200000000) (ψ := -221723/200000) 199 175
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t249 : ((35208279561/625000000000 : ℚ) : ℝ) ≤ stT199 249 := by
  have hc : ((222231/250000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35208279561/625000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((222231/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_c250 :
    |Real.cos (((199 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((948631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 201197/2500000) (δ := 2009/200000000) (ψ := -221723/200000) 199 175
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st199_t250 : ((119986959271/2000000000000 : ℚ) : ℝ) ≤ stT199 250 := by
  have hc : ((948581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((199 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st199_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119986959271/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((948581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st199_p1 : ((111463/250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT199 (i+1) := by
  rw [Finset.sum_range_one]
  exact st199_t1

theorem st199_p2 : ((2327226066629/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT199 (i+1))
      = (∑ i ∈ Finset.range 1, stT199 (i+1)) + stT199 2 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 1
    simpa using h
  have hprev := st199_p1
  have hstep := st199_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p3 : ((1873729241931/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT199 (i+1))
      = (∑ i ∈ Finset.range 2, stT199 (i+1)) + stT199 3 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 2
    simpa using h
  have hprev := st199_p2
  have hstep := st199_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p4 : ((2415762366931/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT199 (i+1))
      = (∑ i ∈ Finset.range 3, stT199 (i+1)) + stT199 4 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 3
    simpa using h
  have hprev := st199_p3
  have hstep := st199_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p5 : ((21947874662793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT199 (i+1))
      = (∑ i ∈ Finset.range 4, stT199 (i+1)) + stT199 5 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 4
    simpa using h
  have hprev := st199_p4
  have hstep := st199_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p6 : ((25582259355991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT199 (i+1))
      = (∑ i ∈ Finset.range 5, stT199 (i+1)) + stT199 6 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 5
    simpa using h
  have hprev := st199_p5
  have hstep := st199_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p7 : ((5381322519359/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT199 (i+1))
      = (∑ i ∈ Finset.range 6, stT199 (i+1)) + stT199 7 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 6
    simpa using h
  have hprev := st199_p6
  have hstep := st199_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p8 : ((15175533365591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT199 (i+1))
      = (∑ i ∈ Finset.range 7, stT199 (i+1)) + stT199 8 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 7
    simpa using h
  have hprev := st199_p7
  have hstep := st199_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p9 : ((30697356696553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT199 (i+1))
      = (∑ i ∈ Finset.range 8, stT199 (i+1)) + stT199 9 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 8
    simpa using h
  have hprev := st199_p8
  have hstep := st199_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p10 : ((33213656400101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT199 (i+1))
      = (∑ i ∈ Finset.range 9, stT199 (i+1)) + stT199 10 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 9
    simpa using h
  have hprev := st199_p9
  have hstep := st199_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p11 : ((17691468367549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT199 (i+1))
      = (∑ i ∈ Finset.range 10, stT199 (i+1)) + stT199 11 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 10
    simpa using h
  have hprev := st199_p10
  have hstep := st199_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p12 : ((37462041200571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT199 (i+1))
      = (∑ i ∈ Finset.range 11, stT199 (i+1)) + stT199 12 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 11
    simpa using h
  have hprev := st199_p11
  have hstep := st199_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p13 : ((35091740681947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT199 (i+1))
      = (∑ i ∈ Finset.range 12, stT199 (i+1)) + stT199 13 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 12
    simpa using h
  have hprev := st199_p12
  have hstep := st199_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p14 : ((7052645231663/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT199 (i+1))
      = (∑ i ∈ Finset.range 13, stT199 (i+1)) + stT199 14 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 13
    simpa using h
  have hprev := st199_p13
  have hstep := st199_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p15 : ((37694405403211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT199 (i+1))
      = (∑ i ∈ Finset.range 14, stT199 (i+1)) + stT199 15 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 14
    simpa using h
  have hprev := st199_p14
  have hstep := st199_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p16 : ((40188750403211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT199 (i+1))
      = (∑ i ∈ Finset.range 15, stT199 (i+1)) + stT199 16 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 15
    simpa using h
  have hprev := st199_p15
  have hstep := st199_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p17 : ((42232360219523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT199 (i+1))
      = (∑ i ∈ Finset.range 16, stT199 (i+1)) + stT199 17 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 16
    simpa using h
  have hprev := st199_p16
  have hstep := st199_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p18 : ((41787886964321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT199 (i+1))
      = (∑ i ∈ Finset.range 17, stT199 (i+1)) + stT199 18 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 17
    simpa using h
  have hprev := st199_p17
  have hstep := st199_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p19 : ((39698519272349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT199 (i+1))
      = (∑ i ∈ Finset.range 18, stT199 (i+1)) + stT199 19 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 18
    simpa using h
  have hprev := st199_p18
  have hstep := st199_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p20 : ((41793700634947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT199 (i+1))
      = (∑ i ∈ Finset.range 19, stT199 (i+1)) + stT199 20 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 19
    simpa using h
  have hprev := st199_p19
  have hstep := st199_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p21 : ((8008968256667/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT199 (i+1))
      = (∑ i ∈ Finset.range 20, stT199 (i+1)) + stT199 21 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 20
    simpa using h
  have hprev := st199_p20
  have hstep := st199_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p22 : ((41941781719543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT199 (i+1))
      = (∑ i ∈ Finset.range 21, stT199 (i+1)) + stT199 22 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 21
    simpa using h
  have hprev := st199_p21
  have hstep := st199_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p23 : ((39868009100373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT199 (i+1))
      = (∑ i ∈ Finset.range 22, stT199 (i+1)) + stT199 23 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 22
    simpa using h
  have hprev := st199_p22
  have hstep := st199_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p24 : ((40865126751499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT199 (i+1))
      = (∑ i ∈ Finset.range 23, stT199 (i+1)) + stT199 24 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 23
    simpa using h
  have hprev := st199_p23
  have hstep := st199_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p25 : ((42286842751499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT199 (i+1))
      = (∑ i ∈ Finset.range 24, stT199 (i+1)) + stT199 25 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 24
    simpa using h
  have hprev := st199_p24
  have hstep := st199_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p26 : ((40977523932411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT199 (i+1))
      = (∑ i ∈ Finset.range 25, stT199 (i+1)) + stT199 26 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 25
    simpa using h
  have hprev := st199_p25
  have hstep := st199_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p27 : ((39195459100423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT199 (i+1))
      = (∑ i ∈ Finset.range 26, stT199 (i+1)) + stT199 27 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 26
    simpa using h
  have hprev := st199_p26
  have hstep := st199_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p28 : ((7753079927921/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT199 (i+1))
      = (∑ i ∈ Finset.range 27, stT199 (i+1)) + stT199 28 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 27
    simpa using h
  have hprev := st199_p27
  have hstep := st199_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p29 : ((39607052445137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT199 (i+1))
      = (∑ i ∈ Finset.range 28, stT199 (i+1)) + stT199 29 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 28
    simpa using h
  have hprev := st199_p28
  have hstep := st199_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p30 : ((10268627051389/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT199 (i+1))
      = (∑ i ∈ Finset.range 29, stT199 (i+1)) + stT199 30 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 29
    simpa using h
  have hprev := st199_p29
  have hstep := st199_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p31 : ((5341510689907/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT199 (i+1))
      = (∑ i ∈ Finset.range 30, stT199 (i+1)) + stT199 31 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 30
    simpa using h
  have hprev := st199_p30
  have hstep := st199_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p32 : ((5548280975629/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT199 (i+1))
      = (∑ i ∈ Finset.range 31, stT199 (i+1)) + stT199 32 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 31
    simpa using h
  have hprev := st199_p31
  have hstep := st199_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p33 : ((114742202581/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT199 (i+1))
      = (∑ i ∈ Finset.range 32, stT199 (i+1)) + stT199 33 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 32
    simpa using h
  have hprev := st199_p32
  have hstep := st199_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p34 : ((4701260568379/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT199 (i+1))
      = (∑ i ∈ Finset.range 33, stT199 (i+1)) + stT199 34 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 33
    simpa using h
  have hprev := st199_p33
  have hstep := st199_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p35 : ((23668973012891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT199 (i+1))
      = (∑ i ∈ Finset.range 34, stT199 (i+1)) + stT199 35 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 34
    simpa using h
  have hprev := st199_p34
  have hstep := st199_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p36 : ((23281572935411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT199 (i+1))
      = (∑ i ∈ Finset.range 35, stT199 (i+1)) + stT199 36 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 35
    simpa using h
  have hprev := st199_p35
  have hstep := st199_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p37 : ((22486444019991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT199 (i+1))
      = (∑ i ∈ Finset.range 36, stT199 (i+1)) + stT199 37 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 36
    simpa using h
  have hprev := st199_p36
  have hstep := st199_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p38 : ((5469104545079/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT199 (i+1))
      = (∑ i ∈ Finset.range 37, stT199 (i+1)) + stT199 38 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 37
    simpa using h
  have hprev := st199_p37
  have hstep := st199_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p39 : ((5521114151959/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT199 (i+1))
      = (∑ i ∈ Finset.range 38, stT199 (i+1)) + stT199 39 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 38
    simpa using h
  have hprev := st199_p38
  have hstep := st199_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p40 : ((11436710376383/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT199 (i+1))
      = (∑ i ∈ Finset.range 39, stT199 (i+1)) + stT199 40 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 39
    simpa using h
  have hprev := st199_p39
  have hstep := st199_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p41 : ((461548671611/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT199 (i+1))
      = (∑ i ∈ Finset.range 40, stT199 (i+1)) + stT199 41 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 40
    simpa using h
  have hprev := st199_p40
  have hstep := st199_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p42 : ((5587992879087/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT199 (i+1))
      = (∑ i ∈ Finset.range 41, stT199 (i+1)) + stT199 42 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 41
    simpa using h
  have hprev := st199_p41
  have hstep := st199_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p43 : ((22113818265193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT199 (i+1))
      = (∑ i ∈ Finset.range 42, stT199 (i+1)) + stT199 43 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 42
    simpa using h
  have hprev := st199_p42
  have hstep := st199_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p44 : ((22855363955809/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT199 (i+1))
      = (∑ i ∈ Finset.range 43, stT199 (i+1)) + stT199 44 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 43
    simpa using h
  have hprev := st199_p43
  have hstep := st199_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p45 : ((22810495760677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT199 (i+1))
      = (∑ i ∈ Finset.range 44, stT199 (i+1)) + stT199 45 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 44
    simpa using h
  have hprev := st199_p44
  have hstep := st199_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p46 : ((22131091133987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT199 (i+1))
      = (∑ i ∈ Finset.range 45, stT199 (i+1)) + stT199 46 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 45
    simpa using h
  have hprev := st199_p45
  have hstep := st199_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p47 : ((11334968977161/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT199 (i+1))
      = (∑ i ∈ Finset.range 46, stT199 (i+1)) + stT199 47 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 46
    simpa using h
  have hprev := st199_p46
  have hstep := st199_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p48 : ((45650038432269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT199 (i+1))
      = (∑ i ∈ Finset.range 47, stT199 (i+1)) + stT199 48 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 47
    simpa using h
  have hprev := st199_p47
  have hstep := st199_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p49 : ((44330052189989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT199 (i+1))
      = (∑ i ∈ Finset.range 48, stT199 (i+1)) + stT199 49 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 48
    simpa using h
  have hprev := st199_p48
  have hstep := st199_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p50 : ((45580292849491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT199 (i+1))
      = (∑ i ∈ Finset.range 49, stT199 (i+1)) + stT199 50 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 49
    simpa using h
  have hprev := st199_p49
  have hstep := st199_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p51 : ((22592960954747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT199 (i+1))
      = (∑ i ∈ Finset.range 50, stT199 (i+1)) + stT199 51 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 50
    simpa using h
  have hprev := st199_p50
  have hstep := st199_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p52 : ((22299371900537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT199 (i+1))
      = (∑ i ∈ Finset.range 51, stT199 (i+1)) + stT199 52 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 51
    simpa using h
  have hprev := st199_p51
  have hstep := st199_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p53 : ((45814102637049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT199 (i+1))
      = (∑ i ∈ Finset.range 52, stT199 (i+1)) + stT199 53 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 52
    simpa using h
  have hprev := st199_p52
  have hstep := st199_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p54 : ((44459150692353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT199 (i+1))
      = (∑ i ∈ Finset.range 53, stT199 (i+1)) + stT199 54 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 53
    simpa using h
  have hprev := st199_p53
  have hstep := st199_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p55 : ((45569387370579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT199 (i+1))
      = (∑ i ∈ Finset.range 54, stT199 (i+1)) + stT199 55 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 54
    simpa using h
  have hprev := st199_p54
  have hstep := st199_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p56 : ((1122536960369/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT199 (i+1))
      = (∑ i ∈ Finset.range 55, stT199 (i+1)) + stT199 56 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 55
    simpa using h
  have hprev := st199_p55
  have hstep := st199_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p57 : ((5636223060017/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT199 (i+1))
      = (∑ i ∈ Finset.range 56, stT199 (i+1)) + stT199 57 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 56
    simpa using h
  have hprev := st199_p56
  have hstep := st199_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p58 : ((1133012442583/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT199 (i+1))
      = (∑ i ∈ Finset.range 57, stT199 (i+1)) + stT199 58 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 57
    simpa using h
  have hprev := st199_p57
  have hstep := st199_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p59 : ((1119240008651/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT199 (i+1))
      = (∑ i ∈ Finset.range 58, stT199 (i+1)) + stT199 59 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 58
    simpa using h
  have hprev := st199_p58
  have hstep := st199_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p60 : ((4554039476871/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT199 (i+1))
      = (∑ i ∈ Finset.range 59, stT199 (i+1)) + stT199 60 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 59
    simpa using h
  have hprev := st199_p59
  have hstep := st199_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p61 : ((2231647942367/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT199 (i+1))
      = (∑ i ∈ Finset.range 60, stT199 (i+1)) + stT199 61 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 60
    simpa using h
  have hprev := st199_p60
  have hstep := st199_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p62 : ((2280662360961/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT199 (i+1))
      = (∑ i ∈ Finset.range 61, stT199 (i+1)) + stT199 62 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 61
    simpa using h
  have hprev := st199_p61
  have hstep := st199_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p63 : ((892150046337/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT199 (i+1))
      = (∑ i ∈ Finset.range 62, stT199 (i+1)) + stT199 63 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 62
    simpa using h
  have hprev := st199_p62
  have hstep := st199_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p64 : ((911988421337/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT199 (i+1))
      = (∑ i ∈ Finset.range 63, stT199 (i+1)) + stT199 64 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 63
    simpa using h
  have hprev := st199_p63
  have hstep := st199_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p65 : ((22329515072367/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT199 (i+1))
      = (∑ i ∈ Finset.range 64, stT199 (i+1)) + stT199 65 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 64
    simpa using h
  have hprev := st199_p64
  have hstep := st199_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p66 : ((22752172781633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT199 (i+1))
      = (∑ i ∈ Finset.range 65, stT199 (i+1)) + stT199 66 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 65
    simpa using h
  have hprev := st199_p65
  have hstep := st199_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p67 : ((44806409535191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT199 (i+1))
      = (∑ i ∈ Finset.range 66, stT199 (i+1)) + stT199 67 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 66
    simpa using h
  have hprev := st199_p66
  have hstep := st199_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p68 : ((45294868957523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT199 (i+1))
      = (∑ i ∈ Finset.range 67, stT199 (i+1)) + stT199 68 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 67
    simpa using h
  have hprev := st199_p67
  have hstep := st199_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p69 : ((22540712980341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT199 (i+1))
      = (∑ i ∈ Finset.range 68, stT199 (i+1)) + stT199 69 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 68
    simpa using h
  have hprev := st199_p68
  have hstep := st199_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p70 : ((11240495486449/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT199 (i+1))
      = (∑ i ∈ Finset.range 69, stT199 (i+1)) + stT199 70 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 69
    simpa using h
  have hprev := st199_p69
  have hstep := st199_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p71 : ((45444661206649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT199 (i+1))
      = (∑ i ∈ Finset.range 70, stT199 (i+1)) + stT199 71 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 70
    simpa using h
  have hprev := st199_p70
  have hstep := st199_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p72 : ((44618105922889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT199 (i+1))
      = (∑ i ∈ Finset.range 71, stT199 (i+1)) + stT199 72 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 71
    simpa using h
  have hprev := st199_p71
  have hstep := st199_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p73 : ((9139500216377/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT199 (i+1))
      = (∑ i ∈ Finset.range 72, stT199 (i+1)) + stT199 73 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 72
    simpa using h
  have hprev := st199_p72
  have hstep := st199_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p74 : ((11133942888649/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT199 (i+1))
      = (∑ i ∈ Finset.range 73, stT199 (i+1)) + stT199 74 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 73
    simpa using h
  have hprev := st199_p73
  have hstep := st199_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p75 : ((2846550312181/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT199 (i+1))
      = (∑ i ∈ Finset.range 74, stT199 (i+1)) + stT199 75 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 74
    simpa using h
  have hprev := st199_p74
  have hstep := st199_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p76 : ((2246899780779/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT199 (i+1))
      = (∑ i ∈ Finset.range 75, stT199 (i+1)) + stT199 76 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 75
    simpa using h
  have hprev := st199_p75
  have hstep := st199_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p77 : ((8991490418349/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT199 (i+1))
      = (∑ i ∈ Finset.range 76, stT199 (i+1)) + stT199 77 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 76
    simpa using h
  have hprev := st199_p76
  have hstep := st199_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p78 : ((5694458641429/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT199 (i+1))
      = (∑ i ∈ Finset.range 77, stT199 (i+1)) + stT199 78 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 77
    simpa using h
  have hprev := st199_p77
  have hstep := st199_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p79 : ((5565335666933/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT199 (i+1))
      = (∑ i ∈ Finset.range 78, stT199 (i+1)) + stT199 79 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 78
    simpa using h
  have hprev := st199_p78
  have hstep := st199_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p80 : ((45611006608489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT199 (i+1))
      = (∑ i ∈ Finset.range 79, stT199 (i+1)) + stT199 80 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 79
    simpa using h
  have hprev := st199_p79
  have hstep := st199_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p81 : ((8984116322341/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT199 (i+1))
      = (∑ i ∈ Finset.range 80, stT199 (i+1)) + stT199 81 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 80
    simpa using h
  have hprev := st199_p80
  have hstep := st199_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p82 : ((44888062818453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT199 (i+1))
      = (∑ i ∈ Finset.range 81, stT199 (i+1)) + stT199 82 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 81
    simpa using h
  have hprev := st199_p81
  have hstep := st199_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p83 : ((45643270150787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT199 (i+1))
      = (∑ i ∈ Finset.range 82, stT199 (i+1)) + stT199 83 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 82
    simpa using h
  have hprev := st199_p82
  have hstep := st199_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p84 : ((44553693492617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT199 (i+1))
      = (∑ i ∈ Finset.range 83, stT199 (i+1)) + stT199 84 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 83
    simpa using h
  have hprev := st199_p83
  have hstep := st199_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p85 : ((45359782996673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT199 (i+1))
      = (∑ i ∈ Finset.range 84, stT199 (i+1)) + stT199 85 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 84
    simpa using h
  have hprev := st199_p84
  have hstep := st199_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p86 : ((1813362983153/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT199 (i+1))
      = (∑ i ∈ Finset.range 85, stT199 (i+1)) + stT199 86 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 85
    simpa using h
  have hprev := st199_p85
  have hstep := st199_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p87 : ((11138053950857/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT199 (i+1))
      = (∑ i ∈ Finset.range 86, stT199 (i+1)) + stT199 87 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 86
    simpa using h
  have hprev := st199_p86
  have hstep := st199_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p88 : ((45611286585919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT199 (i+1))
      = (∑ i ∈ Finset.range 87, stT199 (i+1)) + stT199 88 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 87
    simpa using h
  have hprev := st199_p87
  have hstep := st199_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p89 : ((9008893075079/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT199 (i+1))
      = (∑ i ∈ Finset.range 88, stT199 (i+1)) + stT199 89 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 88
    simpa using h
  have hprev := st199_p88
  have hstep := st199_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p90 : ((44679040846899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT199 (i+1))
      = (∑ i ∈ Finset.range 89, stT199 (i+1)) + stT199 90 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 89
    simpa using h
  have hprev := st199_p89
  have hstep := st199_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p91 : ((9137624643687/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT199 (i+1))
      = (∑ i ∈ Finset.range 90, stT199 (i+1)) + stT199 91 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 90
    simpa using h
  have hprev := st199_p90
  have hstep := st199_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p92 : ((11221422296311/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT199 (i+1))
      = (∑ i ∈ Finset.range 91, stT199 (i+1)) + stT199 92 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 91
    simpa using h
  have hprev := st199_p91
  have hstep := st199_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p93 : ((11192439747149/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT199 (i+1))
      = (∑ i ∈ Finset.range 92, stT199 (i+1)) + stT199 93 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 92
    simpa using h
  have hprev := st199_p92
  have hstep := st199_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p94 : ((5712552301033/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT199 (i+1))
      = (∑ i ∈ Finset.range 93, stT199 (i+1)) + stT199 94 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 93
    simpa using h
  have hprev := st199_p93
  have hstep := st199_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p95 : ((44847935535101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT199 (i+1))
      = (∑ i ∈ Finset.range 94, stT199 (i+1)) + stT199 95 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 94
    simpa using h
  have hprev := st199_p94
  have hstep := st199_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p96 : ((44769194624951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT199 (i+1))
      = (∑ i ∈ Finset.range 95, stT199 (i+1)) + stT199 96 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 95
    simpa using h
  have hprev := st199_p95
  have hstep := st199_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p97 : ((9139724206217/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT199 (i+1))
      = (∑ i ∈ Finset.range 96, stT199 (i+1)) + stT199 97 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 96
    simpa using h
  have hprev := st199_p96
  have hstep := st199_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p98 : ((8983427273139/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT199 (i+1))
      = (∑ i ∈ Finset.range 97, stT199 (i+1)) + stT199 98 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 97
    simpa using h
  have hprev := st199_p97
  have hstep := st199_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p99 : ((44681317264489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT199 (i+1))
      = (∑ i ∈ Finset.range 98, stT199 (i+1)) + stT199 99 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 98
    simpa using h
  have hprev := st199_p98
  have hstep := st199_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p100 : ((9132562056599/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT199 (i+1))
      = (∑ i ∈ Finset.range 99, stT199 (i+1)) + stT199 100 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 99
    simpa using h
  have hprev := st199_p99
  have hstep := st199_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p101 : ((45099480464713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT199 (i+1))
      = (∑ i ∈ Finset.range 100, stT199 (i+1)) + stT199 101 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 100
    simpa using h
  have hprev := st199_p100
  have hstep := st199_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p102 : ((1782297710197/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT199 (i+1))
      = (∑ i ∈ Finset.range 101, stT199 (i+1)) + stT199 102 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 101
    simpa using h
  have hprev := st199_p101
  have hstep := st199_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p103 : ((11380342355929/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT199 (i+1))
      = (∑ i ∈ Finset.range 102, stT199 (i+1)) + stT199 103 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 102
    simpa using h
  have hprev := st199_p102
  have hstep := st199_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p104 : ((45381227728939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT199 (i+1))
      = (∑ i ∈ Finset.range 103, stT199 (i+1)) + stT199 104 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 103
    simpa using h
  have hprev := st199_p103
  have hstep := st199_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p105 : ((44514163112063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT199 (i+1))
      = (∑ i ∈ Finset.range 104, stT199 (i+1)) + stT199 105 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 104
    simpa using h
  have hprev := st199_p104
  have hstep := st199_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p106 : ((45205679180663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT199 (i+1))
      = (∑ i ∈ Finset.range 105, stT199 (i+1)) + stT199 106 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 105
    simpa using h
  have hprev := st199_p105
  have hstep := st199_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p107 : ((45652619601447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT199 (i+1))
      = (∑ i ∈ Finset.range 106, stT199 (i+1)) + stT199 107 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 106
    simpa using h
  have hprev := st199_p106
  have hstep := st199_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p108 : ((44709555886387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT199 (i+1))
      = (∑ i ∈ Finset.range 107, stT199 (i+1)) + stT199 108 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 107
    simpa using h
  have hprev := st199_p107
  have hstep := st199_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p109 : ((44769832834393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT199 (i+1))
      = (∑ i ∈ Finset.range 108, stT199 (i+1)) + stT199 109 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 108
    simpa using h
  have hprev := st199_p108
  have hstep := st199_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p110 : ((45677916717427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT199 (i+1))
      = (∑ i ∈ Finset.range 109, stT199 (i+1)) + stT199 110 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 109
    simpa using h
  have hprev := st199_p109
  have hstep := st199_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p111 : ((45190095065011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT199 (i+1))
      = (∑ i ∈ Finset.range 110, stT199 (i+1)) + stT199 111 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 110
    simpa using h
  have hprev := st199_p110
  have hstep := st199_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p112 : ((44501042556723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT199 (i+1))
      = (∑ i ∈ Finset.range 111, stT199 (i+1)) + stT199 112 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 111
    simpa using h
  have hprev := st199_p111
  have hstep := st199_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p113 : ((45267174331923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT199 (i+1))
      = (∑ i ∈ Finset.range 112, stT199 (i+1)) + stT199 113 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 112
    simpa using h
  have hprev := st199_p112
  have hstep := st199_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p114 : ((22831537683759/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT199 (i+1))
      = (∑ i ∈ Finset.range 113, stT199 (i+1)) + stT199 114 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 113
    simpa using h
  have hprev := st199_p113
  have hstep := st199_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p115 : ((1398878984139/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT199 (i+1))
      = (∑ i ∈ Finset.range 114, stT199 (i+1)) + stT199 115 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 114
    simpa using h
  have hprev := st199_p114
  have hstep := st199_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p116 : ((2790973586839/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT199 (i+1))
      = (∑ i ∈ Finset.range 115, stT199 (i+1)) + stT199 116 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 115
    simpa using h
  have hprev := st199_p115
  have hstep := st199_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p117 : ((11394960410481/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT199 (i+1))
      = (∑ i ∈ Finset.range 116, stT199 (i+1)) + stT199 117 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 116
    simpa using h
  have hprev := st199_p116
  have hstep := st199_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p118 : ((45448526221049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT199 (i+1))
      = (∑ i ∈ Finset.range 117, stT199 (i+1)) + stT199 118 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 117
    simpa using h
  have hprev := st199_p117
  have hstep := st199_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p119 : ((5570080685939/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT199 (i+1))
      = (∑ i ∈ Finset.range 118, stT199 (i+1)) + stT199 119 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 118
    simpa using h
  have hprev := st199_p118
  have hstep := st199_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p120 : ((5608784548199/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT199 (i+1))
      = (∑ i ∈ Finset.range 119, stT199 (i+1)) + stT199 120 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 119
    simpa using h
  have hprev := st199_p119
  have hstep := st199_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p121 : ((11424445707703/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT199 (i+1))
      = (∑ i ∈ Finset.range 120, stT199 (i+1)) + stT199 121 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 120
    simpa using h
  have hprev := st199_p120
  have hstep := st199_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p122 : ((22634293955987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT199 (i+1))
      = (∑ i ∈ Finset.range 121, stT199 (i+1)) + stT199 122 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 121
    simpa using h
  have hprev := st199_p121
  have hstep := st199_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p123 : ((695292041731/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT199 (i+1))
      = (∑ i ∈ Finset.range 122, stT199 (i+1)) + stT199 123 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 122
    simpa using h
  have hprev := st199_p122
  have hstep := st199_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p124 : ((4499684455153/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT199 (i+1))
      = (∑ i ∈ Finset.range 123, stT199 (i+1)) + stT199 124 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 123
    simpa using h
  have hprev := st199_p123
  have hstep := st199_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p125 : ((4572698320017/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT199 (i+1))
      = (∑ i ∈ Finset.range 124, stT199 (i+1)) + stT199 125 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 124
    simpa using h
  have hprev := st199_p124
  have hstep := st199_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p126 : ((45201673097181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT199 (i+1))
      = (∑ i ∈ Finset.range 125, stT199 (i+1)) + stT199 126 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 125
    simpa using h
  have hprev := st199_p125
  have hstep := st199_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p127 : ((695095873757/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT199 (i+1))
      = (∑ i ∈ Finset.range 126, stT199 (i+1)) + stT199 127 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 126
    simpa using h
  have hprev := st199_p126
  have hstep := st199_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p128 : ((22500869230951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT199 (i+1))
      = (∑ i ∈ Finset.range 127, stT199 (i+1)) + stT199 128 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 127
    simpa using h
  have hprev := st199_p127
  have hstep := st199_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p129 : ((11431996392113/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT199 (i+1))
      = (∑ i ∈ Finset.range 128, stT199 (i+1)) + stT199 129 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 128
    simpa using h
  have hprev := st199_p128
  have hstep := st199_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p130 : ((2262856909921/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT199 (i+1))
      = (∑ i ∈ Finset.range 129, stT199 (i+1)) + stT199 130 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 129
    simpa using h
  have hprev := st199_p129
  have hstep := st199_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p131 : ((556240076257/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT199 (i+1))
      = (∑ i ∈ Finset.range 130, stT199 (i+1)) + stT199 131 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 130
    simpa using h
  have hprev := st199_p130
  have hstep := st199_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p132 : ((2805507706961/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT199 (i+1))
      = (∑ i ∈ Finset.range 131, stT199 (i+1)) + stT199 132 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 131
    simpa using h
  have hprev := st199_p131
  have hstep := st199_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p133 : ((11422156983717/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT199 (i+1))
      = (∑ i ∈ Finset.range 132, stT199 (i+1)) + stT199 133 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 132
    simpa using h
  have hprev := st199_p132
  have hstep := st199_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p134 : ((45421587885719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT199 (i+1))
      = (∑ i ∈ Finset.range 133, stT199 (i+1)) + stT199 134 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 133
    simpa using h
  have hprev := st199_p133
  have hstep := st199_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p135 : ((44582188425797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT199 (i+1))
      = (∑ i ∈ Finset.range 134, stT199 (i+1)) + stT199 135 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 134
    simpa using h
  have hprev := st199_p134
  have hstep := st199_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p136 : ((44685494774497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT199 (i+1))
      = (∑ i ∈ Finset.range 135, stT199 (i+1)) + stT199 136 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 135
    simpa using h
  have hprev := st199_p135
  have hstep := st199_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p137 : ((2276989128579/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT199 (i+1))
      = (∑ i ∈ Finset.range 136, stT199 (i+1)) + stT199 137 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 136
    simpa using h
  have hprev := st199_p136
  have hstep := st199_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p138 : ((2281896832233/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT199 (i+1))
      = (∑ i ∈ Finset.range 137, stT199 (i+1)) + stT199 138 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 137
    simpa using h
  have hprev := st199_p137
  have hstep := st199_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p139 : ((44815982978619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT199 (i+1))
      = (∑ i ∈ Finset.range 138, stT199 (i+1)) + stT199 139 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 138
    simpa using h
  have hprev := st199_p138
  have hstep := st199_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p140 : ((44491627702409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT199 (i+1))
      = (∑ i ∈ Finset.range 139, stT199 (i+1)) + stT199 140 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 139
    simpa using h
  have hprev := st199_p139
  have hstep := st199_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p141 : ((22605150840319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT199 (i+1))
      = (∑ i ∈ Finset.range 140, stT199 (i+1)) + stT199 141 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 140
    simpa using h
  have hprev := st199_p140
  have hstep := st199_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p142 : ((45758977519601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT199 (i+1))
      = (∑ i ∈ Finset.range 141, stT199 (i+1)) + stT199 142 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 141
    simpa using h
  have hprev := st199_p141
  have hstep := st199_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p143 : ((9046127503943/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT199 (i+1))
      = (∑ i ∈ Finset.range 142, stT199 (i+1)) + stT199 143 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 142
    simpa using h
  have hprev := st199_p142
  have hstep := st199_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p144 : ((8899836553577/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT199 (i+1))
      = (∑ i ∈ Finset.range 143, stT199 (i+1)) + stT199 144 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 143
    simpa using h
  have hprev := st199_p143
  have hstep := st199_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p145 : ((44749430945791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT199 (i+1))
      = (∑ i ∈ Finset.range 144, stT199 (i+1)) + stT199 145 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 144
    simpa using h
  have hprev := st199_p144
  have hstep := st199_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p146 : ((45572603293411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT199 (i+1))
      = (∑ i ∈ Finset.range 145, stT199 (i+1)) + stT199 146 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 145
    simpa using h
  have hprev := st199_p145
  have hstep := st199_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p147 : ((9132519798603/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT199 (i+1))
      = (∑ i ∈ Finset.range 146, stT199 (i+1)) + stT199 147 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 146
    simpa using h
  have hprev := st199_p146
  have hstep := st199_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p148 : ((1795407494313/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT199 (i+1))
      = (∑ i ∈ Finset.range 147, stT199 (i+1)) + stT199 148 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 147
    simpa using h
  have hprev := st199_p147
  have hstep := st199_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p149 : ((1777951298857/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT199 (i+1))
      = (∑ i ∈ Finset.range 148, stT199 (i+1)) + stT199 149 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 148
    simpa using h
  have hprev := st199_p148
  have hstep := st199_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p150 : ((45016759134417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT199 (i+1))
      = (∑ i ∈ Finset.range 149, stT199 (i+1)) + stT199 150 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 149
    simpa using h
  have hprev := st199_p149
  have hstep := st199_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p151 : ((9144519794001/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT199 (i+1))
      = (∑ i ∈ Finset.range 150, stT199 (i+1)) + stT199 151 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 150
    simpa using h
  have hprev := st199_p150
  have hstep := st199_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p152 : ((45511229902961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT199 (i+1))
      = (∑ i ∈ Finset.range 151, stT199 (i+1)) + stT199 152 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 151
    simpa using h
  have hprev := st199_p151
  have hstep := st199_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p153 : ((4470273890567/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT199 (i+1))
      = (∑ i ∈ Finset.range 152, stT199 (i+1)) + stT199 153 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 152
    simpa using h
  have hprev := st199_p152
  have hstep := st199_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p154 : ((8896518418237/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT199 (i+1))
      = (∑ i ∈ Finset.range 153, stT199 (i+1)) + stT199 154 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 153
    simpa using h
  have hprev := st199_p153
  have hstep := st199_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p155 : ((45163326619437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT199 (i+1))
      = (∑ i ∈ Finset.range 154, stT199 (i+1)) + stT199 155 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 154
    simpa using h
  have hprev := st199_p154
  have hstep := st199_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p156 : ((45765043608237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT199 (i+1))
      = (∑ i ∈ Finset.range 155, stT199 (i+1)) + stT199 156 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 155
    simpa using h
  have hprev := st199_p155
  have hstep := st199_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p157 : ((22719389229927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT199 (i+1))
      = (∑ i ∈ Finset.range 156, stT199 (i+1)) + stT199 157 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 156
    simpa using h
  have hprev := st199_p156
  have hstep := st199_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p158 : ((2232416277777/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT199 (i+1))
      = (∑ i ∈ Finset.range 157, stT199 (i+1)) + stT199 158 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 157
    simpa using h
  have hprev := st199_p157
  have hstep := st199_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p159 : ((2780598919741/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT199 (i+1))
      = (∑ i ∈ Finset.range 158, stT199 (i+1)) + stT199 159 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 158
    simpa using h
  have hprev := st199_p158
  have hstep := st199_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p160 : ((45173790934303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT199 (i+1))
      = (∑ i ∈ Finset.range 159, stT199 (i+1)) + stT199 160 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 159
    simpa using h
  have hprev := st199_p159
  have hstep := st199_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p161 : ((45768720987323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT199 (i+1))
      = (∑ i ∈ Finset.range 160, stT199 (i+1)) + stT199 161 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 160
    simpa using h
  have hprev := st199_p160
  have hstep := st199_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p162 : ((5684962331681/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT199 (i+1))
      = (∑ i ∈ Finset.range 161, stT199 (i+1)) + stT199 162 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 161
    simpa using h
  have hprev := st199_p161
  have hstep := st199_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p163 : ((44696762706763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT199 (i+1))
      = (∑ i ∈ Finset.range 162, stT199 (i+1)) + stT199 163 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 162
    simpa using h
  have hprev := st199_p162
  have hstep := st199_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p164 : ((44448729039341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT199 (i+1))
      = (∑ i ∈ Finset.range 163, stT199 (i+1)) + stT199 164 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 163
    simpa using h
  have hprev := st199_p163
  have hstep := st199_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p165 : ((45051938094167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT199 (i+1))
      = (∑ i ∈ Finset.range 164, stT199 (i+1)) + stT199 165 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 164
    simpa using h
  have hprev := st199_p164
  have hstep := st199_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p166 : ((45726166404617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT199 (i+1))
      = (∑ i ∈ Finset.range 165, stT199 (i+1)) + stT199 166 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 165
    simpa using h
  have hprev := st199_p165
  have hstep := st199_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p167 : ((45616173513609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT199 (i+1))
      = (∑ i ∈ Finset.range 166, stT199 (i+1)) + stT199 167 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 166
    simpa using h
  have hprev := st199_p166
  have hstep := st199_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p168 : ((4486676279021/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT199 (i+1))
      = (∑ i ∈ Finset.range 167, stT199 (i+1)) + stT199 168 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 167
    simpa using h
  have hprev := st199_p167
  have hstep := st199_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p169 : ((22206785942511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT199 (i+1))
      = (∑ i ∈ Finset.range 168, stT199 (i+1)) + stT199 169 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 168
    simpa using h
  have hprev := st199_p168
  have hstep := st199_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p170 : ((22405274691783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT199 (i+1))
      = (∑ i ∈ Finset.range 169, stT199 (i+1)) + stT199 170 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 169
    simpa using h
  have hprev := st199_p169
  have hstep := st199_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p171 : ((5695962399363/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT199 (i+1))
      = (∑ i ∈ Finset.range 170, stT199 (i+1)) + stT199 171 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 170
    simpa using h
  have hprev := st199_p170
  have hstep := st199_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p172 : ((5721379307691/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT199 (i+1))
      = (∑ i ∈ Finset.range 171, stT199 (i+1)) + stT199 172 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 171
    simpa using h
  have hprev := st199_p171
  have hstep := st199_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p173 : ((90366517751/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT199 (i+1))
      = (∑ i ∈ Finset.range 172, stT199 (i+1)) + stT199 173 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 172
    simpa using h
  have hprev := st199_p172
  have hstep := st199_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p174 : ((22251930582543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT199 (i+1))
      = (∑ i ∈ Finset.range 173, stT199 (i+1)) + stT199 174 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 173
    simpa using h
  have hprev := st199_p173
  have hstep := st199_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p175 : ((22263031763187/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT199 (i+1))
      = (∑ i ∈ Finset.range 174, stT199 (i+1)) + stT199 175 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 174
    simpa using h
  have hprev := st199_p174
  have hstep := st199_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p176 : ((565226122141/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT199 (i+1))
      = (∑ i ∈ Finset.range 175, stT199 (i+1)) + stT199 176 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 175
    simpa using h
  have hprev := st199_p175
  have hstep := st199_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p177 : ((22891565691837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT199 (i+1))
      = (∑ i ∈ Finset.range 176, stT199 (i+1)) + stT199 177 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 176
    simpa using h
  have hprev := st199_p176
  have hstep := st199_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p178 : ((22791457073619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT199 (i+1))
      = (∑ i ∈ Finset.range 177, stT199 (i+1)) + stT199 178 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 177
    simpa using h
  have hprev := st199_p177
  have hstep := st199_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p179 : ((22424137499497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT199 (i+1))
      = (∑ i ∈ Finset.range 178, stT199 (i+1)) + stT199 179 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 178
    simpa using h
  have hprev := st199_p178
  have hstep := st199_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p180 : ((22199246823787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT199 (i+1))
      = (∑ i ∈ Finset.range 179, stT199 (i+1)) + stT199 180 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 179
    simpa using h
  have hprev := st199_p179
  have hstep := st199_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p181 : ((2795308669347/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT199 (i+1))
      = (∑ i ∈ Finset.range 180, stT199 (i+1)) + stT199 181 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 180
    simpa using h
  have hprev := st199_p180
  have hstep := st199_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p182 : ((9093201517209/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT199 (i+1))
      = (∑ i ∈ Finset.range 181, stT199 (i+1)) + stT199 182 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 181
    simpa using h
  have hprev := st199_p181
  have hstep := st199_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p183 : ((11455095130893/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT199 (i+1))
      = (∑ i ∈ Finset.range 182, stT199 (i+1)) + stT199 183 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 182
    simpa using h
  have hprev := st199_p182
  have hstep := st199_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p184 : ((22706795128601/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT199 (i+1))
      = (∑ i ∈ Finset.range 183, stT199 (i+1)) + stT199 184 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 183
    simpa using h
  have hprev := st199_p183
  have hstep := st199_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p185 : ((44681465365847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT199 (i+1))
      = (∑ i ∈ Finset.range 184, stT199 (i+1)) + stT199 185 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 184
    simpa using h
  have hprev := st199_p184
  have hstep := st199_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p186 : ((44392003590419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT199 (i+1))
      = (∑ i ∈ Finset.range 185, stT199 (i+1)) + stT199 186 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 185
    simpa using h
  have hprev := st199_p185
  have hstep := st199_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p187 : ((44841056518731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT199 (i+1))
      = (∑ i ∈ Finset.range 186, stT199 (i+1)) + stT199 187 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 186
    simpa using h
  have hprev := st199_p186
  have hstep := st199_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p188 : ((45561956826531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT199 (i+1))
      = (∑ i ∈ Finset.range 187, stT199 (i+1)) + stT199 188 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 187
    simpa using h
  have hprev := st199_p187
  have hstep := st199_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p189 : ((9164078676999/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT199 (i+1))
      = (∑ i ∈ Finset.range 188, stT199 (i+1)) + stT199 189 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 188
    simpa using h
  have hprev := st199_p188
  have hstep := st199_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p190 : ((9072066429089/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT199 (i+1))
      = (∑ i ∈ Finset.range 189, stT199 (i+1)) + stT199 190 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 189
    simpa using h
  have hprev := st199_p189
  have hstep := st199_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p191 : ((4464604133627/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT199 (i+1))
      = (∑ i ∈ Finset.range 190, stT199 (i+1)) + stT199 191 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 190
    simpa using h
  have hprev := st199_p190
  have hstep := st199_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p192 : ((22192192706651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT199 (i+1))
      = (∑ i ∈ Finset.range 191, stT199 (i+1)) + stT199 192 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 191
    simpa using h
  have hprev := st199_p191
  have hstep := st199_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p193 : ((22413636593251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT199 (i+1))
      = (∑ i ∈ Finset.range 192, stT199 (i+1)) + stT199 193 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 192
    simpa using h
  have hprev := st199_p192
  have hstep := st199_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p194 : ((910799888017/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT199 (i+1))
      = (∑ i ∈ Finset.range 193, stT199 (i+1)) + stT199 194 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 193
    simpa using h
  have hprev := st199_p193
  have hstep := st199_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p195 : ((4583667326991/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT199 (i+1))
      = (∑ i ∈ Finset.range 194, stT199 (i+1)) + stT199 195 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 194
    simpa using h
  have hprev := st199_p194
  have hstep := st199_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p196 : ((22719414412529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT199 (i+1))
      = (∑ i ∈ Finset.range 195, stT199 (i+1)) + stT199 196 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 195
    simpa using h
  have hprev := st199_p195
  have hstep := st199_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p197 : ((559083765451/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT199 (i+1))
      = (∑ i ∈ Finset.range 196, stT199 (i+1)) + stT199 197 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 196
    simpa using h
  have hprev := st199_p196
  have hstep := st199_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p198 : ((4436704465181/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT199 (i+1))
      = (∑ i ∈ Finset.range 197, stT199 (i+1)) + stT199 198 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 197
    simpa using h
  have hprev := st199_p197
  have hstep := st199_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p199 : ((44689279979099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT199 (i+1))
      = (∑ i ∈ Finset.range 198, stT199 (i+1)) + stT199 199 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 198
    simpa using h
  have hprev := st199_p198
  have hstep := st199_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p200 : ((45392721048701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT199 (i+1))
      = (∑ i ∈ Finset.range 199, stT199 (i+1)) + stT199 200 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 199
    simpa using h
  have hprev := st199_p199
  have hstep := st199_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p201 : ((45835997935331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT199 (i+1))
      = (∑ i ∈ Finset.range 200, stT199 (i+1)) + stT199 201 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 200
    simpa using h
  have hprev := st199_p200
  have hstep := st199_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p202 : ((45622698683641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT199 (i+1))
      = (∑ i ∈ Finset.range 201, stT199 (i+1)) + stT199 202 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 201
    simpa using h
  have hprev := st199_p201
  have hstep := st199_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p203 : ((2809259906773/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT199 (i+1))
      = (∑ i ∈ Finset.range 202, stT199 (i+1)) + stT199 203 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 202
    simpa using h
  have hprev := st199_p202
  have hstep := st199_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p204 : ((8882323471083/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT199 (i+1))
      = (∑ i ∈ Finset.range 203, stT199 (i+1)) + stT199 204 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 203
    simpa using h
  have hprev := st199_p203
  have hstep := st199_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p205 : ((1779254419197/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT199 (i+1))
      = (∑ i ∈ Finset.range 204, stT199 (i+1)) + stT199 205 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 204
    simpa using h
  have hprev := st199_p204
  have hstep := st199_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p206 : ((45091980068057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT199 (i+1))
      = (∑ i ∈ Finset.range 205, stT199 (i+1)) + stT199 206 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 205
    simpa using h
  have hprev := st199_p205
  have hstep := st199_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p207 : ((45714334387833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT199 (i+1))
      = (∑ i ∈ Finset.range 206, stT199 (i+1)) + stT199 207 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 206
    simpa using h
  have hprev := st199_p206
  have hstep := st199_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p208 : ((45818208896583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT199 (i+1))
      = (∑ i ∈ Finset.range 207, stT199 (i+1)) + stT199 208 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 207
    simpa using h
  have hprev := st199_p207
  have hstep := st199_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p209 : ((22660018222649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT199 (i+1))
      = (∑ i ∈ Finset.range 208, stT199 (i+1)) + stT199 209 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 208
    simpa using h
  have hprev := st199_p208
  have hstep := st199_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p210 : ((1116036794383/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT199 (i+1))
      = (∑ i ∈ Finset.range 209, stT199 (i+1)) + stT199 210 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 209
    simpa using h
  have hprev := st199_p209
  have hstep := st199_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p211 : ((22173382479213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT199 (i+1))
      = (∑ i ∈ Finset.range 210, stT199 (i+1)) + stT199 211 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 210
    simpa using h
  have hprev := st199_p210
  have hstep := st199_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p212 : ((1396098149721/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT199 (i+1))
      = (∑ i ∈ Finset.range 211, stT199 (i+1)) + stT199 212 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 211
    simpa using h
  have hprev := st199_p211
  have hstep := st199_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p213 : ((5669248850259/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT199 (i+1))
      = (∑ i ∈ Finset.range 212, stT199 (i+1)) + stT199 213 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 212
    simpa using h
  have hprev := st199_p212
  have hstep := st199_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p214 : ((45832003335777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT199 (i+1))
      = (∑ i ∈ Finset.range 213, stT199 (i+1)) + stT199 214 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 213
    simpa using h
  have hprev := st199_p213
  have hstep := st199_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p215 : ((1428994878171/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT199 (i+1))
      = (∑ i ∈ Finset.range 214, stT199 (i+1)) + stT199 215 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 214
    simpa using h
  have hprev := st199_p214
  have hstep := st199_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p216 : ((22564379055309/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT199 (i+1))
      = (∑ i ∈ Finset.range 215, stT199 (i+1)) + stT199 216 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 215
    simpa using h
  have hprev := st199_p215
  have hstep := st199_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p217 : ((44510295694523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT199 (i+1))
      = (∑ i ∈ Finset.range 216, stT199 (i+1)) + stT199 217 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 216
    simpa using h
  have hprev := st199_p216
  have hstep := st199_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p218 : ((44355353653589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT199 (i+1))
      = (∑ i ∈ Finset.range 217, stT199 (i+1)) + stT199 218 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 217
    simpa using h
  have hprev := st199_p217
  have hstep := st199_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p219 : ((22390109956827/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT199 (i+1))
      = (∑ i ∈ Finset.range 218, stT199 (i+1)) + stT199 219 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 218
    simpa using h
  have hprev := st199_p218
  have hstep := st199_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p220 : ((45454300928829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT199 (i+1))
      = (∑ i ∈ Finset.range 219, stT199 (i+1)) + stT199 220 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 219
    simpa using h
  have hprev := st199_p219
  have hstep := st199_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p221 : ((45862686826749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT199 (i+1))
      = (∑ i ∈ Finset.range 220, stT199 (i+1)) + stT199 221 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 220
    simpa using h
  have hprev := st199_p220
  have hstep := st199_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p222 : ((9139851750987/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT199 (i+1))
      = (∑ i ∈ Finset.range 221, stT199 (i+1)) + stT199 222 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 221
    simpa using h
  have hprev := st199_p221
  have hstep := st199_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p223 : ((9018134425897/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT199 (i+1))
      = (∑ i ∈ Finset.range 222, stT199 (i+1)) + stT199 223 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 222
    simpa using h
  have hprev := st199_p222
  have hstep := st199_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p224 : ((44491907926847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT199 (i+1))
      = (∑ i ∈ Finset.range 223, stT199 (i+1)) + stT199 224 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 223
    simpa using h
  have hprev := st199_p223
  have hstep := st199_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p225 : ((44343479852633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT199 (i+1))
      = (∑ i ∈ Finset.range 224, stT199 (i+1)) + stT199 225 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 224
    simpa using h
  have hprev := st199_p224
  have hstep := st199_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p226 : ((44750235555353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT199 (i+1))
      = (∑ i ∈ Finset.range 225, stT199 (i+1)) + stT199 226 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 225
    simpa using h
  have hprev := st199_p225
  have hstep := st199_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p227 : ((2838346068203/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT199 (i+1))
      = (∑ i ∈ Finset.range 226, stT199 (i+1)) + stT199 227 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 226
    simpa using h
  have hprev := st199_p226
  have hstep := st199_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p228 : ((22927641210417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT199 (i+1))
      = (∑ i ∈ Finset.range 227, stT199 (i+1)) + stT199 228 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 227
    simpa using h
  have hprev := st199_p227
  have hstep := st199_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p229 : ((9152524343967/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT199 (i+1))
      = (∑ i ∈ Finset.range 228, stT199 (i+1)) + stT199 229 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 228
    simpa using h
  have hprev := st199_p228
  have hstep := st199_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p230 : ((45204999033279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT199 (i+1))
      = (∑ i ∈ Finset.range 229, stT199 (i+1)) + stT199 230 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 229
    simpa using h
  have hprev := st199_p229
  have hstep := st199_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p231 : ((44576455513823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT199 (i+1))
      = (∑ i ∈ Finset.range 230, stT199 (i+1)) + stT199 231 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 230
    simpa using h
  have hprev := st199_p230
  have hstep := st199_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p232 : ((22157086274961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT199 (i+1))
      = (∑ i ∈ Finset.range 231, stT199 (i+1)) + stT199 232 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 231
    simpa using h
  have hprev := st199_p231
  have hstep := st199_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p233 : ((22298072244887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT199 (i+1))
      = (∑ i ∈ Finset.range 232, stT199 (i+1)) + stT199 233 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 232
    simpa using h
  have hprev := st199_p232
  have hstep := st199_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p234 : ((22612763900807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT199 (i+1))
      = (∑ i ∈ Finset.range 233, stT199 (i+1)) + stT199 234 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 233
    simpa using h
  have hprev := st199_p233
  have hstep := st199_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p235 : ((22886447460879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT199 (i+1))
      = (∑ i ∈ Finset.range 234, stT199 (i+1)) + stT199 235 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 234
    simpa using h
  have hprev := st199_p234
  have hstep := st199_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p236 : ((22935294624111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT199 (i+1))
      = (∑ i ∈ Finset.range 235, stT199 (i+1)) + stT199 236 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 235
    simpa using h
  have hprev := st199_p235
  have hstep := st199_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p237 : ((22728357861361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT199 (i+1))
      = (∑ i ∈ Finset.range 236, stT199 (i+1)) + stT199 237 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 236
    simpa using h
  have hprev := st199_p236
  have hstep := st199_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p238 : ((22404527782939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT199 (i+1))
      = (∑ i ∈ Finset.range 237, stT199 (i+1)) + stT199 238 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 237
    simpa using h
  have hprev := st199_p237
  have hstep := st199_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p239 : ((44354760040297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT199 (i+1))
      = (∑ i ∈ Finset.range 238, stT199 (i+1)) + stT199 239 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 238
    simpa using h
  have hprev := st199_p238
  have hstep := st199_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p240 : ((22194242015531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT199 (i+1))
      = (∑ i ∈ Finset.range 239, stT199 (i+1)) + stT199 240 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 239
    simpa using h
  have hprev := st199_p239
  have hstep := st199_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p241 : ((22442415031417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT199 (i+1))
      = (∑ i ∈ Finset.range 240, stT199 (i+1)) + stT199 241 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 240
    simpa using h
  have hprev := st199_p240
  have hstep := st199_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p242 : ((22760973214269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT199 (i+1))
      = (∑ i ∈ Finset.range 241, stT199 (i+1)) + stT199 242 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 241
    simpa using h
  have hprev := st199_p241
  have hstep := st199_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p243 : ((22946591560019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT199 (i+1))
      = (∑ i ∈ Finset.range 242, stT199 (i+1)) + stT199 243 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 242
    simpa using h
  have hprev := st199_p242
  have hstep := st199_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p244 : ((45765930346663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT199 (i+1))
      = (∑ i ∈ Finset.range 243, stT199 (i+1)) + stT199 244 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 243
    simpa using h
  have hprev := st199_p243
  have hstep := st199_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p245 : ((45223536551203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT199 (i+1))
      = (∑ i ∈ Finset.range 244, stT199 (i+1)) + stT199 245 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 244
    simpa using h
  have hprev := st199_p244
  have hstep := st199_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p246 : ((44606345438201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT199 (i+1))
      = (∑ i ∈ Finset.range 245, stT199 (i+1)) + stT199 246 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 245
    simpa using h
  have hprev := st199_p245
  have hstep := st199_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p247 : ((2768490016691/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT199 (i+1))
      = (∑ i ∈ Finset.range 246, stT199 (i+1)) + stT199 247 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 246
    simpa using h
  have hprev := st199_p246
  have hstep := st199_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p248 : ((2780000344191/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT199 (i+1))
      = (∑ i ∈ Finset.range 247, stT199 (i+1)) + stT199 248 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 247
    simpa using h
  have hprev := st199_p247
  have hstep := st199_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p249 : ((351901077969/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT199 (i+1))
      = (∑ i ∈ Finset.range 248, stT199 (i+1)) + stT199 249 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 248
    simpa using h
  have hprev := st199_p248
  have hstep := st199_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_p250 : ((45643272776387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT199 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT199 (i+1))
      = (∑ i ∈ Finset.range 249, stT199 (i+1)) + stT199 250 := by
    have h := Finset.sum_range_succ (fun i => stT199 (i+1)) 249
    simpa using h
  have hprev := st199_p249
  have hstep := st199_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st199_s250 :
    |Real.sin (((199 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))
      - ((9887/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 201197/2500000) (δ := 2009/200000000) (ψ := -221723/200000) 199 175
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 199`** (evaluated boundary). -/
theorem station_199_sign : 0 < hardyG ((((199:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 199 250 (by norm_num) (by norm_num)
    ((-221723/200000 : ℚ) : ℝ)
  have hchain := st199_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT199 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((199 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-221723/200000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st199_c250
  have hsinb := abs_le.mp st199_s250
  have hbdy_lo : ((-10031496323541/396012500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((199 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-221723/200000 : ℚ) : ℝ))) / 2
          - ((((199:ℕ)):ℝ))
            * Real.sin (((199 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-221723/200000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((199:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((199:ℝ) * Real.log (250:ℝ) - ((-221723/200000 : ℚ) : ℝ))) / 2
        - ((199:ℝ)) * Real.sin ((199:ℝ) * Real.log (250:ℝ) - ((-221723/200000 : ℚ) : ℝ))
        ≥ ((-126889413/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((199:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-126889413/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-126889413/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-126889413/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((199:ℕ)):ℝ))+1) * (((((199:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((2763121207/3125000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((45643272776387/10000000000000 : ℚ) : ℝ) + ((-10031496323541/396012500000000 : ℚ) : ℝ)
      - ((2763121207/3125000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-221723/200000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((199:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-221723/200000 : ℚ) : ℝ)
        * (riemannZeta (line ((((199:ℕ)):ℝ)))).re
      - Real.sin ((-221723/200000 : ℚ) : ℝ)
        * (riemannZeta (line ((((199:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((199:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((199:ℕ)):ℝ))
      = (((((199:ℕ)):ℝ)) * (Real.log ((((199:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((199:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_199
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
  have hθwin : |(((-221723/200000 : ℚ) : ℝ) + ((39:ℤ)) * (2*Real.pi)) - theta ((((199:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((199:ℕ)):ℝ)))
    (φ := ((-221723/200000 : ℚ) : ℝ) + ((39:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-221723/200000 : ℚ)) : ℝ) 39).1,
    (cos_sin_shift (((-221723/200000 : ℚ)) : ℝ) 39).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_199_sign
end AxiomAudit
