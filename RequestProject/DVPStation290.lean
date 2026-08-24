import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 290` (rung-290.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT290 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((290 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-160941/125000 : ℚ) : ℝ))

theorem st290_c1 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((55899/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 160941/500000) (δ := 1/1000000000) (ψ := -160941/125000) 290 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t1 : ((55879/200000 : ℚ) : ℝ) ≤ stT290 1 := by
  have hc : ((55879/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55879/200000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((55879/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c2 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((32643/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3095679/10000000) (δ := 3643/250000000) (ψ := -160941/125000) 290 32
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t2 : ((230750129411/1000000000000 : ℚ) : ℝ) ≤ stT290 2 := by
  have hc : ((32633/100000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230750129411/1000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((32633/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c3 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((848649/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55737/400000) (δ := 3667/250000000) (ψ := -160941/125000) 290 51
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t3 : ((2449549674299/5000000000000 : ℚ) : ℝ) ≤ stT290 3 := by
  have hc : ((848549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2449549674299/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((848549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c4 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((4657/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 118903/400000) (δ := 14661/1000000000) (ψ := -160941/125000) 290 64
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t4 : ((18623/100000 : ℚ) : ℝ) ≤ stT290 4 := by
  have hc : ((18623/50000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18623/100000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((18623/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c5 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-997353/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1918013/2500000) (δ := 14533/1000000000) (ψ := -160941/125000) 290 74
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t5 : ((-557593183701/1250000000000 : ℚ) : ℝ) ≤ stT290 5 := by
  have hc : ((-997453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-557593183701/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-997453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c6 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((51349/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -151653/1000000) (δ := 7253/500000000) (ψ := -160941/125000) 290 83
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t6 : ((419211705411/1250000000000 : ℚ) : ℝ) ≤ stT290 6 := by
  have hc : ((205371/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((419211705411/1250000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((205371/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c7 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((496709/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57397/2000000) (δ := 1831/125000000) (ψ := -160941/125000) 290 90
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t7 : ((469298552349/1250000000000 : ℚ) : ℝ) ≤ stT290 7 := by
  have hc : ((496659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((469298552349/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((496659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c8 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((417787/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 284947/1000000) (δ := 907/62500000) (ψ := -160941/125000) 290 96
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t8 : ((1476746172171/10000000000000 : ℚ) : ℝ) ≤ stT290 8 := by
  have hc : ((417687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1476746172171/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((417687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c9 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-369457/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1201127/2000000) (δ := 14669/1000000000) (ψ := -160941/125000) 290 102
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t9 : ((-615845123169/2500000000000 : ℚ) : ℝ) ≤ stT290 9 := by
  have hc : ((-369507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-615845123169/2500000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-369507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c10 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-496281/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60391/80000) (δ := 14563/1000000000) (ψ := -160941/125000) 290 106
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t10 : ((-784768301009/2500000000000 : ℚ) : ℝ) ≤ stT290 10 := by
  have hc : ((-496331/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-784768301009/2500000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-496331/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c11 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((727299/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -945523/5000000) (δ := 7349/500000000) (ψ := -160941/125000) 290 111
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t11 : ((2192587158487/10000000000000 : ℚ) : ℝ) ≤ stT290 11 := by
  have hc : ((727199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2192587158487/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((727199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c12 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((792527/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -327927/2000000) (δ := 3669/250000000) (ψ := -160941/125000) 290 115
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t12 : ((2287539434677/10000000000000 : ℚ) : ℝ) ≤ stT290 12 := by
  have hc : ((792427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2287539434677/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((792427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c13 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-168877/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -644053/1000000) (δ := 3639/250000000) (ψ := -160941/125000) 290 119
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t13 : ((-468435998397/2000000000000 : ℚ) : ℝ) ≤ stT290 13 := by
  have hc : ((-168897/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-468435998397/2000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-168897/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c14 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((249463/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4097/250000) (δ := 7263/500000000) (ψ := -160941/125000) 290 122
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t14 : ((83331374007/312500000000 : ℚ) : ℝ) ≤ stT290 14 := by
  have hc : ((124719/125000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83331374007/312500000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((124719/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c15 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((169973/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3059843/10000000) (δ := 14599/1000000000) (ψ := -160941/125000) 290 125
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t15 : ((109684786731/1250000000000 : ℚ) : ℝ) ≤ stT290 15 := by
  have hc : ((169923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109684786731/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((169923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c16 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((462001/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 545273/2000000) (δ := 14683/1000000000) (ψ := -160941/125000) 290 128
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t16 : ((461901/4000000 : ℚ) : ℝ) ≤ stT290 16 := by
  have hc : ((461901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((461901/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((461901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c17 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((492111/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -444689/10000000) (δ := 7321/500000000) (ψ := -160941/125000) 290 131
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t17 : ((298355774679/1250000000000 : ℚ) : ℝ) ≤ stT290 17 := by
  have hc : ((492061/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298355774679/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((492061/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c18 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-48199/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6128739/10000000) (δ := 3641/250000000) (ψ := -160941/125000) 290 134
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t18 : ((-454483531883/2500000000000 : ℚ) : ℝ) ≤ stT290 18 := by
  have hc : ((-192821/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-454483531883/2500000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-192821/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c19 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((788997/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 827027/5000000) (δ := 117/8000000) (ψ := -160941/125000) 290 136
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t19 : ((1809853574829/10000000000000 : ℚ) : ℝ) ≤ stT290 19 := by
  have hc : ((788897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1809853574829/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((788897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c20 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-985367/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 742577/1000000) (δ := 14611/1000000000) (ψ := -160941/125000) 290 138
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t20 : ((-550892805939/2500000000000 : ℚ) : ℝ) ≤ stT290 20 := by
  have hc : ((-985467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-550892805939/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-985467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c21 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-158621/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -173009/400000) (δ := 14689/1000000000) (ψ := -160941/125000) 290 141
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t21 : ((-346357633059/10000000000000 : ℚ) : ℝ) ≤ stT290 21 := by
  have hc : ((-158721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-346357633059/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-158721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c22 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((138527/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2014151/10000000) (δ := 227/15625000) (ψ := -160941/125000) 290 143
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t22 : ((295297893549/2000000000000 : ℚ) : ℝ) ≤ stT290 22 := by
  have hc : ((138507/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((295297893549/2000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((138507/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c23 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((13852/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1202523/10000000) (δ := 733/50000000) (ψ := -160941/125000) 290 145
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t23 : ((57760313301/312500000000 : ℚ) : ℝ) ≤ stT290 23 := by
  have hc : ((221607/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57760313301/312500000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((221607/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c24 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((15231/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1762739/10000000) (δ := 14557/1000000000) (ψ := -160941/125000) 290 147
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t24 : ((31086059189/200000000000 : ℚ) : ℝ) ≤ stT290 24 := by
  have hc : ((15229/20000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31086059189/200000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((15229/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c25 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((5491/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -895679/2500000) (δ := 1829/125000000) (ψ := -160941/125000) 290 149
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t25 : ((5487/200000 : ℚ) : ℝ) ≤ stT290 25 := by
  have hc : ((5487/40000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5487/200000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((5487/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c26 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-869731/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1312727/2000000) (δ := 14617/1000000000) (ψ := -160941/125000) 290 151
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t26 : ((-852939751811/5000000000000 : ℚ) : ℝ) ≤ stT290 26 := by
  have hc : ((-869831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-852939751811/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-869831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c27 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-56081/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 127253/250000) (δ := 14693/1000000000) (ψ := -160941/125000) 290 152
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t27 : ((-215903993687/2500000000000 : ℚ) : ℝ) ≤ stT290 27 := by
  have hc : ((-112187/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215903993687/2500000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-112187/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c28 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((999867/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1631/400000) (δ := 1837/125000000) (ψ := -160941/125000) 290 154
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t28 : ((944690835737/5000000000000 : ℚ) : ℝ) ≤ stT290 28 := by
  have hc : ((999767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((944690835737/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((999767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c29 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-143859/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5933959/10000000) (δ := 14681/1000000000) (ψ := -160941/125000) 290 156
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t29 : ((-133588342283/1000000000000 : ℚ) : ℝ) ≤ stT290 29 := by
  have hc : ((-143879/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133588342283/1000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-143879/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c30 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((385851/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1468333/5000000) (δ := 14629/1000000000) (ψ := -160941/125000) 290 157
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t30 : ((704281416491/10000000000000 : ℚ) : ℝ) ≤ stT290 30 := by
  have hc : ((385751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((704281416491/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((385751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c31 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-306807/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4706583/10000000) (δ := 14643/1000000000) (ψ := -160941/125000) 290 159
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t31 : ((-275610772489/5000000000000 : ℚ) : ℝ) ≤ stT290 31 := by
  have hc : ((-306907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275610772489/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-306907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c32 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((101019/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2603261/10000000) (δ := 291/20000000) (ψ := -160941/125000) 290 160
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t32 : ((89271299117/1000000000000 : ℚ) : ℝ) ≤ stT290 32 := by
  have hc : ((100999/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89271299117/1000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((100999/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c33 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-857559/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -812907/1250000) (δ := 7319/500000000) (ψ := -160941/125000) 290 162
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t33 : ((-1492993061043/10000000000000 : ℚ) : ℝ) ≤ stT290 33 := by
  have hc : ((-857659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1492993061043/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-857659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c34 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((974319/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -283897/5000000) (δ := 14531/1000000000) (ψ := -160941/125000) 290 163
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t34 : ((334154194343/2000000000000 : ℚ) : ℝ) ≤ stT290 34 := by
  have hc : ((974219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334154194343/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((974219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c35 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-31957/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 237009/500000) (δ := 457/31250000) (ψ := -160941/125000) 290 164
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t35 : ((-54034107803/1000000000000 : ℚ) : ℝ) ≤ stT290 35 := by
  have hc : ((-31967/100000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54034107803/1000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-31967/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c36 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-160317/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1562961/2500000) (δ := 1461/100000000) (ψ := -160941/125000) 290 166
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t36 : ((-267228386779/2000000000000 : ℚ) : ℝ) ≤ stT290 36 := by
  have hc : ((-160337/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-267228386779/2000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-160337/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c37 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((668793/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -523883/2500000) (δ := 14503/1000000000) (ψ := -160941/125000) 290 167
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t37 : ((1099323936377/10000000000000 : ℚ) : ℝ) ≤ stT290 37 := by
  have hc : ((668693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1099323936377/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((668693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c38 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((409141/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30619/200000) (δ := 913/62500000) (ψ := -160941/125000) 290 168
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t38 : ((331816573737/2500000000000 : ℚ) : ℝ) ≤ stT290 38 := by
  have hc : ((409091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((331816573737/2500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((409091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c39 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-287191/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 581903/1250000) (δ := 2903/200000000) (ψ := -160941/125000) 290 169
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t39 : ((-230016953531/5000000000000 : ℚ) : ℝ) ≤ stT290 39 := by
  have hc : ((-287291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230016953531/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-287291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c40 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-487891/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3651333/5000000) (δ := 7311/500000000) (ψ := -160941/125000) 290 170
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t40 : ((-771502544799/5000000000000 : ℚ) : ℝ) ≤ stT290 40 := by
  have hc : ((-487941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-771502544799/5000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-487941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c41 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-791741/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3105563/5000000) (δ := 14567/1000000000) (ψ := -160941/125000) 290 172
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t41 : ((-618324089829/5000000000000 : ℚ) : ℝ) ≤ stT290 41 := by
  have hc : ((-791841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-618324089829/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-791841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c42 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-207027/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4448329/10000000) (δ := 909/62500000) (ψ := -160941/125000) 290 173
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t42 : ((-159802001659/5000000000000 : ℚ) : ℝ) ≤ stT290 42 := by
  have hc : ((-207127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159802001659/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-207127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c43 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((81513/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -77417/250000) (δ := 1819/125000000) (ψ := -160941/125000) 290 174
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t43 : ((1553349721/31250000000 : ℚ) : ℝ) ≤ stT290 43 := by
  have hc : ((5093/15625 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1553349721/31250000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((5093/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c44 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((164073/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -267157/1250000) (δ := 2929/200000000) (ψ := -160941/125000) 290 175
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t44 : ((3864242917/39062500000 : ℚ) : ℝ) ≤ stT290 44 := by
  have hc : ((10253/15625 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3864242917/39062500000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((10253/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c45 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((813311/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1552439/10000000) (δ := 7269/500000000) (ψ := -160941/125000) 290 176
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t45 : ((1212262583021/10000000000000 : ℚ) : ℝ) ≤ stT290 45 := by
  have hc : ((813211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1212262583021/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((813211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c46 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((172533/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13257/100000) (δ := 14631/1000000000) (ψ := -160941/125000) 290 177
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t46 : ((254356444947/2000000000000 : ℚ) : ℝ) ≤ stT290 46 := by
  have hc : ((172513/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254356444947/2000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((172513/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c47 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((8383/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -288319/2000000) (δ := 14679/1000000000) (ψ := -160941/125000) 290 178
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t47 : ((6113197959/50000000000 : ℚ) : ℝ) ≤ stT290 47 := by
  have hc : ((4191/5000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6113197959/50000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((4191/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c48 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((29149/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -471461/2500000) (δ := 1827/125000000) (ψ := -160941/125000) 290 179
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t48 : ((67307463/640000000 : ℚ) : ℝ) ≤ stT290 48 := by
  have hc : ((5829/8000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67307463/640000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((5829/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c49 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((98131/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2644887/10000000) (δ := 14509/1000000000) (ψ := -160941/125000) 290 180
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t49 : ((140158529381/2000000000000 : ℚ) : ℝ) ≤ stT290 49 := by
  have hc : ((98111/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140158529381/2000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((98111/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c50 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((88353/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -185291/500000) (δ := 14601/1000000000) (ψ := -160941/125000) 290 181
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t50 : ((124808539889/10000000000000 : ℚ) : ℝ) ≤ stT290 50 := by
  have hc : ((88253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124808539889/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((88253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c51 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-436733/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5056899/10000000) (δ := 2939/200000000) (ψ := -160941/125000) 290 182
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t51 : ((-611688950073/10000000000000 : ℚ) : ℝ) ≤ stT290 51 := by
  have hc : ((-436833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-611688950073/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-436833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c52 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-892969/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6686739/10000000) (δ := 2923/200000000) (ψ := -160941/125000) 290 183
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t52 : ((-1238464328819/10000000000000 : ℚ) : ℝ) ≤ stT290 52 := by
  have hc : ((-893069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1238464328819/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-893069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c53 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-957581/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3561603/5000000) (δ := 2923/200000000) (ψ := -160941/125000) 290 183
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t53 : ((-657738183843/5000000000000 : ℚ) : ℝ) ≤ stT290 53 := by
  have hc : ((-957681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-657738183843/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-957681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c54 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-202057/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 993403/2000000) (δ := 14523/1000000000) (ψ := -160941/125000) 290 184
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t54 : ((-68758216149/1250000000000 : ℚ) : ℝ) ≤ stT290 54 := by
  have hc : ((-202107/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68758216149/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-202107/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c55 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((519219/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2562149/10000000) (δ := 14573/1000000000) (ψ := -160941/125000) 290 185
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t55 : ((699979540481/10000000000000 : ℚ) : ℝ) ≤ stT290 55 := by
  have hc : ((519119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((699979540481/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((519119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c56 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((999457/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41201/5000000) (δ := 7333/500000000) (ψ := -160941/125000) 290 186
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t56 : ((667723377621/5000000000000 : ℚ) : ℝ) ≤ stT290 56 := by
  have hc : ((999357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((667723377621/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((999357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c57 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((377907/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -591631/2000000) (δ := 14559/1000000000) (ψ := -160941/125000) 290 187
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t57 : ((125104365331/2500000000000 : ℚ) : ℝ) ≤ stT290 57 := by
  have hc : ((377807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125104365331/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((377807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c58 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-376309/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6057063/10000000) (δ := 14551/1000000000) (ψ := -160941/125000) 290 188
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t58 : ((-98836766067/1000000000000 : ℚ) : ℝ) ≤ stT290 58 := by
  have hc : ((-376359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98836766067/1000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-376359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c59 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-821339/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6336377/10000000) (δ := 14551/1000000000) (ψ := -160941/125000) 290 188
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t59 : ((-106942321971/1000000000000 : ℚ) : ℝ) ≤ stT290 59 := by
  have hc : ((-821439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106942321971/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-821439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c60 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((215397/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2813561/10000000) (δ := 2909/200000000) (ψ := -160941/125000) 290 189
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t60 : ((139005842459/2500000000000 : ℚ) : ℝ) ≤ stT290 60 := by
  have hc : ((215347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139005842459/2500000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((215347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c61 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((467193/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -45533/500000) (δ := 14637/1000000000) (ψ := -160941/125000) 290 190
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t61 : ((37382184289/312500000000 : ℚ) : ℝ) ≤ stT290 61 := by
  have hc : ((467143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37382184289/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((467143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c62 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-353311/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15093/31250) (δ := 14673/1000000000) (ψ := -160941/125000) 290 191
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t62 : ((-224416338411/5000000000000 : ℚ) : ℝ) ≤ stT290 62 := by
  have hc : ((-353411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224416338411/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-353411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c63 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-907551/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 677053/1000000) (δ := 14673/1000000000) (ψ := -160941/125000) 290 191
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t63 : ((-571766578591/5000000000000 : ℚ) : ℝ) ≤ stT290 63 := by
  have hc : ((-907651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-571766578591/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-907651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c64 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((546989/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 620021/2500000) (δ := 729/50000000) (ψ := -160941/125000) 290 192
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t64 : ((546889/8000000 : ℚ) : ℝ) ≤ stT290 64 := by
  have hc : ((546889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((546889/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((546889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c65 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((175083/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -993667/5000000) (δ := 14687/1000000000) (ψ := -160941/125000) 290 193
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t65 : ((108566332563/1250000000000 : ℚ) : ℝ) ≤ stT290 65 := by
  have hc : ((87529/125000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108566332563/1250000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((87529/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c66 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-881839/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -165659/250000) (δ := 7297/500000000) (ψ := -160941/125000) 290 194
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t66 : ((-217118388837/2000000000000 : ℚ) : ℝ) ≤ stT290 66 := by
  have hc : ((-881939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217118388837/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-881939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c67 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-139197/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4276117/10000000) (δ := 14609/1000000000) (ψ := -160941/125000) 290 194
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t67 : ((-34035689683/2000000000000 : ℚ) : ℝ) ≤ stT290 67 := by
  have hc : ((-139297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34035689683/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-139297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c68 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((192411/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -690899/10000000) (δ := 14701/1000000000) (ψ := -160941/125000) 290 195
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t68 : ((116654166549/1000000000000 : ℚ) : ℝ) ≤ stT290 68 := by
  have hc : ((192391/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116654166549/1000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((192391/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c69 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-685359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1453683/2500000) (δ := 7297/500000000) (ψ := -160941/125000) 290 196
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t69 : ((-825195986281/10000000000000 : ℚ) : ℝ) ≤ stT290 69 := by
  have hc : ((-685459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-825195986281/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-685459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c70 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-136271/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1154269/2500000) (δ := 14609/1000000000) (ψ := -160941/125000) 290 196
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t70 : ((-162934812509/5000000000000 : ℚ) : ℝ) ≤ stT290 70 := by
  have hc : ((-136321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162934812509/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-136321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c71 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((118543/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -807053/10000000) (δ := 14687/1000000000) (ψ := -160941/125000) 290 197
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t71 : ((281339490641/2500000000000 : ℚ) : ℝ) ≤ stT290 71 := by
  have hc : ((237061/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((281339490641/2500000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((237061/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c72 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-415021/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1593737/2500000) (δ := 14623/1000000000) (ψ := -160941/125000) 290 198
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t72 : ((-30572884647/312500000000 : ℚ) : ℝ) ≤ stT290 72 := by
  have hc : ((-415071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30572884647/312500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-415071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c73 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((60213/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1812597/5000000) (δ := 729/50000000) (ψ := -160941/125000) 290 198
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t73 : ((70415436993/5000000000000 : ℚ) : ℝ) ≤ stT290 73 := by
  have hc : ((60163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70415436993/5000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((60163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c74 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((126273/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2218709/10000000) (δ := 1453/100000000) (ψ := -160941/125000) 290 199
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t74 : ((36691520607/500000000000 : ℚ) : ℝ) ≤ stT290 74 := by
  have hc : ((126253/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36691520607/500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((126253/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c75 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-198143/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3756519/5000000) (δ := 14673/1000000000) (ψ := -160941/125000) 290 199
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t75 : ((-228819014263/2000000000000 : ℚ) : ℝ) ≤ stT290 75 := by
  have hc : ((-198163/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228819014263/2000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-198163/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c76 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((52849/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 281569/2000000) (δ := 7283/500000000) (ψ := -160941/125000) 290 200
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t76 : ((121229511969/1250000000000 : ℚ) : ℝ) ≤ stT290 76 := by
  have hc : ((211371/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121229511969/1250000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((211371/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c77 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-175361/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2411423/5000000) (δ := 7329/500000000) (ψ := -160941/125000) 290 201
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t77 : ((-99949714033/2500000000000 : ℚ) : ℝ) ≤ stT290 77 := by
  have hc : ((-175411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99949714033/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-175411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c78 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-47939/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4532119/10000000) (δ := 7329/500000000) (ψ := -160941/125000) 290 201
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t78 : ((-27151460301/1000000000000 : ℚ) : ℝ) ≤ stT290 78 := by
  have hc : ((-47959/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27151460301/1000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-47959/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c79 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((356851/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1940069/10000000) (δ := 14551/1000000000) (ψ := -160941/125000) 290 202
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t79 : ((401432166687/5000000000000 : ℚ) : ℝ) ≤ stT290 79 := by
  have hc : ((356801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((401432166687/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((356801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c80 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-963833/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7179561/10000000) (δ := 14551/1000000000) (ψ := -160941/125000) 290 202
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t80 : ((-538854933861/5000000000000 : ℚ) : ℝ) ≤ stT290 80 := by
  have hc : ((-963933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-538854933861/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-963933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c81 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((122723/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47791/1000000) (δ := 3661/250000000) (ψ := -160941/125000) 290 203
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t81 : ((272689972731/2500000000000 : ℚ) : ℝ) ≤ stT290 81 := by
  have hc : ((245421/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272689972731/2500000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((245421/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c82 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-820849/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -633423/1000000) (δ := 7333/500000000) (ψ := -160941/125000) 290 204
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t82 : ((-226646778971/2500000000000 : ℚ) : ℝ) ≤ stT290 82 := by
  have hc : ((-820949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-226646778971/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-820949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c83 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((111153/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 490757/2000000) (δ := 7333/500000000) (ψ := -160941/125000) 290 204
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t83 : ((60992124193/1000000000000 : ℚ) : ℝ) ≤ stT290 83 := by
  have hc : ((111133/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60992124193/1000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((111133/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c84 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-127473/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -457147/1000000) (δ := 2903/100000000) (ψ := -160941/125000) 290 205
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t84 : ((-13913907007/500000000000 : ℚ) : ℝ) ≤ stT290 84 := by
  have hc : ((-127523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13913907007/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-127523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c85 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-163/5000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2004253/5000000) (δ := 1463/100000000) (ψ := -160941/125000) 290 205
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t85 : ((-354681531/100000000000 : ℚ) : ℝ) ≤ stT290 85 := by
  have hc : ((-327/10000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-354681531/100000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-327/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c86 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((279097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3219857/10000000) (δ := 14523/1000000000) (ψ := -160941/125000) 290 206
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t86 : ((300849998019/10000000000000 : ℚ) : ℝ) ≤ stT290 86 := by
  have hc : ((278997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((300849998019/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((278997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c87 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-474083/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1290449/2500000) (δ := 367/25000000) (ψ := -160941/125000) 290 206
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t87 : ((-508377758679/10000000000000 : ℚ) : ℝ) ≤ stT290 87 := by
  have hc : ((-474183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-508377758679/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-474183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c88 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((618359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56509/250000) (δ := 3647/250000000) (ψ := -160941/125000) 290 207
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t88 : ((659065948777/10000000000000 : ℚ) : ℝ) ≤ stT290 88 := by
  have hc : ((618259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((659065948777/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((618259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c89 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-718689/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5931777/10000000) (δ := 2923/200000000) (ψ := -160941/125000) 290 207
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t89 : ((-380957451211/5000000000000 : ℚ) : ℝ) ≤ stT290 89 := by
  have hc : ((-718789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-380957451211/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-718789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c90 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((783687/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1675543/10000000) (δ := 2939/200000000) (ψ := -160941/125000) 290 208
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t90 : ((206493197001/2500000000000 : ℚ) : ℝ) ≤ stT290 90 := by
  have hc : ((783587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((206493197001/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((783587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c91 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-821161/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3167799/5000000) (δ := 5819/200000000) (ψ := -160941/125000) 290 208
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t91 : ((-172183117477/2000000000000 : ℚ) : ℝ) ≤ stT290 91 := by
  have hc : ((-821261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172183117477/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-821261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c92 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((33469/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -362201/2500000) (δ := 7301/500000000) (ψ := -160941/125000) 290 209
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t92 : ((1744483599/20000000000 : ℚ) : ℝ) ≤ stT290 92 := by
  have hc : ((6693/8000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1744483599/20000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((6693/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c93 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-166637/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3194549/5000000) (δ := 14601/1000000000) (ψ := -160941/125000) 290 209
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t93 : ((-21601913683/250000000000 : ℚ) : ℝ) ≤ stT290 93 := by
  have hc : ((-166657/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21601913683/250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-166657/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c94 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((810431/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1564773/10000000) (δ := 7347/500000000) (ψ := -160941/125000) 290 210
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t94 : ((835792410351/10000000000000 : ℚ) : ℝ) ≤ stT290 94 := by
  have hc : ((810331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((835792410351/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((810331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c95 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-191421/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24429/40000) (δ := 14509/1000000000) (ψ := -160941/125000) 290 210
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t95 : ((-98209787817/1250000000000 : ℚ) : ℝ) ≤ stT290 95 := by
  have hc : ((-95723/125000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98209787817/1250000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-95723/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c96 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((347057/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2009021/10000000) (δ := 14587/1000000000) (ψ := -160941/125000) 290 211
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t96 : ((17708114217/250000000000 : ℚ) : ℝ) ≤ stT290 96 := by
  have hc : ((347007/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17708114217/250000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((347007/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c97 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-589797/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5504009/10000000) (δ := 14587/1000000000) (ψ := -160941/125000) 290 211
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t97 : ((-598950149259/10000000000000 : ℚ) : ℝ) ≤ stT290 97 := by
  have hc : ((-589897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-598950149259/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-589897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c98 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((447171/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -345999/1250000) (δ := 14679/1000000000) (ψ := -160941/125000) 290 212
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t98 : ((56451208099/1250000000000 : ℚ) : ℝ) ≤ stT290 98 := by
  have hc : ((447071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56451208099/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((447071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c99 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-26307/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2296249/5000000) (δ := 14679/1000000000) (ψ := -160941/125000) 290 212
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t99 : ((-13224792523/500000000000 : ℚ) : ℝ) ≤ stT290 99 := by
  have hc : ((-26317/100000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13224792523/500000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-26317/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c100 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((39187/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3828997/10000000) (δ := 14631/1000000000) (ψ := -160941/125000) 290 213
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t100 : ((39086960913/10000000000000 : ℚ) : ℝ) ≤ stT290 100 := by
  have hc : ((39087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39086960913/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((39087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c101 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((43017/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3385043/10000000) (δ := 14631/1000000000) (ψ := -160941/125000) 290 213
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t101 : ((42783605889/2000000000000 : ℚ) : ℝ) ≤ stT290 101 := by
  have hc : ((42997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42783605889/2000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((42997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c102 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-480483/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5180003/10000000) (δ := 7269/500000000) (ψ := -160941/125000) 290 214
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t102 : ((-118962074071/2500000000000 : ℚ) : ℝ) ≤ stT290 102 := by
  have hc : ((-480583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118962074071/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-480583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c103 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((181679/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1893169/10000000) (δ := 2933/200000000) (ψ := -160941/125000) 290 214
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t103 : ((89494477083/1250000000000 : ℚ) : ℝ) ≤ stT290 103 := by
  have hc : ((90827/125000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89494477083/1250000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((90827/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c104 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-457027/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1702479/2500000) (δ := 2929/200000000) (ψ := -160941/125000) 290 215
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t104 : ((-448201021737/5000000000000 : ℚ) : ℝ) ≤ stT290 104 := by
  have hc : ((-457077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-448201021737/5000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-457077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c105 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((99869/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 127971/10000000) (δ := 7279/500000000) (ψ := -160941/125000) 290 215
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t105 : ((974523981/10000000000 : ℚ) : ℝ) ≤ stT290 105 := by
  have hc : ((99859/100000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((974523981/10000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((99859/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c106 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-471113/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7000029/10000000) (δ := 2929/200000000) (ψ := -160941/125000) 290 215
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t106 : ((-228817012809/2500000000000 : ℚ) : ℝ) ≤ stT290 106 := by
  have hc : ((-471163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228817012809/2500000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-471163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c107 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((144949/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -190033/1000000) (δ := 14651/1000000000) (ψ := -160941/125000) 290 216
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t107 : ((8756755109/125000000000 : ℚ) : ℝ) ≤ stT290 107 := by
  have hc : ((144929/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8756755109/125000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((144929/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c108 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-1793/5000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 484391/1000000) (δ := 14651/1000000000) (ψ := -160941/125000) 290 216
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t108 : ((-3451594337/100000000000 : ℚ) : ℝ) ≤ stT290 108 := by
  have hc : ((-3587/10000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3451594337/100000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-3587/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c109 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-50917/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2091009/5000000) (δ := 909/62500000) (ψ := -160941/125000) 290 217
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t109 : ((-48817568709/5000000000000 : ℚ) : ℝ) ≤ stT290 109 := by
  have hc : ((-50967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48817568709/5000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-50967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c110 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((35041/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 487809/2000000) (δ := 14659/1000000000) (ψ := -160941/125000) 290 217
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t110 : ((66808605609/1250000000000 : ℚ) : ℝ) ≤ stT290 110 := by
  have hc : ((140139/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66808605609/1250000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((140139/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c111 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-896719/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6707741/10000000) (δ := 14567/1000000000) (ψ := -160941/125000) 290 218
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t111 : ((-425611464201/5000000000000 : ℚ) : ℝ) ≤ stT290 111 := by
  have hc : ((-896819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-425611464201/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-896819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c112 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((996623/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -102753/5000000) (δ := 14567/1000000000) (ψ := -160941/125000) 290 218
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t112 : ((941625544453/10000000000000 : ℚ) : ℝ) ≤ stT290 112 := by
  have hc : ((996523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((941625544453/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((996523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c113 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-798507/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6239019/10000000) (δ := 14567/1000000000) (ψ := -160941/125000) 290 218
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t113 : ((-751266375647/10000000000000 : ℚ) : ℝ) ≤ stT290 113 := by
  have hc : ((-798607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-751266375647/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-798607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c114 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((331877/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3081259/10000000) (δ := 7337/500000000) (ψ := -160941/125000) 290 219
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t114 : ((62147472309/2000000000000 : ℚ) : ℝ) ≤ stT290 114 := by
  have hc : ((331777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62147472309/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((331777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c115 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((267239/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3250673/10000000) (δ := 14529/1000000000) (ψ := -160941/125000) 290 219
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t115 : ((31138523257/1250000000000 : ℚ) : ℝ) ≤ stT290 115 := by
  have hc : ((267139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31138523257/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((267139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c116 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-392067/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -77253/125000) (δ := 14581/1000000000) (ψ := -160941/125000) 290 220
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t116 : ((-364071615809/5000000000000 : ℚ) : ℝ) ≤ stT290 116 := by
  have hc : ((-392117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-364071615809/5000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-392117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c117 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((249963/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8603/2000000) (δ := 14581/1000000000) (ψ := -160941/125000) 290 220
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t117 : ((231067681/2500000000 : ℚ) : ℝ) ≤ stT290 117 := by
  have hc : ((124969/125000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((231067681/2500000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((124969/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c118 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-158453/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 776659/1250000) (δ := 7311/500000000) (ψ := -160941/125000) 290 220
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t118 : ((-5835451279/80000000000 : ℚ) : ℝ) ≤ stT290 118 := by
  have hc : ((-158473/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5835451279/80000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-158473/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c119 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((218397/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3376561/10000000) (δ := 2903/200000000) (ψ := -160941/125000) 290 221
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t119 : ((100056211653/5000000000000 : ℚ) : ℝ) ≤ stT290 119 := by
  have hc : ((218297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100056211653/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((218297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c120 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((118673/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2690457/10000000) (δ := 459/31250000) (ψ := -160941/125000) 290 221
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t120 : ((1353877497/31250000000 : ℚ) : ℝ) ≤ stT290 120 := by
  have hc : ((14831/31250 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1353877497/31250000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((14831/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c121 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-47117/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7000877/10000000) (δ := 913/62500000) (ψ := -160941/125000) 290 222
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t121 : ((-21419093051/250000000000 : ℚ) : ℝ) ≤ stT290 121 := by
  have hc : ((-23561/25000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21419093051/250000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-23561/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c122 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((457859/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -258441/2500000) (δ := 2919/200000000) (ψ := -160941/125000) 290 222
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t122 : ((414480582813/5000000000000 : ℚ) : ℝ) ≤ stT290 122 := by
  have hc : ((457809/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((414480582813/5000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((457809/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c123 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-93439/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1221157/2500000) (δ := 913/62500000) (ψ := -160941/125000) 290 222
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t123 : ((-1053421061/31250000000 : ℚ) : ℝ) ≤ stT290 123 := by
  have hc : ((-11683/31250 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1053421061/31250000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-11683/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c124 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-39893/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -990573/2000000) (δ := 14503/1000000000) (ψ := -160941/125000) 290 223
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t124 : ((-35833971381/1000000000000 : ℚ) : ℝ) ≤ stT290 124 := by
  have hc : ((-39903/100000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35833971381/1000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-39903/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c125 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((939991/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10881/125000) (δ := 14503/1000000000) (ψ := -160941/125000) 290 223
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t125 : ((840663887457/10000000000000 : ℚ) : ℝ) ≤ stT290 125 := by
  have hc : ((939891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((840663887457/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((939891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c126 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-885781/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 265897/400000) (δ := 14503/1000000000) (ψ := -160941/125000) 290 223
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t126 : ((-789205692351/10000000000000 : ℚ) : ℝ) ≤ stT290 126 := by
  have hc : ((-885881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-789205692351/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-885881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c127 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((236789/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3329341/10000000) (δ := 14593/1000000000) (ψ := -160941/125000) 290 224
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t127 : ((52506851071/2500000000000 : ℚ) : ℝ) ≤ stT290 127 := by
  have hc : ((236689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52506851071/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((236689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c128 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((587531/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2356979/10000000) (δ := 14593/1000000000) (ψ := -160941/125000) 290 224
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t128 : ((519220274573/10000000000000 : ℚ) : ℝ) ≤ stT290 128 := by
  have hc : ((587431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((519220274573/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((587431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c129 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-249579/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7708889/10000000) (δ := 14517/1000000000) (ψ := -160941/125000) 290 225
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t129 : ((-54941022851/625000000000 : ℚ) : ℝ) ≤ stT290 129 := by
  have hc : ((-62401/62500 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54941022851/625000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-62401/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c130 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((166087/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2110439/10000000) (δ := 14517/1000000000) (ψ := -160941/125000) 290 225
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t130 : ((36411501399/625000000000 : ℚ) : ℝ) ≤ stT290 130 := by
  have hc : ((83031/125000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36411501399/625000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((83031/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c131 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((9577/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3445163/10000000) (δ := 7343/500000000) (ψ := -160941/125000) 290 225
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t131 : ((261346709/15625000000 : ℚ) : ℝ) ≤ stT290 131 := by
  have hc : ((2393/12500 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261346709/15625000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((2393/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c132 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-903981/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1349893/2000000) (δ := 14579/1000000000) (ψ := -160941/125000) 290 226
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t132 : ((-786902157509/10000000000000 : ℚ) : ℝ) ≤ stT290 132 := by
  have hc : ((-904081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-786902157509/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-904081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c133 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((54513/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -255549/2000000) (δ := 14579/1000000000) (ψ := -160941/125000) 290 226
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t133 : ((189053173943/2500000000000 : ℚ) : ℝ) ≤ stT290 133 := by
  have hc : ((218027/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189053173943/2500000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((218027/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c134 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-90271/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 259561/625000) (δ := 29179/1000000000) (ψ := -160941/125000) 290 226
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t134 : ((-78068705399/10000000000000 : ℚ) : ℝ) ≤ stT290 134 := by
  have hc : ((-90371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78068705399/10000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-90371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c135 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-97531/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -770581/1250000) (δ := 14531/1000000000) (ψ := -160941/125000) 290 227
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t135 : ((-167904162681/2500000000000 : ℚ) : ℝ) ≤ stT290 135 := by
  have hc : ((-195087/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167904162681/2500000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-195087/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c136 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((947449/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -203519/2500000) (δ := 917/62500000) (ψ := -160941/125000) 290 227
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t136 : ((203086047177/2500000000000 : ℚ) : ℝ) ≤ stT290 136 := by
  have hc : ((947349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203086047177/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((947349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c137 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-226169/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4497347/10000000) (δ := 14531/1000000000) (ψ := -160941/125000) 290 227
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t137 : ((-96657365151/5000000000000 : ℚ) : ℝ) ≤ stT290 137 := by
  have hc : ((-226269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96657365151/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-226269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c138 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-90049/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5937909/10000000) (δ := 2913/200000000) (ψ := -160941/125000) 290 228
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t138 : ((-153330964611/2500000000000 : ℚ) : ℝ) ≤ stT290 138 := by
  have hc : ((-180123/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153330964611/2500000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-180123/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c139 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((480351/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -703191/10000000) (δ := 7319/500000000) (ψ := -160941/125000) 290 228
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t139 : ((101846386147/1250000000000 : ℚ) : ℝ) ≤ stT290 139 := by
  have hc : ((480301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101846386147/1250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((480301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c140 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-224853/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4493971/10000000) (δ := 2913/200000000) (ψ := -160941/125000) 290 228
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t140 : ((-38024030543/2000000000000 : ℚ) : ℝ) ≤ stT290 140 := by
  have hc : ((-224953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38024030543/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-224953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c141 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-375889/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6053877/10000000) (δ := 7273/500000000) (ψ := -160941/125000) 290 229
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t141 : ((-39574722591/625000000000 : ℚ) : ℝ) ≤ stT290 141 := by
  have hc : ((-375939/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39574722591/625000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-375939/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c142 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((931579/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -930157/10000000) (δ := 7273/500000000) (ψ := -160941/125000) 290 229
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t142 : ((781679478699/10000000000000 : ℚ) : ℝ) ≤ stT290 142 := by
  have hc : ((931479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((781679478699/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((931479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c143 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-46057/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4157603/10000000) (δ := 7273/500000000) (ψ := -160941/125000) 290 229
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t143 : ((-38556656001/5000000000000 : ℚ) : ℝ) ≤ stT290 143 := by
  have hc : ((-46107/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38556656001/5000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-46107/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c144 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-428251/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10397/16000) (δ := 14653/1000000000) (ψ := -160941/125000) 290 230
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t144 : ((-178458892767/2500000000000 : ℚ) : ℝ) ≤ stT290 144 := by
  have hc : ((-428301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178458892767/2500000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-428301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c145 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((103707/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1480763/10000000) (δ := 291/20000000) (ψ := -160941/125000) 290 230
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t145 : ((86113512303/1250000000000 : ℚ) : ℝ) ≤ stT290 145 := by
  have hc : ((207389/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86113512303/1250000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((207389/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c146 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((169143/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 350209/1000000) (δ := 14653/1000000000) (ψ := -160941/125000) 290 230
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t146 : ((27980166403/2000000000000 : ℚ) : ℝ) ≤ stT290 146 := by
  have hc : ((169043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27980166403/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((169043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c147 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-971633/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -907137/1250000) (δ := 91/6250000) (ψ := -160941/125000) 290 231
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t147 : ((-801472745871/10000000000000 : ℚ) : ℝ) ≤ stT290 147 := by
  have hc : ((-971733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-801472745871/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-971733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c148 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((592429/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1170907/5000000) (δ := 14643/1000000000) (ψ := -160941/125000) 290 231
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t148 : ((243445442013/5000000000000 : ℚ) : ℝ) ≤ stT290 148 := by
  have hc : ((592329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((243445442013/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((592329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c149 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((526631/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2540409/10000000) (δ := 91/6250000) (ψ := -160941/125000) 290 231
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t149 : ((431350517661/10000000000000 : ℚ) : ℝ) ≤ stT290 149 := by
  have hc : ((526531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((431350517661/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((526531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c150 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-982817/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7389861/10000000) (δ := 14643/1000000000) (ψ := -160941/125000) 290 231
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t150 : ((-802548781749/10000000000000 : ℚ) : ℝ) ≤ stT290 150 := by
  have hc : ((-982917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-802548781749/10000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-982917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c151 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((33933/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3500767/10000000) (δ := 1817/125000000) (ψ := -160941/125000) 290 232
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t151 : ((6899498111/500000000000 : ℚ) : ℝ) ≤ stT290 151 := by
  have hc : ((33913/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6899498111/500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((33913/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c152 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((217709/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1284741/10000000) (δ := 14667/1000000000) (ψ := -160941/125000) 290 232
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t152 : ((44141254047/625000000000 : ℚ) : ℝ) ≤ stT290 152 := by
  have hc : ((54421/62500 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44141254047/625000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((54421/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c153 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-747803/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 754857/1250000) (δ := 14667/1000000000) (ψ := -160941/125000) 290 232
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t153 : ((-604644424059/10000000000000 : ℚ) : ℝ) ≤ stT290 153 := by
  have hc : ((-747903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-604644424059/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-747903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c154 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-49549/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -98919/200000) (δ := 7287/500000000) (ψ := -160941/125000) 290 233
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t154 : ((-79875593229/2500000000000 : ℚ) : ℝ) ≤ stT290 154 := by
  have hc : ((-99123/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79875593229/2500000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-99123/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c155 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((248717/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63347/2500000) (δ := 14629/1000000000) (ψ := -160941/125000) 290 233
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t155 : ((49938534887/625000000000 : ℚ) : ℝ) ≤ stT290 155 := by
  have hc : ((62173/62500 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49938534887/625000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((62173/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c156 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-191617/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 881803/2000000) (δ := 7287/500000000) (ψ := -160941/125000) 290 233
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t156 : ((-153496490597/10000000000000 : ℚ) : ℝ) ≤ stT290 156 := by
  have hc : ((-191717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153496490597/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-191717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c157 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-889267/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6666343/10000000) (δ := 7341/500000000) (ψ := -160941/125000) 290 234
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t157 : ((-709792240929/10000000000000 : ℚ) : ℝ) ≤ stT290 157 := by
  have hc : ((-889367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-709792240929/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-889367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c158 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((678359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2063173/10000000) (δ := 7341/500000000) (ψ := -160941/125000) 290 234
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t158 : ((539593695263/10000000000000 : ℚ) : ℝ) ≤ stT290 158 := by
  have hc : ((678259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((539593695263/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((678259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c159 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((134149/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2510997/10000000) (δ := 7341/500000000) (ψ := -160941/125000) 290 234
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t159 : ((26591793081/625000000000 : ℚ) : ℝ) ≤ stT290 159 := by
  have hc : ((33531/62500 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26591793081/625000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((33531/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c160 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-474773/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7056457/10000000) (δ := 7341/500000000) (ψ := -160941/125000) 290 234
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t160 : ((-37538081911/500000000000 : ℚ) : ℝ) ≤ stT290 160 := by
  have hc : ((-474823/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37538081911/500000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-474823/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c161 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-41433/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2067197/5000000) (δ := 14589/1000000000) (ψ := -160941/125000) 290 235
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t161 : ((-32693208613/5000000000000 : ℚ) : ℝ) ≤ stT290 161 := by
  have hc : ((-41483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32693208613/5000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-41483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c162 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((494973/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 177403/5000000) (δ := 14589/1000000000) (ψ := -160941/125000) 290 235
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t162 : ((194424066551/2500000000000 : ℚ) : ℝ) ≤ stT290 162 := by
  have hc : ((494923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194424066551/2500000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((494923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c163 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-3483/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4816383/10000000) (δ := 7307/500000000) (ψ := -160941/125000) 290 235
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t163 : ((-682220331/25000000000 : ℚ) : ℝ) ≤ stT290 163 := by
  have hc : ((-871/2500 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-682220331/25000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-871/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c164 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-847967/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1291467/2000000) (δ := 14507/1000000000) (ψ := -160941/125000) 290 236
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t164 : ((-662229230223/10000000000000 : ℚ) : ℝ) ≤ stT290 164 := by
  have hc : ((-848067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-662229230223/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-848067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c165 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((170551/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -102503/500000) (δ := 14507/1000000000) (ψ := -160941/125000) 290 236
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t165 : ((33188537487/625000000000 : ℚ) : ℝ) ≤ stT290 165 := by
  have hc : ((85263/125000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33188537487/625000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((85263/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c166 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((298017/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 145663/625000) (δ := 1837/125000000) (ψ := -160941/125000) 290 236
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t166 : ((4625341741/100000000000 : ℚ) : ℝ) ≤ stT290 166 := by
  have hc : ((297967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4625341741/100000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((297967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c167 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-892661/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 668503/1000000) (δ := 14507/1000000000) (ψ := -160941/125000) 290 236
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t167 : ((-10794373251/156250000000 : ℚ) : ℝ) ≤ stT290 167 := by
  have hc : ((-892761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10794373251/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-892761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c168 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-151123/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4694611/10000000) (δ := 73/5000000) (ψ := -160941/125000) 290 237
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t168 : ((-116632539441/5000000000000 : ℚ) : ℝ) ≤ stT290 168 := by
  have hc : ((-151173/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116632539441/5000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-151173/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c169 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((987739/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -391881/10000000) (δ := 73/5000000) (ψ := -160941/125000) 290 237
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t169 : ((75972154797/1000000000000 : ℚ) : ℝ) ≤ stT290 169 := by
  have hc : ((987639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75972154797/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((987639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c170 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((3327/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1942701/5000000) (δ := 14603/1000000000) (ψ := -160941/125000) 290 237
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t170 : ((634087487/500000000000 : ℚ) : ℝ) ≤ stT290 170 := by
  have hc : ((3307/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((634087487/500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((3307/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c171 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-248393/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1892591/2500000) (δ := 1451/100000000) (ψ := -160941/125000) 290 238
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t171 : ((-1187313831/15625000000 : ℚ) : ℝ) ≤ stT290 171 := by
  have hc : ((-124209/125000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1187313831/15625000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-124209/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c172 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((57873/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1671481/5000000) (δ := 14693/1000000000) (ψ := -160941/125000) 290 238
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t172 : ((1378394913/78125000000 : ℚ) : ℝ) ≤ stT290 172 := by
  have hc : ((7231/31250 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1378394913/78125000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((7231/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c173 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((470711/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26873/312500) (δ := 1451/100000000) (ψ := -160941/125000) 290 238
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t173 : ((71567299677/1000000000000 : ℚ) : ℝ) ≤ stT290 173 := by
  have hc : ((470661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71567299677/1000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((470661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c174 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-430143/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2519309/5000000) (δ := 14693/1000000000) (ψ := -160941/125000) 290 238
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t174 : ((-326166788057/10000000000000 : ℚ) : ℝ) ≤ stT290 174 := by
  have hc : ((-430243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-326166788057/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-430243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c175 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-429941/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6514587/10000000) (δ := 14617/1000000000) (ψ := -160941/125000) 290 239
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t175 : ((-325042666639/5000000000000 : ℚ) : ℝ) ≤ stT290 175 := by
  have hc : ((-429991/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-325042666639/5000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-429991/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c176 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((289451/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2383537/10000000) (δ := 14617/1000000000) (ψ := -160941/125000) 290 239
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t176 : ((109072053489/2500000000000 : ℚ) : ℝ) ≤ stT290 176 := by
  have hc : ((289401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109072053489/2500000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((289401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c177 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((385729/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 215521/1250000) (δ := 14617/1000000000) (ψ := -160941/125000) 290 239
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t177 : ((144947038817/2500000000000 : ℚ) : ℝ) ≤ stT290 177 := by
  have hc : ((385679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144947038817/2500000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((385679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c178 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-85449/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5808673/10000000) (δ := 14617/1000000000) (ψ := -160941/125000) 290 239
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t178 : ((-32028064509/625000000000 : ℚ) : ℝ) ≤ stT290 178 := by
  have hc : ((-170923/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32028064509/625000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-170923/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c179 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-345999/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5837623/10000000) (δ := 581/40000000) (ψ := -160941/125000) 290 240
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t179 : ((-64662370091/1250000000000 : ℚ) : ℝ) ≤ stT290 179 := by
  have hc : ((-346049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64662370091/1250000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-346049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c180 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((376081/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -224831/1250000) (δ := 581/40000000) (ψ := -160941/125000) 290 240
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t180 : ((56055317201/1000000000000 : ℚ) : ℝ) ≤ stT290 180 := by
  have hc : ((376031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56055317201/1000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((376031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c181 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((315793/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2217997/10000000) (δ := 581/40000000) (ψ := -160941/125000) 290 240
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t181 : ((117344938721/2500000000000 : ℚ) : ℝ) ≤ stT290 181 := by
  have hc : ((315743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117344938721/2500000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((315743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c182 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-396033/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6212457/10000000) (δ := 581/40000000) (ψ := -160941/125000) 290 240
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t182 : ((-234877219/4000000000 : ℚ) : ℝ) ≤ stT290 182 := by
  have hc : ((-396083/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234877219/4000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-396083/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c183 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-18621/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5522869/10000000) (δ := 14571/1000000000) (ψ := -160941/125000) 290 241
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t183 : ((-55069451723/1250000000000 : ℚ) : ℝ) ≤ stT290 183 := by
  have hc : ((-148993/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55069451723/1250000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-148993/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c184 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((161751/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1571909/10000000) (δ := 14571/1000000000) (ψ := -160941/125000) 290 241
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t184 : ((119229548779/2000000000000 : ℚ) : ℝ) ≤ stT290 184 := by
  have hc : ((161731/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119229548779/2000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((161731/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c185 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((58731/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73677/312500) (δ := 1829/125000000) (ψ := -160941/125000) 290 241
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t185 : ((21586250647/500000000000 : ℚ) : ℝ) ≤ stT290 185 := by
  have hc : ((58721/100000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21586250647/500000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((58721/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c186 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-201239/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3132997/5000000) (δ := 1829/125000000) (ψ := -160941/125000) 290 241
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t186 : ((-2305843911/39062500000 : ℚ) : ℝ) ≤ stT290 186 := by
  have hc : ((-12579/15625 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2305843911/39062500000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-12579/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c187 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-605991/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -138863/250000) (δ := 1833/125000000) (ψ := -160941/125000) 290 242
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t187 : ((-443217983843/10000000000000 : ℚ) : ℝ) ≤ stT290 187 := by
  have hc : ((-606091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-443217983843/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-606091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c188 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((780613/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1687877/10000000) (δ := 14539/1000000000) (ψ := -160941/125000) 290 242
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t188 : ((142311715803/2500000000000 : ℚ) : ℝ) ≤ stT290 188 := by
  have hc : ((780513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142311715803/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((780513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c189 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((81239/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26979/125000) (δ := 1833/125000000) (ψ := -160941/125000) 290 242
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t189 : ((3692719143/78125000000 : ℚ) : ℝ) ≤ stT290 189 := by
  have hc : ((162453/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3692719143/78125000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((162453/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c190 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-146619/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1196829/2000000) (δ := 1833/125000000) (ψ := -160941/125000) 290 242
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t190 : ((-106383221803/2000000000000 : ℚ) : ℝ) ≤ stT290 190 := by
  have hc : ((-146639/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106383221803/2000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-146639/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c191 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-714847/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5918003/10000000) (δ := 14557/1000000000) (ψ := -160941/125000) 290 243
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t191 : ((-20692711021/400000000000 : ℚ) : ℝ) ≤ stT290 191 := by
  have hc : ((-714947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20692711021/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-714947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c192 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((657839/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17057/80000) (δ := 7323/500000000) (ψ := -160941/125000) 290 243
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t192 : ((474681685693/10000000000000 : ℚ) : ℝ) ≤ stT290 192 := by
  have hc : ((657739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((474681685693/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((657739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c193 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((396937/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 326821/2000000) (δ := 7323/500000000) (ψ := -160941/125000) 290 243
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t193 : ((57137043181/1000000000000 : ℚ) : ℝ) ≤ stT290 193 := by
  have hc : ((396887/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57137043181/1000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((396887/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c194 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-549333/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1076181/2000000) (δ := 7323/500000000) (ψ := -160941/125000) 290 243
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t194 : ((-394470367247/10000000000000 : ℚ) : ℝ) ≤ stT290 194 := by
  have hc : ((-549433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-394470367247/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-549433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c195 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-87673/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -824943/1250000) (δ := 293/20000000) (ψ := -160941/125000) 290 244
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t195 : ((-12558222309/200000000000 : ℚ) : ℝ) ≤ stT290 195 := by
  have hc : ((-87683/100000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12558222309/200000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-87683/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c196 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((201301/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -361387/1250000) (δ := 14553/1000000000) (ψ := -160941/125000) 290 244
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t196 : ((28750114107/1000000000000 : ℚ) : ℝ) ≤ stT290 196 := by
  have hc : ((201251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28750114107/1000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((201251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c197 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((59339/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 798501/10000000) (δ := 293/20000000) (ψ := -160941/125000) 290 244
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t197 : ((16909121757/250000000000 : ℚ) : ℝ) ≤ stT290 197 := by
  have hc : ((237331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16909121757/250000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((237331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c198 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-215263/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2234697/5000000) (δ := 14553/1000000000) (ψ := -160941/125000) 290 244
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t198 : ((-15305202321/1000000000000 : ℚ) : ℝ) ≤ stT290 198 := by
  have hc : ((-215363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15305202321/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-215363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c199 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-994267/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1896541/2500000) (δ := 733/50000000) (ψ := -160941/125000) 290 245
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t199 : ((-352444433847/5000000000000 : ℚ) : ℝ) ≤ stT290 199 := by
  have hc : ((-994367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-352444433847/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-994367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c200 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-2511/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1976051/5000000) (δ := 14543/1000000000) (ψ := -160941/125000) 290 245
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t200 : ((-224152919/312500000000 : ℚ) : ℝ) ≤ stT290 200 := by
  have hc : ((-317/31250 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224152919/312500000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-317/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c201 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((990977/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -84023/2500000) (δ := 14543/1000000000) (ψ := -160941/125000) 290 245
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t201 : ((139782027513/2000000000000 : ℚ) : ℝ) ≤ stT290 201 := by
  have hc : ((990877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139782027513/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((990877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c202 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((131461/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1630933/5000000) (δ := 733/50000000) (ψ := -160941/125000) 290 245
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t202 : ((92460385367/5000000000000 : ℚ) : ℝ) ≤ stT290 202 := by
  have hc : ((131411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92460385367/5000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((131411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c203 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-183841/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6842133/10000000) (δ := 14543/1000000000) (ψ := -160941/125000) 290 245
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t203 : ((-129045233043/2000000000000 : ℚ) : ℝ) ≤ stT290 203 := by
  have hc : ((-183861/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129045233043/2000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-183861/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c204 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-523093/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -265159/500000) (δ := 1821/125000000) (ψ := -160941/125000) 290 246
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t204 : ((-366308870213/10000000000000 : ℚ) : ℝ) ≤ stT290 204 := by
  have hc : ((-523193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-366308870213/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-523193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c205 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((152559/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -175793/1000000) (δ := 1821/125000000) (ψ := -160941/125000) 290 246
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t205 : ((10653781377/200000000000 : ℚ) : ℝ) ≤ stT290 205 := by
  have hc : ((152539/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10653781377/200000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((152539/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c206 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((759647/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 354013/2000000) (δ := 1821/125000000) (ψ := -160941/125000) 290 246
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t206 : ((529201459951/10000000000000 : ℚ) : ℝ) ≤ stT290 206 := by
  have hc : ((759547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((529201459951/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((759547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c207 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-257747/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 105619/200000) (δ := 1821/125000000) (ψ := -160941/125000) 290 246
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t207 : ((-179181547053/5000000000000 : ℚ) : ℝ) ≤ stT290 207 := by
  have hc : ((-257797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179181547053/5000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-257797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c208 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-93291/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6933021/10000000) (δ := 227/15625000) (ψ := -160941/125000) 290 247
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t208 : ((-505411517/7812500000 : ℚ) : ℝ) ≤ stT290 208 := by
  have hc : ((-93301/100000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-505411517/7812500000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-93301/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c209 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((46843/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -107993/312500) (δ := 227/15625000) (ψ := -160941/125000) 290 247
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t209 : ((8096166513/625000000000 : ℚ) : ℝ) ≤ stT290 209 := by
  have hc : ((23409/125000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8096166513/625000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((23409/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c210 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((499999/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4867/10000000) (δ := 587/40000000) (ψ := -160941/125000) 290 247
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t210 : ((68999461337/1000000000000 : ℚ) : ℝ) ≤ stT290 210 := by
  have hc : ((499949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68999461337/1000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((499949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c211 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((190013/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 862263/2500000) (δ := 587/40000000) (ψ := -160941/125000) 290 247
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t211 : ((32685356691/2500000000000 : ℚ) : ℝ) ≤ stT290 211 := by
  have hc : ((189913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32685356691/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((189913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c212 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-231149/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1719231/2500000) (δ := 227/15625000) (ψ := -160941/125000) 290 247
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t212 : ((-79385498361/1250000000000 : ℚ) : ℝ) ≤ stT290 212 := by
  have hc : ((-115587/125000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79385498361/1250000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-115587/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c213 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-70261/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2709631/5000000) (δ := 14621/1000000000) (ψ := -160941/125000) 290 248
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t213 : ((-96301258383/2500000000000 : ℚ) : ℝ) ≤ stT290 213 := by
  have hc : ((-140547/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96301258383/2500000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-140547/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c214 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((21561/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1011717/5000000) (δ := 7291/500000000) (ψ := -160941/125000) 290 248
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t214 : ((23578623971/500000000000 : ℚ) : ℝ) ≤ stT290 214 := by
  have hc : ((172463/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23578623971/500000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((172463/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c215 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((428183/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 339129/2500000) (δ := 7291/500000000) (ψ := -160941/125000) 290 248
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t215 : ((145992068601/2500000000000 : ℚ) : ℝ) ≤ stT290 215 := by
  have hc : ((428133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145992068601/2500000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((428133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c216 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-312217/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2360403/5000000) (δ := 7291/500000000) (ψ := -160941/125000) 290 248
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t216 : ((-106252429619/5000000000000 : ℚ) : ℝ) ≤ stT290 216 := by
  have hc : ((-312317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106252429619/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-312317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c217 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-498143/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1527691/2000000) (δ := 7257/500000000) (ψ := -160941/125000) 290 249
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t217 : ((-67639165417/1000000000000 : ℚ) : ℝ) ≤ stT290 217 := by
  have hc : ((-498193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67639165417/1000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-498193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c218 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-37669/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2152561/5000000) (δ := 14689/1000000000) (ψ := -160941/125000) 290 249
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t218 : ((-6382404621/625000000000 : ℚ) : ℝ) ≤ stT290 218 := by
  have hc : ((-18847/125000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6382404621/625000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-18847/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c219 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((923071/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -197403/2000000) (δ := 7257/500000000) (ψ := -160941/125000) 290 249
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t219 : ((623685654627/10000000000000 : ℚ) : ℝ) ≤ stT290 219 := by
  have hc : ((922971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((623685654627/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((922971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c220 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((120147/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 115797/500000) (δ := 7257/500000000) (ψ := -160941/125000) 290 249
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t220 : ((80989503273/2000000000000 : ℚ) : ℝ) ≤ stT290 220 := by
  have hc : ((120127/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80989503273/2000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((120127/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c221 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-621603/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 140099/250000) (δ := 7257/500000000) (ψ := -160941/125000) 290 249
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t221 : ((-418202822119/10000000000000 : ℚ) : ℝ) ≤ stT290 221 := by
  have hc : ((-621703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-418202822119/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-621703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c222 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-917429/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3415459/5000000) (δ := 3649/250000000) (ψ := -160941/125000) 290 250
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t222 : ((-615806011053/10000000000000 : ℚ) : ℝ) ≤ stT290 222 := by
  have hc : ((-917529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-615806011053/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-917529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c223 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((14133/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1786239/5000000) (δ := 3649/250000000) (ψ := -160941/125000) 290 250
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t223 : ((9457452827/1000000000000 : ℚ) : ℝ) ≤ stT290 223 := by
  have hc : ((14123/100000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9457452827/1000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((14123/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c224 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((495687/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -328611/10000000) (δ := 14607/1000000000) (ψ := -160941/125000) 290 250
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t224 : ((331161348461/5000000000000 : ℚ) : ℝ) ≤ stT290 224 := by
  have hc : ((495637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((331161348461/5000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((495637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c225 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((79807/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2900829/10000000) (δ := 14607/1000000000) (ψ := -160941/125000) 290 250
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t225 : ((26595640071/1000000000000 : ℚ) : ℝ) ≤ stT290 225 := by
  have hc : ((79787/200000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26595640071/1000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((79787/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c226 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-767899/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3057939/5000000) (δ := 29007/1000000000) (ψ := -160941/125000) 290 250
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t226 : ((-510866022809/10000000000000 : ℚ) : ℝ) ≤ stT290 226 := by
  have hc : ((-767999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-510866022809/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-767999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c227 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-208411/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3195587/5000000) (δ := 1813/125000000) (ψ := -160941/125000) 290 251
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t227 : ((-8646498479/156250000000 : ℚ) : ℝ) ≤ stT290 227 := by
  have hc : ((-52109/62500 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8646498479/156250000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-52109/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c228 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((142521/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -801091/2500000) (δ := 1813/125000000) (ψ := -160941/125000) 290 251
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t228 : ((47176849643/2500000000000 : ℚ) : ℝ) ≤ stT290 228 := by
  have hc : ((142471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47176849643/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((142471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c229 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((999921/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15737/5000000) (δ := 1813/125000000) (ψ := -160941/125000) 290 251
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t229 : ((330349856789/5000000000000 : ℚ) : ℝ) ≤ stT290 229 := by
  have hc : ((999821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((330349856789/5000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((999821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c230 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((314347/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 195473/625000) (δ := 14699/1000000000) (ψ := -160941/125000) 290 251
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t230 : ((10360409343/500000000000 : ℚ) : ℝ) ≤ stT290 230 := by
  have hc : ((314247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10360409343/500000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((314247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c231 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-403297/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1568227/2500000) (δ := 14699/1000000000) (ψ := -160941/125000) 290 251
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t231 : ((-8293217667/156250000000 : ℚ) : ℝ) ≤ stT290 231 := by
  have hc : ((-403347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8293217667/156250000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-403347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c232 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-81373/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1260669/2000000) (δ := 57/3906250) (ψ := -160941/125000) 290 252
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t232 : ((-53430625139/1000000000000 : ℚ) : ℝ) ≤ stT290 232 := by
  have hc : ((-81383/100000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53430625139/1000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-81383/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c233 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((7311/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3185047/10000000) (δ := 14611/1000000000) (ψ := -160941/125000) 290 252
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t233 : ((9575903657/500000000000 : ℚ) : ℝ) ≤ stT290 233 := by
  have hc : ((14617/50000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9575903657/500000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((14617/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c234 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((999487/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8009/1000000) (δ := 57/3906250) (ψ := -160941/125000) 290 252
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t234 : ((16332981741/250000000000 : ℚ) : ℝ) ≤ stT290 234 := by
  have hc : ((999387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16332981741/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((999387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c235 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((358029/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7529/25000) (δ := 57/3906250) (ψ := -160941/125000) 290 252
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t235 : ((29185888589/1250000000000 : ℚ) : ℝ) ≤ stT290 235 := by
  have hc : ((357929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29185888589/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((357929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c236 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-761271/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 761271/1250000) (δ := 14611/1000000000) (ψ := -160941/125000) 290 252
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t236 : ((-99122129119/2000000000000 : ℚ) : ℝ) ≤ stT290 236 := by
  have hc : ((-761371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99122129119/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-761371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c237 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-21687/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3276139/5000000) (δ := 7259/500000000) (ψ := -160941/125000) 290 253
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t237 : ((-2817769703/50000000000 : ℚ) : ℝ) ≤ stT290 237 := by
  have hc : ((-43379/50000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2817769703/50000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-43379/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c238 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((170099/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1749833/5000000) (δ := 2937/200000000) (ψ := -160941/125000) 290 253
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t238 : ((110193861797/10000000000000 : ℚ) : ℝ) ≤ stT290 238 := by
  have hc : ((169999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110193861797/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((169999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c239 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((983133/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -459813/10000000) (δ := 7259/500000000) (ψ := -160941/125000) 290 253
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t239 : ((317935481959/5000000000000 : ℚ) : ℝ) ≤ stT290 239 := by
  have hc : ((983033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((317935481959/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((983033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c240 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((517439/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 320919/1250000) (δ := 7259/500000000) (ψ := -160941/125000) 290 253
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t240 : ((333940772483/10000000000000 : ℚ) : ℝ) ≤ stT290 240 := by
  have hc : ((517339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((333940772483/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((517339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c241 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-153667/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2790951/5000000) (δ := 7259/500000000) (ψ := -160941/125000) 290 253
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t241 : ((-24750444411/625000000000 : ℚ) : ℝ) ≤ stT290 241 := by
  have hc : ((-38423/62500 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24750444411/625000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-38423/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c242 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-95767/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7123981/10000000) (δ := 117/8000000) (ψ := -160941/125000) 290 254
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t242 : ((-2462714001/40000000000 : ℚ) : ℝ) ≤ stT290 242 := by
  have hc : ((-95777/100000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2462714001/40000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-95777/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c243 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-20707/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4134299/10000000) (δ := 7289/500000000) (ψ := -160941/125000) 290 254
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t243 : ((-3324899683/625000000000 : ℚ) : ℝ) ≤ stT290 243 := by
  have hc : ((-5183/62500 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3324899683/625000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-5183/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c244 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((894829/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1156869/10000000) (δ := 7289/500000000) (ψ := -160941/125000) 290 254
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t244 : ((71598898767/1250000000000 : ℚ) : ℝ) ≤ stT290 244 := by
  have hc : ((894729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71598898767/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((894729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c245 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((749601/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 361669/2000000) (δ := 1161/40000000) (ψ := -160941/125000) 290 254
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t245 : ((119709550219/2500000000000 : ℚ) : ℝ) ≤ stT290 245 := by
  have hc : ((749501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119709550219/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((749501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c246 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-10239/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1190381/2500000) (δ := 117/8000000) (ψ := -160941/125000) 290 254
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t246 : ((-52241146649/2500000000000 : ℚ) : ℝ) ≤ stT290 246 := by
  have hc : ((-81937/250000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52241146649/2500000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-81937/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c247 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-99817/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 481419/625000) (δ := 117/8000000) (ψ := -160941/125000) 290 254
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t247 : ((-12703684539/200000000000 : ℚ) : ℝ) ≤ stT290 247 := by
  have hc : ((-99827/100000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12703684539/200000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-99827/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c248 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((-221791/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -507597/1000000) (δ := 14671/1000000000) (ψ := -160941/125000) 290 255
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t248 : ((-140869256841/5000000000000 : ℚ) : ℝ) ≤ stT290 248 := by
  have hc : ((-221841/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140869256841/5000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-221841/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c249 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((324929/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2158497/10000000) (δ := 3633/250000000) (ψ := -160941/125000) 290 255
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t249 : ((51470904849/1250000000000 : ℚ) : ℝ) ≤ stT290 249 := by
  have hc : ((324879/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51470904849/1250000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((324879/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_c250 :
    |Real.cos (((290 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((477823/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5979/80000) (δ := 14671/1000000000) (ψ := -160941/125000) 290 255
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st290_t250 : ((60433984543/1000000000000 : ℚ) : ℝ) ≤ stT290 250 := by
  have hc : ((477773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((290 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st290_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60433984543/1000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((477773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st290_p1 : ((55879/200000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT290 (i+1) := by
  rw [Finset.sum_range_one]
  exact st290_t1

theorem st290_p2 : ((510145129411/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT290 (i+1))
      = (∑ i ∈ Finset.range 1, stT290 (i+1)) + stT290 2 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 1
    simpa using h
  have hprev := st290_p1
  have hstep := st290_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p3 : ((2500137660677/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT290 (i+1))
      = (∑ i ∈ Finset.range 2, stT290 (i+1)) + stT290 3 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 2
    simpa using h
  have hprev := st290_p2
  have hstep := st290_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p4 : ((2965712660677/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT290 (i+1))
      = (∑ i ∈ Finset.range 3, stT290 (i+1)) + stT290 4 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 3
    simpa using h
  have hprev := st290_p3
  have hstep := st290_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p5 : ((74021051731/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT290 (i+1))
      = (∑ i ∈ Finset.range 4, stT290 (i+1)) + stT290 5 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 4
    simpa using h
  have hprev := st290_p4
  have hstep := st290_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p6 : ((2688949704097/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT290 (i+1))
      = (∑ i ∈ Finset.range 5, stT290 (i+1)) + stT290 6 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 5
    simpa using h
  have hprev := st290_p5
  have hstep := st290_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p7 : ((725509361759/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT290 (i+1))
      = (∑ i ∈ Finset.range 6, stT290 (i+1)) + stT290 7 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 6
    simpa using h
  have hprev := st290_p6
  have hstep := st290_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p8 : ((15986933407351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT290 (i+1))
      = (∑ i ∈ Finset.range 7, stT290 (i+1)) + stT290 8 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 7
    simpa using h
  have hprev := st290_p7
  have hstep := st290_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p9 : ((540942116587/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT290 (i+1))
      = (∑ i ∈ Finset.range 8, stT290 (i+1)) + stT290 9 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 8
    simpa using h
  have hprev := st290_p8
  have hstep := st290_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p10 : ((10384479710639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT290 (i+1))
      = (∑ i ∈ Finset.range 9, stT290 (i+1)) + stT290 10 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 9
    simpa using h
  have hprev := st290_p9
  have hstep := st290_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p11 : ((6288533434563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT290 (i+1))
      = (∑ i ∈ Finset.range 10, stT290 (i+1)) + stT290 11 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 10
    simpa using h
  have hprev := st290_p10
  have hstep := st290_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p12 : ((14864606303803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT290 (i+1))
      = (∑ i ∈ Finset.range 11, stT290 (i+1)) + stT290 12 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 11
    simpa using h
  have hprev := st290_p11
  have hstep := st290_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p13 : ((6261213155909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT290 (i+1))
      = (∑ i ∈ Finset.range 12, stT290 (i+1)) + stT290 13 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 12
    simpa using h
  have hprev := st290_p12
  have hstep := st290_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p14 : ((7594515140021/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT290 (i+1))
      = (∑ i ∈ Finset.range 13, stT290 (i+1)) + stT290 14 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 13
    simpa using h
  have hprev := st290_p13
  have hstep := st290_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p15 : ((1606650857389/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT290 (i+1))
      = (∑ i ∈ Finset.range 14, stT290 (i+1)) + stT290 15 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 14
    simpa using h
  have hprev := st290_p14
  have hstep := st290_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p16 : ((1722126107389/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT290 (i+1))
      = (∑ i ∈ Finset.range 15, stT290 (i+1)) + stT290 16 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 15
    simpa using h
  have hprev := st290_p15
  have hstep := st290_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p17 : ((9804053635661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT290 (i+1))
      = (∑ i ∈ Finset.range 16, stT290 (i+1)) + stT290 17 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 16
    simpa using h
  have hprev := st290_p16
  have hstep := st290_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p18 : ((1779017314379/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT290 (i+1))
      = (∑ i ∈ Finset.range 17, stT290 (i+1)) + stT290 18 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 17
    simpa using h
  have hprev := st290_p17
  have hstep := st290_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p19 : ((19600026718619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT290 (i+1))
      = (∑ i ∈ Finset.range 18, stT290 (i+1)) + stT290 19 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 18
    simpa using h
  have hprev := st290_p18
  have hstep := st290_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p20 : ((17396455494863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT290 (i+1))
      = (∑ i ∈ Finset.range 19, stT290 (i+1)) + stT290 20 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 19
    simpa using h
  have hprev := st290_p19
  have hstep := st290_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p21 : ((4262524465451/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT290 (i+1))
      = (∑ i ∈ Finset.range 20, stT290 (i+1)) + stT290 21 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 20
    simpa using h
  have hprev := st290_p20
  have hstep := st290_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p22 : ((18526587329549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT290 (i+1))
      = (∑ i ∈ Finset.range 21, stT290 (i+1)) + stT290 22 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 21
    simpa using h
  have hprev := st290_p21
  have hstep := st290_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p23 : ((20374917355181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT290 (i+1))
      = (∑ i ∈ Finset.range 22, stT290 (i+1)) + stT290 23 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 22
    simpa using h
  have hprev := st290_p22
  have hstep := st290_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p24 : ((21929220314631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT290 (i+1))
      = (∑ i ∈ Finset.range 23, stT290 (i+1)) + stT290 24 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 23
    simpa using h
  have hprev := st290_p23
  have hstep := st290_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p25 : ((22203570314631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT290 (i+1))
      = (∑ i ∈ Finset.range 24, stT290 (i+1)) + stT290 25 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 24
    simpa using h
  have hprev := st290_p24
  have hstep := st290_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p26 : ((20497690811009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT290 (i+1))
      = (∑ i ∈ Finset.range 25, stT290 (i+1)) + stT290 26 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 25
    simpa using h
  have hprev := st290_p25
  have hstep := st290_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p27 : ((19634074836261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT290 (i+1))
      = (∑ i ∈ Finset.range 26, stT290 (i+1)) + stT290 27 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 26
    simpa using h
  have hprev := st290_p26
  have hstep := st290_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p28 : ((4304691301547/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT290 (i+1))
      = (∑ i ∈ Finset.range 27, stT290 (i+1)) + stT290 28 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 27
    simpa using h
  have hprev := st290_p27
  have hstep := st290_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p29 : ((4037514616981/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT290 (i+1))
      = (∑ i ∈ Finset.range 28, stT290 (i+1)) + stT290 29 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 28
    simpa using h
  have hprev := st290_p28
  have hstep := st290_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p30 : ((5222963625349/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT290 (i+1))
      = (∑ i ∈ Finset.range 29, stT290 (i+1)) + stT290 30 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 29
    simpa using h
  have hprev := st290_p29
  have hstep := st290_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p31 : ((10170316478209/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT290 (i+1))
      = (∑ i ∈ Finset.range 30, stT290 (i+1)) + stT290 31 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 30
    simpa using h
  have hprev := st290_p30
  have hstep := st290_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p32 : ((5308336486897/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT290 (i+1))
      = (∑ i ∈ Finset.range 31, stT290 (i+1)) + stT290 32 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 31
    simpa using h
  have hprev := st290_p31
  have hstep := st290_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p33 : ((3948070577309/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT290 (i+1))
      = (∑ i ∈ Finset.range 32, stT290 (i+1)) + stT290 33 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 32
    simpa using h
  have hprev := st290_p32
  have hstep := st290_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p34 : ((1070556192913/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT290 (i+1))
      = (∑ i ∈ Finset.range 33, stT290 (i+1)) + stT290 34 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 33
    simpa using h
  have hprev := st290_p33
  have hstep := st290_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p35 : ((2087078278023/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT290 (i+1))
      = (∑ i ∈ Finset.range 34, stT290 (i+1)) + stT290 35 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 34
    simpa using h
  have hprev := st290_p34
  have hstep := st290_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p36 : ((3906928169267/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT290 (i+1))
      = (∑ i ∈ Finset.range 35, stT290 (i+1)) + stT290 36 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 35
    simpa using h
  have hprev := st290_p35
  have hstep := st290_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p37 : ((2579245597839/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT290 (i+1))
      = (∑ i ∈ Finset.range 36, stT290 (i+1)) + stT290 37 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 36
    simpa using h
  have hprev := st290_p36
  have hstep := st290_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p38 : ((1098061553883/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT290 (i+1))
      = (∑ i ∈ Finset.range 37, stT290 (i+1)) + stT290 38 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 37
    simpa using h
  have hprev := st290_p37
  have hstep := st290_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p39 : ((10750598585299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT290 (i+1))
      = (∑ i ∈ Finset.range 38, stT290 (i+1)) + stT290 39 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 38
    simpa using h
  have hprev := st290_p38
  have hstep := st290_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p40 : ((19958192081/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT290 (i+1))
      = (∑ i ∈ Finset.range 39, stT290 (i+1)) + stT290 40 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 39
    simpa using h
  have hprev := st290_p39
  have hstep := st290_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p41 : ((9360771950671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT290 (i+1))
      = (∑ i ∈ Finset.range 40, stT290 (i+1)) + stT290 41 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 40
    simpa using h
  have hprev := st290_p40
  have hstep := st290_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p42 : ((2300242487253/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT290 (i+1))
      = (∑ i ∈ Finset.range 41, stT290 (i+1)) + stT290 42 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 41
    simpa using h
  have hprev := st290_p41
  have hstep := st290_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p43 : ((2362376476093/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT290 (i+1))
      = (∑ i ∈ Finset.range 42, stT290 (i+1)) + stT290 43 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 42
    simpa using h
  have hprev := st290_p42
  have hstep := st290_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p44 : ((2486032249437/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT290 (i+1))
      = (∑ i ∈ Finset.range 43, stT290 (i+1)) + stT290 44 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 43
    simpa using h
  have hprev := st290_p43
  have hstep := st290_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p45 : ((21100520578517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT290 (i+1))
      = (∑ i ∈ Finset.range 44, stT290 (i+1)) + stT290 45 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 44
    simpa using h
  have hprev := st290_p44
  have hstep := st290_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p46 : ((5593075700813/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT290 (i+1))
      = (∑ i ∈ Finset.range 45, stT290 (i+1)) + stT290 46 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 45
    simpa using h
  have hprev := st290_p45
  have hstep := st290_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p47 : ((5898735598763/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT290 (i+1))
      = (∑ i ∈ Finset.range 46, stT290 (i+1)) + stT290 47 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 46
    simpa using h
  have hprev := st290_p46
  have hstep := st290_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p48 : ((24646621504427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT290 (i+1))
      = (∑ i ∈ Finset.range 47, stT290 (i+1)) + stT290 48 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 47
    simpa using h
  have hprev := st290_p47
  have hstep := st290_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p49 : ((6336853537833/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT290 (i+1))
      = (∑ i ∈ Finset.range 48, stT290 (i+1)) + stT290 49 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 48
    simpa using h
  have hprev := st290_p48
  have hstep := st290_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p50 : ((25472222691221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT290 (i+1))
      = (∑ i ∈ Finset.range 49, stT290 (i+1)) + stT290 50 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 49
    simpa using h
  have hprev := st290_p49
  have hstep := st290_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p51 : ((6215133435287/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT290 (i+1))
      = (∑ i ∈ Finset.range 50, stT290 (i+1)) + stT290 51 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 50
    simpa using h
  have hprev := st290_p50
  have hstep := st290_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p52 : ((23622069412329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT290 (i+1))
      = (∑ i ∈ Finset.range 51, stT290 (i+1)) + stT290 52 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 51
    simpa using h
  have hprev := st290_p51
  have hstep := st290_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p53 : ((22306593044643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT290 (i+1))
      = (∑ i ∈ Finset.range 52, stT290 (i+1)) + stT290 53 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 52
    simpa using h
  have hprev := st290_p52
  have hstep := st290_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p54 : ((21756527315451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT290 (i+1))
      = (∑ i ∈ Finset.range 53, stT290 (i+1)) + stT290 54 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 53
    simpa using h
  have hprev := st290_p53
  have hstep := st290_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p55 : ((5614126713983/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT290 (i+1))
      = (∑ i ∈ Finset.range 54, stT290 (i+1)) + stT290 55 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 54
    simpa using h
  have hprev := st290_p54
  have hstep := st290_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p56 : ((11895976805587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT290 (i+1))
      = (∑ i ∈ Finset.range 55, stT290 (i+1)) + stT290 56 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 55
    simpa using h
  have hprev := st290_p55
  have hstep := st290_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p57 : ((12146185536249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT290 (i+1))
      = (∑ i ∈ Finset.range 56, stT290 (i+1)) + stT290 57 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 56
    simpa using h
  have hprev := st290_p56
  have hstep := st290_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p58 : ((5826000852957/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT290 (i+1))
      = (∑ i ∈ Finset.range 57, stT290 (i+1)) + stT290 58 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 57
    simpa using h
  have hprev := st290_p57
  have hstep := st290_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p59 : ((11117290096059/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT290 (i+1))
      = (∑ i ∈ Finset.range 58, stT290 (i+1)) + stT290 59 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 58
    simpa using h
  have hprev := st290_p58
  have hstep := st290_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p60 : ((11395301780977/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT290 (i+1))
      = (∑ i ∈ Finset.range 59, stT290 (i+1)) + stT290 60 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 59
    simpa using h
  have hprev := st290_p59
  have hstep := st290_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p61 : ((11993416729601/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT290 (i+1))
      = (∑ i ∈ Finset.range 60, stT290 (i+1)) + stT290 61 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 60
    simpa using h
  have hprev := st290_p60
  have hstep := st290_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p62 : ((1176900039119/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT290 (i+1))
      = (∑ i ∈ Finset.range 61, stT290 (i+1)) + stT290 62 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 61
    simpa using h
  have hprev := st290_p61
  have hstep := st290_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p63 : ((11197233812599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT290 (i+1))
      = (∑ i ∈ Finset.range 62, stT290 (i+1)) + stT290 63 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 62
    simpa using h
  have hprev := st290_p62
  have hstep := st290_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p64 : ((11539039437599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT290 (i+1))
      = (∑ i ∈ Finset.range 63, stT290 (i+1)) + stT290 64 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 63
    simpa using h
  have hprev := st290_p63
  have hstep := st290_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p65 : ((11973304767851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT290 (i+1))
      = (∑ i ∈ Finset.range 64, stT290 (i+1)) + stT290 65 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 64
    simpa using h
  have hprev := st290_p64
  have hstep := st290_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p66 : ((22861017591517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT290 (i+1))
      = (∑ i ∈ Finset.range 65, stT290 (i+1)) + stT290 66 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 65
    simpa using h
  have hprev := st290_p65
  have hstep := st290_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p67 : ((11345419571551/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT290 (i+1))
      = (∑ i ∈ Finset.range 66, stT290 (i+1)) + stT290 67 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 66
    simpa using h
  have hprev := st290_p66
  have hstep := st290_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p68 : ((1491086300537/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT290 (i+1))
      = (∑ i ∈ Finset.range 67, stT290 (i+1)) + stT290 68 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 67
    simpa using h
  have hprev := st290_p67
  have hstep := st290_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p69 : ((23032184822311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT290 (i+1))
      = (∑ i ∈ Finset.range 68, stT290 (i+1)) + stT290 69 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 68
    simpa using h
  have hprev := st290_p68
  have hstep := st290_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p70 : ((22706315197293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT290 (i+1))
      = (∑ i ∈ Finset.range 69, stT290 (i+1)) + stT290 70 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 69
    simpa using h
  have hprev := st290_p69
  have hstep := st290_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p71 : ((23831673159857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT290 (i+1))
      = (∑ i ∈ Finset.range 70, stT290 (i+1)) + stT290 71 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 70
    simpa using h
  have hprev := st290_p70
  have hstep := st290_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p72 : ((22853340851153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT290 (i+1))
      = (∑ i ∈ Finset.range 71, stT290 (i+1)) + stT290 72 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 71
    simpa using h
  have hprev := st290_p71
  have hstep := st290_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p73 : ((22994171725139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT290 (i+1))
      = (∑ i ∈ Finset.range 72, stT290 (i+1)) + stT290 73 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 72
    simpa using h
  have hprev := st290_p72
  have hstep := st290_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p74 : ((23728002137279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT290 (i+1))
      = (∑ i ∈ Finset.range 73, stT290 (i+1)) + stT290 74 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 73
    simpa using h
  have hprev := st290_p73
  have hstep := st290_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p75 : ((5645976766491/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT290 (i+1))
      = (∑ i ∈ Finset.range 74, stT290 (i+1)) + stT290 75 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 74
    simpa using h
  have hprev := st290_p74
  have hstep := st290_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p76 : ((5888435790429/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT290 (i+1))
      = (∑ i ∈ Finset.range 75, stT290 (i+1)) + stT290 76 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 75
    simpa using h
  have hprev := st290_p75
  have hstep := st290_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p77 : ((1447121519099/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT290 (i+1))
      = (∑ i ∈ Finset.range 76, stT290 (i+1)) + stT290 77 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 76
    simpa using h
  have hprev := st290_p76
  have hstep := st290_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p78 : ((11441214851287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT290 (i+1))
      = (∑ i ∈ Finset.range 77, stT290 (i+1)) + stT290 78 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 77
    simpa using h
  have hprev := st290_p77
  have hstep := st290_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p79 : ((5921323508987/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT290 (i+1))
      = (∑ i ∈ Finset.range 78, stT290 (i+1)) + stT290 79 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 78
    simpa using h
  have hprev := st290_p78
  have hstep := st290_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p80 : ((11303792084113/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT290 (i+1))
      = (∑ i ∈ Finset.range 79, stT290 (i+1)) + stT290 80 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 79
    simpa using h
  have hprev := st290_p79
  have hstep := st290_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p81 : ((473966881183/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT290 (i+1))
      = (∑ i ∈ Finset.range 80, stT290 (i+1)) + stT290 81 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 80
    simpa using h
  have hprev := st290_p80
  have hstep := st290_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p82 : ((11395878471633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT290 (i+1))
      = (∑ i ∈ Finset.range 81, stT290 (i+1)) + stT290 82 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 81
    simpa using h
  have hprev := st290_p81
  have hstep := st290_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p83 : ((5850419546299/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT290 (i+1))
      = (∑ i ∈ Finset.range 82, stT290 (i+1)) + stT290 83 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 82
    simpa using h
  have hprev := st290_p82
  have hstep := st290_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p84 : ((45162890713/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT290 (i+1))
      = (∑ i ∈ Finset.range 83, stT290 (i+1)) + stT290 84 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 83
    simpa using h
  have hprev := st290_p83
  have hstep := st290_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p85 : ((5771982972989/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT290 (i+1))
      = (∑ i ∈ Finset.range 84, stT290 (i+1)) + stT290 85 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 84
    simpa using h
  have hprev := st290_p84
  have hstep := st290_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p86 : ((935551275599/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT290 (i+1))
      = (∑ i ∈ Finset.range 85, stT290 (i+1)) + stT290 86 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 85
    simpa using h
  have hprev := st290_p85
  have hstep := st290_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p87 : ((715012629103/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT290 (i+1))
      = (∑ i ∈ Finset.range 86, stT290 (i+1)) + stT290 87 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 86
    simpa using h
  have hprev := st290_p86
  have hstep := st290_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p88 : ((23539470080073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT290 (i+1))
      = (∑ i ∈ Finset.range 87, stT290 (i+1)) + stT290 88 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 87
    simpa using h
  have hprev := st290_p87
  have hstep := st290_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p89 : ((22777555177651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT290 (i+1))
      = (∑ i ∈ Finset.range 88, stT290 (i+1)) + stT290 89 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 88
    simpa using h
  have hprev := st290_p88
  have hstep := st290_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p90 : ((4720705593131/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT290 (i+1))
      = (∑ i ∈ Finset.range 89, stT290 (i+1)) + stT290 90 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 89
    simpa using h
  have hprev := st290_p89
  have hstep := st290_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p91 : ((2274261237827/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT290 (i+1))
      = (∑ i ∈ Finset.range 90, stT290 (i+1)) + stT290 91 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 90
    simpa using h
  have hprev := st290_p90
  have hstep := st290_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p92 : ((2361485417777/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT290 (i+1))
      = (∑ i ∈ Finset.range 91, stT290 (i+1)) + stT290 92 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 91
    simpa using h
  have hprev := st290_p91
  have hstep := st290_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p93 : ((455015552609/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT290 (i+1))
      = (∑ i ∈ Finset.range 92, stT290 (i+1)) + stT290 93 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 92
    simpa using h
  have hprev := st290_p92
  have hstep := st290_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p94 : ((23586570040801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT290 (i+1))
      = (∑ i ∈ Finset.range 93, stT290 (i+1)) + stT290 94 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 93
    simpa using h
  have hprev := st290_p93
  have hstep := st290_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p95 : ((4560178347653/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT290 (i+1))
      = (∑ i ∈ Finset.range 94, stT290 (i+1)) + stT290 95 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 94
    simpa using h
  have hprev := st290_p94
  have hstep := st290_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p96 : ((4701843261389/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT290 (i+1))
      = (∑ i ∈ Finset.range 95, stT290 (i+1)) + stT290 96 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 95
    simpa using h
  have hprev := st290_p95
  have hstep := st290_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p97 : ((11455133078843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT290 (i+1))
      = (∑ i ∈ Finset.range 96, stT290 (i+1)) + stT290 97 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 96
    simpa using h
  have hprev := st290_p96
  have hstep := st290_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p98 : ((11680937911239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT290 (i+1))
      = (∑ i ∈ Finset.range 97, stT290 (i+1)) + stT290 98 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 97
    simpa using h
  have hprev := st290_p97
  have hstep := st290_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p99 : ((11548689986009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT290 (i+1))
      = (∑ i ∈ Finset.range 98, stT290 (i+1)) + stT290 99 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 98
    simpa using h
  have hprev := st290_p98
  have hstep := st290_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p100 : ((23136466932931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT290 (i+1))
      = (∑ i ∈ Finset.range 99, stT290 (i+1)) + stT290 100 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 99
    simpa using h
  have hprev := st290_p99
  have hstep := st290_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p101 : ((2918798120297/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT290 (i+1))
      = (∑ i ∈ Finset.range 100, stT290 (i+1)) + stT290 101 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 100
    simpa using h
  have hprev := st290_p100
  have hstep := st290_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p102 : ((5718634166523/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT290 (i+1))
      = (∑ i ∈ Finset.range 101, stT290 (i+1)) + stT290 102 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 101
    simpa using h
  have hprev := st290_p101
  have hstep := st290_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p103 : ((5897623120689/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT290 (i+1))
      = (∑ i ∈ Finset.range 102, stT290 (i+1)) + stT290 103 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 102
    simpa using h
  have hprev := st290_p102
  have hstep := st290_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p104 : ((11347045219641/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT290 (i+1))
      = (∑ i ∈ Finset.range 103, stT290 (i+1)) + stT290 104 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 103
    simpa using h
  have hprev := st290_p103
  have hstep := st290_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p105 : ((11834307210141/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT290 (i+1))
      = (∑ i ∈ Finset.range 104, stT290 (i+1)) + stT290 105 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 104
    simpa using h
  have hprev := st290_p104
  have hstep := st290_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p106 : ((11376673184523/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT290 (i+1))
      = (∑ i ∈ Finset.range 105, stT290 (i+1)) + stT290 106 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 105
    simpa using h
  have hprev := st290_p105
  have hstep := st290_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p107 : ((11726943388883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT290 (i+1))
      = (∑ i ∈ Finset.range 106, stT290 (i+1)) + stT290 107 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 106
    simpa using h
  have hprev := st290_p106
  have hstep := st290_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p108 : ((11554363672033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT290 (i+1))
      = (∑ i ∈ Finset.range 107, stT290 (i+1)) + stT290 108 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 107
    simpa using h
  have hprev := st290_p107
  have hstep := st290_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p109 : ((2876386525831/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT290 (i+1))
      = (∑ i ∈ Finset.range 108, stT290 (i+1)) + stT290 109 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 108
    simpa using h
  have hprev := st290_p108
  have hstep := st290_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p110 : ((36789939143/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT290 (i+1))
      = (∑ i ∈ Finset.range 109, stT290 (i+1)) + stT290 110 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 109
    simpa using h
  have hprev := st290_p109
  have hstep := st290_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p111 : ((11347169061559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT290 (i+1))
      = (∑ i ∈ Finset.range 110, stT290 (i+1)) + stT290 111 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 110
    simpa using h
  have hprev := st290_p110
  have hstep := st290_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p112 : ((23635963667571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT290 (i+1))
      = (∑ i ∈ Finset.range 111, stT290 (i+1)) + stT290 112 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 111
    simpa using h
  have hprev := st290_p111
  have hstep := st290_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p113 : ((5721174322981/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT290 (i+1))
      = (∑ i ∈ Finset.range 112, stT290 (i+1)) + stT290 113 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 112
    simpa using h
  have hprev := st290_p112
  have hstep := st290_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p114 : ((23195434653469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT290 (i+1))
      = (∑ i ∈ Finset.range 113, stT290 (i+1)) + stT290 114 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 113
    simpa using h
  have hprev := st290_p113
  have hstep := st290_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p115 : ((937781713581/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT290 (i+1))
      = (∑ i ∈ Finset.range 114, stT290 (i+1)) + stT290 115 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 114
    simpa using h
  have hprev := st290_p114
  have hstep := st290_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p116 : ((22716399607907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT290 (i+1))
      = (∑ i ∈ Finset.range 115, stT290 (i+1)) + stT290 116 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 115
    simpa using h
  have hprev := st290_p115
  have hstep := st290_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p117 : ((23640670331907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT290 (i+1))
      = (∑ i ∈ Finset.range 116, stT290 (i+1)) + stT290 117 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 116
    simpa using h
  have hprev := st290_p116
  have hstep := st290_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p118 : ((1431952432627/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT290 (i+1))
      = (∑ i ∈ Finset.range 117, stT290 (i+1)) + stT290 118 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 117
    simpa using h
  have hprev := st290_p117
  have hstep := st290_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p119 : ((11555675672669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT290 (i+1))
      = (∑ i ∈ Finset.range 118, stT290 (i+1)) + stT290 119 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 118
    simpa using h
  have hprev := st290_p118
  have hstep := st290_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p120 : ((11772296072189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT290 (i+1))
      = (∑ i ∈ Finset.range 119, stT290 (i+1)) + stT290 120 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 119
    simpa using h
  have hprev := st290_p119
  have hstep := st290_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p121 : ((11343914211169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT290 (i+1))
      = (∑ i ∈ Finset.range 120, stT290 (i+1)) + stT290 121 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 120
    simpa using h
  have hprev := st290_p120
  have hstep := st290_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p122 : ((5879197396991/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT290 (i+1))
      = (∑ i ∈ Finset.range 121, stT290 (i+1)) + stT290 122 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 121
    simpa using h
  have hprev := st290_p121
  have hstep := st290_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p123 : ((5794923712111/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT290 (i+1))
      = (∑ i ∈ Finset.range 122, stT290 (i+1)) + stT290 123 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 122
    simpa using h
  have hprev := st290_p122
  have hstep := st290_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p124 : ((11410677567317/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT290 (i+1))
      = (∑ i ∈ Finset.range 123, stT290 (i+1)) + stT290 124 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 123
    simpa using h
  have hprev := st290_p123
  have hstep := st290_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p125 : ((23662019022091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT290 (i+1))
      = (∑ i ∈ Finset.range 124, stT290 (i+1)) + stT290 125 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 124
    simpa using h
  have hprev := st290_p124
  have hstep := st290_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p126 : ((1143640666487/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT290 (i+1))
      = (∑ i ∈ Finset.range 125, stT290 (i+1)) + stT290 126 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 125
    simpa using h
  have hprev := st290_p125
  have hstep := st290_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p127 : ((2885355091753/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT290 (i+1))
      = (∑ i ∈ Finset.range 126, stT290 (i+1)) + stT290 127 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 126
    simpa using h
  have hprev := st290_p126
  have hstep := st290_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p128 : ((23602061008597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT290 (i+1))
      = (∑ i ∈ Finset.range 127, stT290 (i+1)) + stT290 128 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 127
    simpa using h
  have hprev := st290_p127
  have hstep := st290_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p129 : ((22723004642981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT290 (i+1))
      = (∑ i ∈ Finset.range 128, stT290 (i+1)) + stT290 129 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 128
    simpa using h
  have hprev := st290_p128
  have hstep := st290_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p130 : ((4661117733073/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT290 (i+1))
      = (∑ i ∈ Finset.range 129, stT290 (i+1)) + stT290 130 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 129
    simpa using h
  have hprev := st290_p129
  have hstep := st290_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p131 : ((187782804473/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT290 (i+1))
      = (∑ i ∈ Finset.range 130, stT290 (i+1)) + stT290 131 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 130
    simpa using h
  have hprev := st290_p130
  have hstep := st290_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p132 : ((1417871775101/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT290 (i+1))
      = (∑ i ∈ Finset.range 131, stT290 (i+1)) + stT290 132 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 131
    simpa using h
  have hprev := st290_p131
  have hstep := st290_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p133 : ((5860540274347/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT290 (i+1))
      = (∑ i ∈ Finset.range 132, stT290 (i+1)) + stT290 133 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 132
    simpa using h
  have hprev := st290_p132
  have hstep := st290_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p134 : ((23364092391989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT290 (i+1))
      = (∑ i ∈ Finset.range 133, stT290 (i+1)) + stT290 134 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 133
    simpa using h
  have hprev := st290_p133
  have hstep := st290_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p135 : ((4538495148253/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT290 (i+1))
      = (∑ i ∈ Finset.range 134, stT290 (i+1)) + stT290 135 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 134
    simpa using h
  have hprev := st290_p134
  have hstep := st290_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p136 : ((23504819929973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT290 (i+1))
      = (∑ i ∈ Finset.range 135, stT290 (i+1)) + stT290 136 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 135
    simpa using h
  have hprev := st290_p135
  have hstep := st290_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p137 : ((23311505199671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT290 (i+1))
      = (∑ i ∈ Finset.range 136, stT290 (i+1)) + stT290 137 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 136
    simpa using h
  have hprev := st290_p136
  have hstep := st290_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p138 : ((22698181341227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT290 (i+1))
      = (∑ i ∈ Finset.range 137, stT290 (i+1)) + stT290 138 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 137
    simpa using h
  have hprev := st290_p137
  have hstep := st290_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p139 : ((23512952430403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT290 (i+1))
      = (∑ i ∈ Finset.range 138, stT290 (i+1)) + stT290 139 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 138
    simpa using h
  have hprev := st290_p138
  have hstep := st290_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p140 : ((2915354034711/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT290 (i+1))
      = (∑ i ∈ Finset.range 139, stT290 (i+1)) + stT290 140 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 139
    simpa using h
  have hprev := st290_p139
  have hstep := st290_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p141 : ((2836204589529/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT290 (i+1))
      = (∑ i ∈ Finset.range 140, stT290 (i+1)) + stT290 141 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 140
    simpa using h
  have hprev := st290_p140
  have hstep := st290_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p142 : ((23471316194931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT290 (i+1))
      = (∑ i ∈ Finset.range 141, stT290 (i+1)) + stT290 142 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 141
    simpa using h
  have hprev := st290_p141
  have hstep := st290_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p143 : ((23394202882929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT290 (i+1))
      = (∑ i ∈ Finset.range 142, stT290 (i+1)) + stT290 143 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 142
    simpa using h
  have hprev := st290_p142
  have hstep := st290_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p144 : ((22680367311861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT290 (i+1))
      = (∑ i ∈ Finset.range 143, stT290 (i+1)) + stT290 144 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 143
    simpa using h
  have hprev := st290_p143
  have hstep := st290_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p145 : ((4673855082057/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT290 (i+1))
      = (∑ i ∈ Finset.range 144, stT290 (i+1)) + stT290 145 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 144
    simpa using h
  have hprev := st290_p144
  have hstep := st290_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p146 : ((235091762423/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT290 (i+1))
      = (∑ i ∈ Finset.range 145, stT290 (i+1)) + stT290 146 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 145
    simpa using h
  have hprev := st290_p145
  have hstep := st290_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p147 : ((22707703496429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT290 (i+1))
      = (∑ i ∈ Finset.range 146, stT290 (i+1)) + stT290 147 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 146
    simpa using h
  have hprev := st290_p146
  have hstep := st290_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p148 : ((4638918876091/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT290 (i+1))
      = (∑ i ∈ Finset.range 147, stT290 (i+1)) + stT290 148 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 147
    simpa using h
  have hprev := st290_p147
  have hstep := st290_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p149 : ((5906486224529/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT290 (i+1))
      = (∑ i ∈ Finset.range 148, stT290 (i+1)) + stT290 149 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 148
    simpa using h
  have hprev := st290_p148
  have hstep := st290_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p150 : ((22823396116367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT290 (i+1))
      = (∑ i ∈ Finset.range 149, stT290 (i+1)) + stT290 150 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 149
    simpa using h
  have hprev := st290_p149
  have hstep := st290_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p151 : ((22961386078587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT290 (i+1))
      = (∑ i ∈ Finset.range 150, stT290 (i+1)) + stT290 151 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 150
    simpa using h
  have hprev := st290_p150
  have hstep := st290_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p152 : ((23667646143339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT290 (i+1))
      = (∑ i ∈ Finset.range 151, stT290 (i+1)) + stT290 152 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 151
    simpa using h
  have hprev := st290_p151
  have hstep := st290_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p153 : ((288287521491/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT290 (i+1))
      = (∑ i ∈ Finset.range 152, stT290 (i+1)) + stT290 153 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 152
    simpa using h
  have hprev := st290_p152
  have hstep := st290_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p154 : ((5685874836591/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT290 (i+1))
      = (∑ i ∈ Finset.range 153, stT290 (i+1)) + stT290 154 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 153
    simpa using h
  have hprev := st290_p153
  have hstep := st290_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p155 : ((5885628976139/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT290 (i+1))
      = (∑ i ∈ Finset.range 154, stT290 (i+1)) + stT290 155 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 154
    simpa using h
  have hprev := st290_p154
  have hstep := st290_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p156 : ((23389019413959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT290 (i+1))
      = (∑ i ∈ Finset.range 155, stT290 (i+1)) + stT290 156 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 155
    simpa using h
  have hprev := st290_p155
  have hstep := st290_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p157 : ((2267922717303/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT290 (i+1))
      = (∑ i ∈ Finset.range 156, stT290 (i+1)) + stT290 157 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 156
    simpa using h
  have hprev := st290_p156
  have hstep := st290_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p158 : ((23218820868293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT290 (i+1))
      = (∑ i ∈ Finset.range 157, stT290 (i+1)) + stT290 158 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 157
    simpa using h
  have hprev := st290_p157
  have hstep := st290_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p159 : ((23644289557589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT290 (i+1))
      = (∑ i ∈ Finset.range 158, stT290 (i+1)) + stT290 159 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 158
    simpa using h
  have hprev := st290_p158
  have hstep := st290_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p160 : ((22893527919369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT290 (i+1))
      = (∑ i ∈ Finset.range 159, stT290 (i+1)) + stT290 160 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 159
    simpa using h
  have hprev := st290_p159
  have hstep := st290_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p161 : ((22828141502143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT290 (i+1))
      = (∑ i ∈ Finset.range 160, stT290 (i+1)) + stT290 161 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 160
    simpa using h
  have hprev := st290_p160
  have hstep := st290_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p162 : ((23605837768347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT290 (i+1))
      = (∑ i ∈ Finset.range 161, stT290 (i+1)) + stT290 162 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 161
    simpa using h
  have hprev := st290_p161
  have hstep := st290_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p163 : ((23332949635947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT290 (i+1))
      = (∑ i ∈ Finset.range 162, stT290 (i+1)) + stT290 163 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 162
    simpa using h
  have hprev := st290_p162
  have hstep := st290_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p164 : ((5667680101431/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT290 (i+1))
      = (∑ i ∈ Finset.range 163, stT290 (i+1)) + stT290 164 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 163
    simpa using h
  have hprev := st290_p163
  have hstep := st290_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p165 : ((5800434251379/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT290 (i+1))
      = (∑ i ∈ Finset.range 164, stT290 (i+1)) + stT290 165 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 164
    simpa using h
  have hprev := st290_p164
  have hstep := st290_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p166 : ((739508474363/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT290 (i+1))
      = (∑ i ∈ Finset.range 165, stT290 (i+1)) + stT290 166 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 165
    simpa using h
  have hprev := st290_p165
  have hstep := st290_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p167 : ((717919727861/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT290 (i+1))
      = (∑ i ∈ Finset.range 166, stT290 (i+1)) + stT290 167 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 166
    simpa using h
  have hprev := st290_p166
  have hstep := st290_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p168 : ((2274016621267/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT290 (i+1))
      = (∑ i ∈ Finset.range 167, stT290 (i+1)) + stT290 168 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 167
    simpa using h
  have hprev := st290_p167
  have hstep := st290_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p169 : ((18359287313/7812500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT290 (i+1))
      = (∑ i ∈ Finset.range 168, stT290 (i+1)) + stT290 169 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 168
    simpa using h
  have hprev := st290_p168
  have hstep := st290_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p170 : ((1175628475519/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT290 (i+1))
      = (∑ i ∈ Finset.range 169, stT290 (i+1)) + stT290 170 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 169
    simpa using h
  have hprev := st290_p169
  have hstep := st290_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p171 : ((1137634432927/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT290 (i+1))
      = (∑ i ∈ Finset.range 170, stT290 (i+1)) + stT290 171 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 170
    simpa using h
  have hprev := st290_p170
  have hstep := st290_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p172 : ((5732280801851/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT290 (i+1))
      = (∑ i ∈ Finset.range 171, stT290 (i+1)) + stT290 172 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 171
    simpa using h
  have hprev := st290_p171
  have hstep := st290_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p173 : ((11822398102087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT290 (i+1))
      = (∑ i ∈ Finset.range 172, stT290 (i+1)) + stT290 173 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 172
    simpa using h
  have hprev := st290_p172
  have hstep := st290_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p174 : ((23318629416117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT290 (i+1))
      = (∑ i ∈ Finset.range 173, stT290 (i+1)) + stT290 174 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 173
    simpa using h
  have hprev := st290_p173
  have hstep := st290_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p175 : ((22668544082839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT290 (i+1))
      = (∑ i ∈ Finset.range 174, stT290 (i+1)) + stT290 175 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 174
    simpa using h
  have hprev := st290_p174
  have hstep := st290_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p176 : ((4620966459359/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT290 (i+1))
      = (∑ i ∈ Finset.range 175, stT290 (i+1)) + stT290 176 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 175
    simpa using h
  have hprev := st290_p175
  have hstep := st290_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p177 : ((23684620452063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT290 (i+1))
      = (∑ i ∈ Finset.range 176, stT290 (i+1)) + stT290 177 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 176
    simpa using h
  have hprev := st290_p176
  have hstep := st290_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p178 : ((23172171419919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT290 (i+1))
      = (∑ i ∈ Finset.range 177, stT290 (i+1)) + stT290 178 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 177
    simpa using h
  have hprev := st290_p177
  have hstep := st290_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p179 : ((22654872459191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT290 (i+1))
      = (∑ i ∈ Finset.range 178, stT290 (i+1)) + stT290 179 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 178
    simpa using h
  have hprev := st290_p178
  have hstep := st290_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p180 : ((23215425631201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT290 (i+1))
      = (∑ i ∈ Finset.range 179, stT290 (i+1)) + stT290 180 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 179
    simpa using h
  have hprev := st290_p179
  have hstep := st290_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p181 : ((4736961077217/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT290 (i+1))
      = (∑ i ∈ Finset.range 180, stT290 (i+1)) + stT290 181 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 180
    simpa using h
  have hprev := st290_p180
  have hstep := st290_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p182 : ((4619522467717/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT290 (i+1))
      = (∑ i ∈ Finset.range 181, stT290 (i+1)) + stT290 182 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 181
    simpa using h
  have hprev := st290_p181
  have hstep := st290_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p183 : ((22657056724801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT290 (i+1))
      = (∑ i ∈ Finset.range 182, stT290 (i+1)) + stT290 183 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 182
    simpa using h
  have hprev := st290_p182
  have hstep := st290_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p184 : ((2906650558587/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT290 (i+1))
      = (∑ i ∈ Finset.range 183, stT290 (i+1)) + stT290 184 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 183
    simpa using h
  have hprev := st290_p183
  have hstep := st290_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p185 : ((5921232370409/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT290 (i+1))
      = (∑ i ∈ Finset.range 184, stT290 (i+1)) + stT290 185 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 184
    simpa using h
  have hprev := st290_p184
  have hstep := st290_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p186 : ((1154731672021/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT290 (i+1))
      = (∑ i ∈ Finset.range 185, stT290 (i+1)) + stT290 186 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 185
    simpa using h
  have hprev := st290_p185
  have hstep := st290_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p187 : ((22651415456577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT290 (i+1))
      = (∑ i ∈ Finset.range 186, stT290 (i+1)) + stT290 187 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 186
    simpa using h
  have hprev := st290_p186
  have hstep := st290_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p188 : ((23220662319789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT290 (i+1))
      = (∑ i ∈ Finset.range 187, stT290 (i+1)) + stT290 188 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 187
    simpa using h
  have hprev := st290_p187
  have hstep := st290_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p189 : ((23693330370093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT290 (i+1))
      = (∑ i ∈ Finset.range 188, stT290 (i+1)) + stT290 189 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 188
    simpa using h
  have hprev := st290_p188
  have hstep := st290_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p190 : ((11580707130539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT290 (i+1))
      = (∑ i ∈ Finset.range 189, stT290 (i+1)) + stT290 190 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 189
    simpa using h
  have hprev := st290_p189
  have hstep := st290_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p191 : ((22644096485553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT290 (i+1))
      = (∑ i ∈ Finset.range 190, stT290 (i+1)) + stT290 191 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 190
    simpa using h
  have hprev := st290_p190
  have hstep := st290_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p192 : ((11559389085623/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT290 (i+1))
      = (∑ i ∈ Finset.range 191, stT290 (i+1)) + stT290 192 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 191
    simpa using h
  have hprev := st290_p191
  have hstep := st290_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p193 : ((1480634287691/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT290 (i+1))
      = (∑ i ∈ Finset.range 192, stT290 (i+1)) + stT290 193 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 192
    simpa using h
  have hprev := st290_p192
  have hstep := st290_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p194 : ((23295678235809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT290 (i+1))
      = (∑ i ∈ Finset.range 193, stT290 (i+1)) + stT290 194 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 193
    simpa using h
  have hprev := st290_p193
  have hstep := st290_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p195 : ((22667767120359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT290 (i+1))
      = (∑ i ∈ Finset.range 194, stT290 (i+1)) + stT290 195 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 194
    simpa using h
  have hprev := st290_p194
  have hstep := st290_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p196 : ((22955268261429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT290 (i+1))
      = (∑ i ∈ Finset.range 195, stT290 (i+1)) + stT290 196 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 195
    simpa using h
  have hprev := st290_p195
  have hstep := st290_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p197 : ((23631633131709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT290 (i+1))
      = (∑ i ∈ Finset.range 196, stT290 (i+1)) + stT290 197 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 196
    simpa using h
  have hprev := st290_p196
  have hstep := st290_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p198 : ((23478581108499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT290 (i+1))
      = (∑ i ∈ Finset.range 197, stT290 (i+1)) + stT290 198 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 197
    simpa using h
  have hprev := st290_p197
  have hstep := st290_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p199 : ((4554738448161/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT290 (i+1))
      = (∑ i ∈ Finset.range 198, stT290 (i+1)) + stT290 199 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 198
    simpa using h
  have hprev := st290_p198
  have hstep := st290_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p200 : ((22766519347397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT290 (i+1))
      = (∑ i ∈ Finset.range 199, stT290 (i+1)) + stT290 200 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 199
    simpa using h
  have hprev := st290_p199
  have hstep := st290_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p201 : ((11732714742481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT290 (i+1))
      = (∑ i ∈ Finset.range 200, stT290 (i+1)) + stT290 201 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 200
    simpa using h
  have hprev := st290_p200
  have hstep := st290_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p202 : ((1478146890981/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT290 (i+1))
      = (∑ i ∈ Finset.range 201, stT290 (i+1)) + stT290 202 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 201
    simpa using h
  have hprev := st290_p201
  have hstep := st290_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p203 : ((23005124090481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT290 (i+1))
      = (∑ i ∈ Finset.range 202, stT290 (i+1)) + stT290 203 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 202
    simpa using h
  have hprev := st290_p202
  have hstep := st290_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p204 : ((5659703805067/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT290 (i+1))
      = (∑ i ∈ Finset.range 203, stT290 (i+1)) + stT290 204 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 203
    simpa using h
  have hprev := st290_p203
  have hstep := st290_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p205 : ((11585752144559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT290 (i+1))
      = (∑ i ∈ Finset.range 204, stT290 (i+1)) + stT290 205 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 204
    simpa using h
  have hprev := st290_p204
  have hstep := st290_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p206 : ((23700705749069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT290 (i+1))
      = (∑ i ∈ Finset.range 205, stT290 (i+1)) + stT290 206 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 205
    simpa using h
  have hprev := st290_p205
  have hstep := st290_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p207 : ((23342342654963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT290 (i+1))
      = (∑ i ∈ Finset.range 206, stT290 (i+1)) + stT290 207 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 206
    simpa using h
  have hprev := st290_p206
  have hstep := st290_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p208 : ((22695415913203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT290 (i+1))
      = (∑ i ∈ Finset.range 207, stT290 (i+1)) + stT290 208 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 207
    simpa using h
  have hprev := st290_p207
  have hstep := st290_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p209 : ((22824954577411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT290 (i+1))
      = (∑ i ∈ Finset.range 208, stT290 (i+1)) + stT290 209 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 208
    simpa using h
  have hprev := st290_p208
  have hstep := st290_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p210 : ((23514949190781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT290 (i+1))
      = (∑ i ∈ Finset.range 209, stT290 (i+1)) + stT290 210 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 209
    simpa using h
  have hprev := st290_p209
  have hstep := st290_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p211 : ((4729138123509/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT290 (i+1))
      = (∑ i ∈ Finset.range 210, stT290 (i+1)) + stT290 211 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 210
    simpa using h
  have hprev := st290_p210
  have hstep := st290_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p212 : ((23010606630657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT290 (i+1))
      = (∑ i ∈ Finset.range 211, stT290 (i+1)) + stT290 212 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 211
    simpa using h
  have hprev := st290_p211
  have hstep := st290_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p213 : ((181003212777/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT290 (i+1))
      = (∑ i ∈ Finset.range 212, stT290 (i+1)) + stT290 213 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 212
    simpa using h
  have hprev := st290_p212
  have hstep := st290_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p214 : ((4619394815309/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT290 (i+1))
      = (∑ i ∈ Finset.range 213, stT290 (i+1)) + stT290 214 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 213
    simpa using h
  have hprev := st290_p213
  have hstep := st290_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p215 : ((23680942350949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT290 (i+1))
      = (∑ i ∈ Finset.range 214, stT290 (i+1)) + stT290 215 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 214
    simpa using h
  have hprev := st290_p214
  have hstep := st290_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p216 : ((23468437491711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT290 (i+1))
      = (∑ i ∈ Finset.range 215, stT290 (i+1)) + stT290 216 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 215
    simpa using h
  have hprev := st290_p215
  have hstep := st290_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p217 : ((22792045837541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT290 (i+1))
      = (∑ i ∈ Finset.range 216, stT290 (i+1)) + stT290 217 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 216
    simpa using h
  have hprev := st290_p216
  have hstep := st290_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p218 : ((4537985472721/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT290 (i+1))
      = (∑ i ∈ Finset.range 217, stT290 (i+1)) + stT290 218 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 217
    simpa using h
  have hprev := st290_p217
  have hstep := st290_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p219 : ((2914201627279/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT290 (i+1))
      = (∑ i ∈ Finset.range 218, stT290 (i+1)) + stT290 219 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 218
    simpa using h
  have hprev := st290_p218
  have hstep := st290_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p220 : ((23718560534597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT290 (i+1))
      = (∑ i ∈ Finset.range 219, stT290 (i+1)) + stT290 220 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 219
    simpa using h
  have hprev := st290_p219
  have hstep := st290_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p221 : ((11650178856239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT290 (i+1))
      = (∑ i ∈ Finset.range 220, stT290 (i+1)) + stT290 221 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 220
    simpa using h
  have hprev := st290_p220
  have hstep := st290_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p222 : ((907382068057/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT290 (i+1))
      = (∑ i ∈ Finset.range 221, stT290 (i+1)) + stT290 222 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 221
    simpa using h
  have hprev := st290_p221
  have hstep := st290_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p223 : ((4555825245939/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT290 (i+1))
      = (∑ i ∈ Finset.range 222, stT290 (i+1)) + stT290 223 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 222
    simpa using h
  have hprev := st290_p222
  have hstep := st290_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p224 : ((23441448926617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT290 (i+1))
      = (∑ i ∈ Finset.range 223, stT290 (i+1)) + stT290 224 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 223
    simpa using h
  have hprev := st290_p223
  have hstep := st290_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p225 : ((23707405327327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT290 (i+1))
      = (∑ i ∈ Finset.range 224, stT290 (i+1)) + stT290 225 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 224
    simpa using h
  have hprev := st290_p224
  have hstep := st290_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p226 : ((11598269652259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT290 (i+1))
      = (∑ i ∈ Finset.range 225, stT290 (i+1)) + stT290 226 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 225
    simpa using h
  have hprev := st290_p225
  have hstep := st290_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p227 : ((11321581700931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT290 (i+1))
      = (∑ i ∈ Finset.range 226, stT290 (i+1)) + stT290 227 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 226
    simpa using h
  have hprev := st290_p226
  have hstep := st290_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p228 : ((11415935400217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT290 (i+1))
      = (∑ i ∈ Finset.range 227, stT290 (i+1)) + stT290 228 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 227
    simpa using h
  have hprev := st290_p227
  have hstep := st290_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p229 : ((5873142628503/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT290 (i+1))
      = (∑ i ∈ Finset.range 228, stT290 (i+1)) + stT290 229 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 228
    simpa using h
  have hprev := st290_p228
  have hstep := st290_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p230 : ((2962472337609/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT290 (i+1))
      = (∑ i ∈ Finset.range 229, stT290 (i+1)) + stT290 230 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 229
    simpa using h
  have hprev := st290_p229
  have hstep := st290_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p231 : ((2896126596273/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT290 (i+1))
      = (∑ i ∈ Finset.range 230, stT290 (i+1)) + stT290 231 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 230
    simpa using h
  have hprev := st290_p230
  have hstep := st290_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p232 : ((11317353259397/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT290 (i+1))
      = (∑ i ∈ Finset.range 231, stT290 (i+1)) + stT290 232 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 231
    simpa using h
  have hprev := st290_p231
  have hstep := st290_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p233 : ((11413112295967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT290 (i+1))
      = (∑ i ∈ Finset.range 232, stT290 (i+1)) + stT290 233 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 232
    simpa using h
  have hprev := st290_p232
  have hstep := st290_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p234 : ((11739771930787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT290 (i+1))
      = (∑ i ∈ Finset.range 233, stT290 (i+1)) + stT290 234 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 233
    simpa using h
  have hprev := st290_p233
  have hstep := st290_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p235 : ((11856515485143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT290 (i+1))
      = (∑ i ∈ Finset.range 234, stT290 (i+1)) + stT290 235 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 234
    simpa using h
  have hprev := st290_p234
  have hstep := st290_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p236 : ((23217420324691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT290 (i+1))
      = (∑ i ∈ Finset.range 235, stT290 (i+1)) + stT290 236 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 235
    simpa using h
  have hprev := st290_p235
  have hstep := st290_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p237 : ((22653866384091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT290 (i+1))
      = (∑ i ∈ Finset.range 236, stT290 (i+1)) + stT290 237 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 236
    simpa using h
  have hprev := st290_p236
  have hstep := st290_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p238 : ((177844220671/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT290 (i+1))
      = (∑ i ∈ Finset.range 237, stT290 (i+1)) + stT290 238 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 237
    simpa using h
  have hprev := st290_p237
  have hstep := st290_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p239 : ((11699965604903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT290 (i+1))
      = (∑ i ∈ Finset.range 238, stT290 (i+1)) + stT290 239 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 238
    simpa using h
  have hprev := st290_p238
  have hstep := st290_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p240 : ((23733871982289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT290 (i+1))
      = (∑ i ∈ Finset.range 239, stT290 (i+1)) + stT290 240 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 239
    simpa using h
  have hprev := st290_p239
  have hstep := st290_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p241 : ((23337864871713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT290 (i+1))
      = (∑ i ∈ Finset.range 240, stT290 (i+1)) + stT290 241 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 240
    simpa using h
  have hprev := st290_p240
  have hstep := st290_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p242 : ((22722186371463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT290 (i+1))
      = (∑ i ∈ Finset.range 241, stT290 (i+1)) + stT290 242 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 241
    simpa using h
  have hprev := st290_p241
  have hstep := st290_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p243 : ((4533797595307/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT290 (i+1))
      = (∑ i ∈ Finset.range 242, stT290 (i+1)) + stT290 243 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 242
    simpa using h
  have hprev := st290_p242
  have hstep := st290_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p244 : ((23241779166671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT290 (i+1))
      = (∑ i ∈ Finset.range 243, stT290 (i+1)) + stT290 244 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 243
    simpa using h
  have hprev := st290_p243
  have hstep := st290_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p245 : ((23720617367547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT290 (i+1))
      = (∑ i ∈ Finset.range 244, stT290 (i+1)) + stT290 245 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 244
    simpa using h
  have hprev := st290_p244
  have hstep := st290_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p246 : ((23511652780951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT290 (i+1))
      = (∑ i ∈ Finset.range 245, stT290 (i+1)) + stT290 246 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 245
    simpa using h
  have hprev := st290_p245
  have hstep := st290_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p247 : ((22876468554001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT290 (i+1))
      = (∑ i ∈ Finset.range 246, stT290 (i+1)) + stT290 247 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 246
    simpa using h
  have hprev := st290_p246
  have hstep := st290_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p248 : ((22594730040319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT290 (i+1))
      = (∑ i ∈ Finset.range 247, stT290 (i+1)) + stT290 248 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 247
    simpa using h
  have hprev := st290_p247
  have hstep := st290_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p249 : ((23006497279111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT290 (i+1))
      = (∑ i ∈ Finset.range 248, stT290 (i+1)) + stT290 249 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 248
    simpa using h
  have hprev := st290_p248
  have hstep := st290_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_p250 : ((23610837124541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT290 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT290 (i+1))
      = (∑ i ∈ Finset.range 249, stT290 (i+1)) + stT290 250 := by
    have h := Finset.sum_range_succ (fun i => stT290 (i+1)) 249
    simpa using h
  have hprev := st290_p249
  have hstep := st290_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st290_s250 :
    |Real.sin (((290 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))
      - ((294517/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 5979/80000) (δ := 14671/1000000000) (ψ := -160941/125000) 290 255
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 290`** (evaluated boundary). -/
theorem station_290_sign : hardyG ((((290:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 290 250 (by norm_num) (by norm_num)
    ((-160941/125000 : ℚ) : ℝ)
  have hchain := st290_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT290 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((290 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-160941/125000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st290_c250
  have hsinb := abs_le.mp st290_s250
  have hbdy_lo : ((-6792324694771/420501250000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((290 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-160941/125000 : ℚ) : ℝ))) / 2
          - ((((290:ℕ)):ℝ))
            * Real.sin (((290 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-160941/125000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((290:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((290:ℝ) * Real.log (250:ℝ) - ((-160941/125000 : ℚ) : ℝ))) / 2
        - ((290:ℝ)) * Real.sin ((290:ℝ) * Real.log (250:ℝ) - ((-160941/125000 : ℚ) : ℝ))
        ≥ ((-85916803/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((290:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-85916803/1000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-85916803/1000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-85916803/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((290:ℕ)):ℝ))+1) * (((((290:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((286521778851/156250000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((23610837124541/10000000000000 : ℚ) : ℝ) + ((-6792324694771/420501250000000 : ℚ) : ℝ)
      - ((286521778851/156250000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-160941/125000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((290:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-160941/125000 : ℚ) : ℝ)
        * (riemannZeta (line ((((290:ℕ)):ℝ)))).re
      - Real.sin ((-160941/125000 : ℚ) : ℝ)
        * (riemannZeta (line ((((290:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((290:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((290:ℕ)):ℝ))
      = (((((290:ℕ)):ℝ)) * (Real.log ((((290:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((290:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_290
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
  have hθwin : |(((-160941/125000 : ℚ) : ℝ) + ((66:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((290:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((290:ℕ)):ℝ)))
    (φ := ((-160941/125000 : ℚ) : ℝ) + ((66:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-160941/125000 : ℚ) : ℝ) + ((66:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-160941/125000 : ℚ)) : ℝ) - Real.pi) + ((66:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-160941/125000 : ℚ)) : ℝ) - Real.pi) 66).1,
    (cos_sin_shift ((((-160941/125000 : ℚ)) : ℝ) - Real.pi) 66).2]
  exact cos_sin_flip ((-160941/125000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_290_sign
end AxiomAudit
