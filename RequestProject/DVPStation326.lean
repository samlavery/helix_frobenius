import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 326` (rung-335.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT326 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((326 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-176407/500000 : ℚ) : ℝ))

theorem st326_c1 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((234601/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 176407/2000000) (δ := 1/1000000000) (ψ := -176407/500000) 326 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t1 : ((14661/15625 : ℚ) : ℝ) ≤ stT326 1 := by
  have hc : ((14661/15625 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14661/15625 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((14661/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c2 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((248077/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 62057/2000000) (δ := 823/50000000) (ψ := -176407/500000) 326 36
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t2 : ((438498077871/625000000000 : ℚ) : ℝ) ≤ stT326 2 := by
  have hc : ((62013/62500 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((438498077871/625000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((62013/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c3 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((936303/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 112139/1250000) (δ := 4123/250000000) (ψ := -176407/500000) 326 57
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t3 : ((2702584946453/5000000000000 : ℚ) : ℝ) ≤ stT326 3 := by
  have hc : ((936203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2702584946453/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((936203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c4 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((497269/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10457/400000) (δ := 8159/500000000) (ψ := -176407/500000) 326 72
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t4 : ((497219/1000000 : ℚ) : ℝ) ≤ stT326 4 := by
  have hc : ((497219/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((497219/1000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((497219/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c5 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-927319/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137899/200000) (δ := 3281/200000000) (ψ := -176407/500000) 326 84
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t5 : ((-518442987123/1250000000000 : ℚ) : ℝ) ≤ stT326 5 := by
  have hc : ((-927419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-518442987123/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-927419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c6 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((991541/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 325403/10000000) (δ := 16369/1000000000) (ψ := -176407/500000) 326 93
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t6 : ((2023770018281/5000000000000 : ℚ) : ℝ) ≤ stT326 6 := by
  have hc : ((991441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2023770018281/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((991441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c7 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((993069/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 294517/10000000) (δ := 2047/125000000) (ψ := -176407/500000) 326 101
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t7 : ((938267330759/2500000000000 : ℚ) : ℝ) ≤ stT326 7 := by
  have hc : ((992969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((938267330759/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((992969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c8 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((944983/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -166627/2000000) (δ := 8213/500000000) (ψ := -176407/500000) 326 108
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t8 : ((3340665027639/10000000000000 : ℚ) : ℝ) ≤ stT326 8 := by
  have hc : ((944883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3340665027639/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((944883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c9 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((467081/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 912231/10000000) (δ := 821/50000000) (ψ := -176407/500000) 326 114
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t9 : ((1556769844323/5000000000000 : ℚ) : ℝ) ≤ stT326 9 := by
  have hc : ((467031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1556769844323/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((467031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c10 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-247007/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7466741/10000000) (δ := 16463/1000000000) (ψ := -176407/500000) 326 120
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t10 : ((-48823991181/156250000000 : ℚ) : ℝ) ≤ stT326 10 := by
  have hc : ((-30879/31250 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48823991181/156250000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-30879/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c11 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-491011/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7379219/10000000) (δ := 4123/250000000) (ψ := -176407/500000) 326 124
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t11 : ((-740302447977/2500000000000 : ℚ) : ℝ) ≤ stT326 11 := by
  have hc : ((-491061/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-740302447977/2500000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-491061/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c12 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((995151/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -246307/10000000) (δ := 131/8000000) (ψ := -176407/500000) 326 129
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t12 : ((2872464469301/10000000000000 : ℚ) : ℝ) ≤ stT326 12 := by
  have hc : ((995051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2872464469301/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((995051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c13 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((325211/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2156641/10000000) (δ := 2057/125000000) (ψ := -176407/500000) 326 133
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t13 : ((1803668067/10000000000 : ℚ) : ℝ) ≤ stT326 13 := by
  have hc : ((325161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1803668067/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((325161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c14 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((993859/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -34649/1250000) (δ := 3297/200000000) (ψ := -176407/500000) 326 137
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t14 : ((663983057127/2500000000000 : ℚ) : ℝ) ≤ stT326 14 := by
  have hc : ((993759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((663983057127/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((993759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c15 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-462519/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -859979/1250000) (δ := 8157/500000000) (ψ := -176407/500000) 326 141
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t15 : ((-1194348069741/5000000000000 : ℚ) : ℝ) ≤ stT326 15 := by
  have hc : ((-462569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1194348069741/5000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-462569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c16 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((52889/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -351211/2500000) (δ := 3287/200000000) (ψ := -176407/500000) 326 144
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t16 : ((211531/1000000 : ℚ) : ℝ) ≤ stT326 16 := by
  have hc : ((211531/250000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211531/1000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((211531/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c17 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((469321/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 176063/2000000) (δ := 16357/1000000000) (ψ := -176407/500000) 326 147
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t17 : ((284537308869/1250000000000 : ℚ) : ℝ) ≤ stT326 17 := by
  have hc : ((469271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((284537308869/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((469271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c18 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((495369/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 340521/10000000) (δ := 653/40000000) (ψ := -176407/500000) 326 150
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t18 : ((583738890009/2500000000000 : ℚ) : ℝ) ≤ stT326 18 := by
  have hc : ((495319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((583738890009/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((495319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c19 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((464753/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2718601/10000000) (δ := 16403/1000000000) (ψ := -176407/500000) 326 153
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t19 : ((1065986932521/10000000000000 : ℚ) : ℝ) ≤ stT326 19 := by
  have hc : ((464653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1065986932521/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((464653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c20 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-997279/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 958689/1250000) (δ := 16389/1000000000) (ψ := -176407/500000) 326 155
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t20 : ((-557551816443/2500000000000 : ℚ) : ℝ) ≤ stT326 20 := by
  have hc : ((-997379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-557551816443/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-997379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c21 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((49617/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61927/2000000) (δ := 16467/1000000000) (ψ := -176407/500000) 326 158
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t21 : ((13532776867/62500000000 : ℚ) : ℝ) ≤ stT326 21 := by
  have hc : ((12403/12500 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13532776867/62500000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((12403/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c22 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-913663/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6807509/10000000) (δ := 327/20000000) (ψ := -176407/500000) 326 160
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t22 : ((-243518753263/1250000000000 : ℚ) : ℝ) ≤ stT326 22 := by
  have hc : ((-913763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243518753263/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-913763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c23 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-2577/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1022041/2500000) (δ := 16331/1000000000) (ψ := -176407/500000) 326 163
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t23 : ((-1076351849/80000000000 : ℚ) : ℝ) ≤ stT326 23 := by
  have hc : ((-2581/40000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1076351849/80000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-2581/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c24 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((14796/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25563/312500) (δ := 8243/500000000) (ψ := -176407/500000) 326 165
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t24 : ((483184198351/2500000000000 : ℚ) : ℝ) ≤ stT326 24 := by
  have hc : ((236711/250000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((483184198351/2500000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((236711/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c25 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((5721/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1035987/10000000) (δ := 16303/1000000000) (ψ := -176407/500000) 326 167
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t25 : ((45763/250000 : ℚ) : ℝ) ≤ stT326 25 := by
  have hc : ((45763/50000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45763/250000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((45763/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c26 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((805681/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1584931/10000000) (δ := 3263/200000000) (ψ := -176407/500000) 326 169
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t26 : ((1579874039541/10000000000000 : ℚ) : ℝ) ≤ stT326 26 := by
  have hc : ((805581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1579874039541/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((805581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c27 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((931987/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 927349/10000000) (δ := 16329/1000000000) (ψ := -176407/500000) 326 171
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t27 : ((3586833063/20000000000 : ℚ) : ℝ) ≤ stT326 27 := by
  have hc : ((931887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3586833063/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((931887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c28 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((942901/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -424451/5000000) (δ := 2043/125000000) (ψ := -176407/500000) 326 173
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t28 : ((890863035711/5000000000000 : ℚ) : ℝ) ≤ stT326 28 := by
  have hc : ((942801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((890863035711/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((942801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c29 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((52219/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3665419/10000000) (δ := 8179/500000000) (ψ := -176407/500000) 326 175
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t29 : ((96875381057/5000000000000 : ℚ) : ℝ) ≤ stT326 29 := by
  have hc : ((52169/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96875381057/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((52169/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c30 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-987077/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7451623/10000000) (δ := 4093/250000000) (ψ := -176407/500000) 326 177
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t30 : ((-901165255167/5000000000000 : ℚ) : ℝ) ≤ stT326 30 := by
  have hc : ((-987177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-901165255167/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-987177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c31 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((28923/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1782091/5000000) (δ := 4081/250000000) (ψ := -176407/500000) 326 178
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t31 : ((51911319859/2000000000000 : ℚ) : ℝ) ≤ stT326 31 := by
  have hc : ((28903/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51911319859/2000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((28903/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c32 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((175851/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -988277/5000000) (δ := 16309/1000000000) (ψ := -176407/500000) 326 180
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t32 : ((77704806179/625000000000 : ℚ) : ℝ) ≤ stT326 32 := by
  have hc : ((87913/125000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77704806179/625000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((87913/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c33 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-491573/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7394337/10000000) (δ := 16401/1000000000) (ψ := -176407/500000) 326 181
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t33 : ((-855806011071/5000000000000 : ℚ) : ℝ) ≤ stT326 33 := by
  have hc : ((-491623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-855806011071/5000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-491623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c34 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((992391/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61721/2000000) (δ := 4097/250000000) (ψ := -176407/500000) 326 183
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t34 : ((340352836127/2000000000000 : ℚ) : ℝ) ≤ stT326 34 := by
  have hc : ((992291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((340352836127/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((992291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c35 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-988981/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7482509/10000000) (δ := 16373/1000000000) (ψ := -176407/500000) 326 185
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t35 : ((-1671852516029/10000000000000 : ℚ) : ℝ) ≤ stT326 35 := by
  have hc : ((-989081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1671852516029/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-989081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c36 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((995727/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -231189/10000000) (δ := 8233/500000000) (ψ := -176407/500000) 326 186
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t36 : ((829688834791/5000000000000 : ℚ) : ℝ) ≤ stT326 36 := by
  have hc : ((995627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((829688834791/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((995627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c37 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-833613/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6391033/10000000) (δ := 16359/1000000000) (ψ := -176407/500000) 326 187
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t37 : ((-137061583487/1000000000000 : ℚ) : ℝ) ≤ stT326 37 := by
  have hc : ((-833713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137061583487/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-833713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c38 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((31491/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -329031/1000000) (δ := 8229/500000000) (ψ := -176407/500000) 326 189
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t38 : ((51064863399/1250000000000 : ℚ) : ℝ) ≤ stT326 38 := by
  have hc : ((62957/250000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51064863399/1250000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((62957/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c39 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((645817/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2171759/10000000) (δ := 8183/500000000) (ψ := -176407/500000) 326 190
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t39 : ((1033974363477/10000000000000 : ℚ) : ℝ) ≤ stT326 39 := by
  have hc : ((645717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1033974363477/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((645717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c40 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-954603/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7097803/10000000) (δ := 16473/1000000000) (ψ := -176407/500000) 326 191
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t40 : ((-1509518146717/10000000000000 : ℚ) : ℝ) ≤ stT326 40 := by
  have hc : ((-954703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1509518146717/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-954703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c41 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-3327/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -838731/2000000) (δ := 4079/250000000) (ψ := -176407/500000) 326 193
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t41 : ((-20803131029/1250000000000 : ℚ) : ℝ) ≤ stT326 41 := by
  have hc : ((-26641/250000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20803131029/1250000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-26641/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c42 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((99451/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -131037/5000000) (δ := 8197/500000000) (ψ := -176407/500000) 326 194
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t42 : ((153440744553/1000000000000 : ℚ) : ℝ) ≤ stT326 42 := by
  have hc : ((99441/100000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153440744553/1000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((99441/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c43 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((283909/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80183/250000) (δ := 8151/500000000) (ψ := -176407/500000) 326 195
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t43 : ((86560893573/2000000000000 : ℚ) : ℝ) ≤ stT326 43 := by
  have hc : ((283809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86560893573/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((283809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c44 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-797731/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6235799/10000000) (δ := 8197/500000000) (ψ := -176407/500000) 326 196
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t44 : ((-1202775708867/10000000000000 : ℚ) : ℝ) ≤ stT326 44 := by
  have hc : ((-797831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1202775708867/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-797831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c45 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-922737/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1372959/2000000) (δ := 16423/1000000000) (ψ := -176407/500000) 326 198
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t45 : ((-171960523743/1250000000000 : ℚ) : ℝ) ≤ stT326 45 := by
  have hc : ((-922837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171960523743/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-922837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c46 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-289003/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -931991/2000000) (δ := 1633/100000000) (ψ := -176407/500000) 326 199
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t46 : ((-21312962263/500000000000 : ℚ) : ℝ) ≤ stT326 46 := by
  have hc : ((-289103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21312962263/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-289103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c47 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((421123/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -710071/2500000) (δ := 8183/500000000) (ψ := -176407/500000) 326 200
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t47 : ((614124777927/10000000000000 : ℚ) : ℝ) ≤ stT326 47 := by
  have hc : ((421023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((614124777927/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((421023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c48 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((849431/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -694863/5000000) (δ := 3269/200000000) (ψ := -176407/500000) 326 201
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t48 : ((9807225057/80000000000 : ℚ) : ℝ) ≤ stT326 48 := by
  have hc : ((849331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9807225057/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((849331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c49 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((496569/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -293041/10000000) (δ := 4113/250000000) (ψ := -176407/500000) 326 202
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t49 : ((709312644349/5000000000000 : ℚ) : ℝ) ≤ stT326 49 := by
  have hc : ((496519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((709312644349/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((496519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c50 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((196561/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 464277/10000000) (δ := 4111/250000000) (ψ := -176407/500000) 326 203
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t50 : ((277950837233/2000000000000 : ℚ) : ℝ) ≤ stT326 50 := by
  have hc : ((196541/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((277950837233/2000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((196541/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c51 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((936539/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 895433/10000000) (δ := 16337/1000000000) (ψ := -176407/500000) 326 204
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t51 : ((32781920073/250000000000 : ℚ) : ℝ) ≤ stT326 51 := by
  have hc : ((936439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32781920073/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((936439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c52 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((918989/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1013221/10000000) (δ := 1643/100000000) (ψ := -176407/500000) 326 205
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t52 : ((5097077283/40000000000 : ℚ) : ℝ) ≤ stT326 52 := by
  have hc : ((918889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5097077283/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((918889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c53 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((236363/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 829541/10000000) (δ := 16323/1000000000) (ψ := -176407/500000) 326 206
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t53 : ((32463505849/250000000000 : ℚ) : ℝ) ≤ stT326 53 := by
  have hc : ((118169/125000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32463505849/250000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((118169/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c54 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((989899/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 355639/10000000) (δ := 3283/200000000) (ψ := -176407/500000) 326 207
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t54 : ((1346945203773/10000000000000 : ℚ) : ℝ) ≤ stT326 54 := by
  have hc : ((989799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1346945203773/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((989799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c55 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((987367/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -397807/10000000) (δ := 3299/200000000) (ψ := -176407/500000) 326 208
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t55 : ((1331229835533/10000000000000 : ℚ) : ℝ) ≤ stT326 55 := by
  have hc : ((987267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1331229835533/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((987267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c56 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((842829/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1420693/10000000) (δ := 8201/500000000) (ψ := -176407/500000) 326 209
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t56 : ((563071909537/5000000000000 : ℚ) : ℝ) ≤ stT326 56 := by
  have hc : ((842729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((563071909537/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((842729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c57 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((470099/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2703483/10000000) (δ := 8247/500000000) (ψ := -176407/500000) 326 210
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t57 : ((155632178867/2500000000000 : ℚ) : ℝ) ≤ stT326 57 := by
  have hc : ((469999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155632178867/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((469999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c58 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-123737/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4237129/10000000) (δ := 16387/1000000000) (ψ := -176407/500000) 326 211
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t58 : ((-32521206081/2000000000000 : ℚ) : ℝ) ≤ stT326 58 := by
  have hc : ((-123837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32521206081/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-123837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c59 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-370469/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1503289/2500000) (δ := 4081/250000000) (ψ := -176407/500000) 326 212
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t59 : ((-48237498091/500000000000 : ℚ) : ℝ) ≤ stT326 59 := by
  have hc : ((-370519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48237498091/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-370519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c60 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-498853/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 768463/1000000) (δ := 16479/1000000000) (ψ := -176407/500000) 326 212
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t60 : ((-128816255697/1000000000000 : ℚ) : ℝ) ≤ stT326 60 := by
  have hc : ((-498903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128816255697/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-498903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c61 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-285787/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5448047/10000000) (δ := 16431/1000000000) (ψ := -176407/500000) 326 213
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t61 : ((-365976833853/5000000000000 : ℚ) : ℝ) ≤ stT326 61 := by
  have hc : ((-285837/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-365976833853/5000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-285837/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c62 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((365193/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2992391/10000000) (δ := 8169/500000000) (ψ := -176407/500000) 326 214
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t62 : ((463668475093/10000000000000 : ℚ) : ℝ) ≤ stT326 62 := by
  have hc : ((365093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((463668475093/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((365093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c63 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((39663/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 162377/5000000) (δ := 3289/200000000) (ψ := -176407/500000) 326 215
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t63 : ((49965620579/400000000000 : ℚ) : ℝ) ≤ stT326 63 := by
  have hc : ((39659/40000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49965620579/400000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((39659/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c64 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((52393/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -509669/2000000) (δ := 511/31250000) (ψ := -176407/500000) 326 216
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t64 : ((52383/800000 : ℚ) : ℝ) ≤ stT326 64 := by
  have hc : ((52383/100000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52383/800000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((52383/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c65 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-39171/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1124077/2000000) (δ := 16459/1000000000) (ψ := -176407/500000) 326 217
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t65 : ((-48593423683/625000000000 : ℚ) : ℝ) ≤ stT326 65 := by
  have hc : ((-156709/250000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48593423683/625000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-156709/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c66 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-183221/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6822627/10000000) (δ := 2043/125000000) (ψ := -176407/500000) 326 217
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t66 : ((-45110819103/400000000000 : ℚ) : ℝ) ≤ stT326 66 := by
  have hc : ((-183241/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45110819103/400000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-183241/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c67 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((110371/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 421319/1250000) (δ := 4109/250000000) (ψ := -176407/500000) 326 218
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t67 : ((67389251887/2500000000000 : ℚ) : ℝ) ≤ stT326 67 := by
  have hc : ((110321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67389251887/2500000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((110321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c68 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((994467/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4111/156250) (δ := 8237/500000000) (ψ := -176407/500000) 326 219
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t68 : ((602923492413/5000000000000 : ℚ) : ℝ) ≤ stT326 68 := by
  have hc : ((994367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((602923492413/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((994367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c69 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-58389/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2036523/5000000) (δ := 8211/500000000) (ψ := -176407/500000) 326 220
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t69 : ((-70412509051/10000000000000 : ℚ) : ℝ) ≤ stT326 69 := by
  have hc : ((-58489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70412509051/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-58489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c70 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-498397/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1530749/2000000) (δ := 16381/1000000000) (ψ := -176407/500000) 326 220
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t70 : ((-595758309363/5000000000000 : ℚ) : ℝ) ≤ stT326 70 := by
  have hc : ((-498447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-595758309363/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-498447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c71 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((16751/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3506231/10000000) (δ := 2061/125000000) (ψ := -176407/500000) 326 221
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t71 : ((19867900721/1000000000000 : ℚ) : ℝ) ≤ stT326 71 := by
  have hc : ((16741/100000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19867900721/1000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((16741/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c72 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((94887/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -401449/5000000) (δ := 3279/200000000) (ψ := -176407/500000) 326 222
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t72 : ((111813588147/1000000000000 : ℚ) : ℝ) ≤ stT326 72 := by
  have hc : ((94877/100000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111813588147/1000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((94877/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c73 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-511503/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2634661/5000000) (δ := 16303/1000000000) (ψ := -176407/500000) 326 223
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t73 : ((-149696572609/2500000000000 : ℚ) : ℝ) ≤ stT326 73 := by
  have hc : ((-511603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149696572609/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-511603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c74 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-686671/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2909621/5000000) (δ := 16303/1000000000) (ψ := -176407/500000) 326 223
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t74 : ((-798355491767/10000000000000 : ℚ) : ℝ) ≤ stT326 74 := by
  have hc : ((-686771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-798355491767/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-686771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c75 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((912909/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 210221/2000000) (δ := 16393/1000000000) (ψ := -176407/500000) 326 224
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t75 : ((10540205523/100000000000 : ℚ) : ℝ) ≤ stT326 75 := by
  have hc : ((912809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10540205523/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((912809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c76 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((5197/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -193101/500000) (δ := 16317/1000000000) (ψ := -176407/500000) 326 225
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t76 : ((2969211403/1000000000000 : ℚ) : ℝ) ≤ stT326 76 := by
  have hc : ((5177/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2969211403/1000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((5177/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c77 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-455541/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6791741/10000000) (δ := 8243/500000000) (ψ := -176407/500000) 326 225
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t77 : ((-259597118573/2500000000000 : ℚ) : ℝ) ≤ stT326 77 := by
  have hc : ((-455591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-259597118573/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-455591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c78 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((200521/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1600049/10000000) (δ := 16379/1000000000) (ψ := -176407/500000) 326 226
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t78 : ((14188563087/156250000000 : ℚ) : ℝ) ≤ stT326 78 := by
  have hc : ((12531/15625 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14188563087/156250000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((12531/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c79 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((40229/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3725629/10000000) (δ := 16331/1000000000) (ψ := -176407/500000) 326 227
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t79 : ((45204870573/5000000000000 : ℚ) : ℝ) ≤ stT326 79 := by
  have hc : ((40179/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45204870573/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((40179/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c80 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-431111/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6526093/10000000) (δ := 16331/1000000000) (ψ := -176407/500000) 326 227
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t80 : ((-241026328737/2500000000000 : ℚ) : ℝ) ≤ stT326 80 := by
  have hc : ((-431161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-241026328737/2500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-431161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c81 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((464889/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 942467/10000000) (δ := 3273/200000000) (ψ := -176407/500000) 326 228
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t81 : ((516487726129/5000000000000 : ℚ) : ℝ) ≤ stT326 81 := by
  have hc : ((464839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((516487726129/5000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((464839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c82 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-329099/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -953073/2000000) (δ := 16457/1000000000) (ψ := -176407/500000) 326 229
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t82 : ((-90884930721/2500000000000 : ℚ) : ℝ) ≤ stT326 82 := by
  have hc : ((-329199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90884930721/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-329199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c83 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-457013/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 639197/1250000) (δ := 16457/1000000000) (ψ := -176407/500000) 326 229
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t83 : ((-501746884659/10000000000000 : ℚ) : ℝ) ≤ stT326 83 := by
  have hc : ((-457113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-501746884659/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-457113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c84 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((944893/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33353/400000) (δ := 131/4000000) (ψ := -176407/500000) 326 230
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t84 : ((1030853249577/10000000000000 : ℚ) : ℝ) ≤ stT326 84 := by
  have hc : ((944793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1030853249577/10000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((944793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c85 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-463791/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6896711/10000000) (δ := 409/25000000) (ψ := -176407/500000) 326 231
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t85 : ((-503106532173/5000000000000 : ℚ) : ℝ) ≤ stT326 85 := by
  have hc : ((-463841/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-503106532173/5000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-463841/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c86 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((493913/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2635529/10000000) (δ := 409/25000000) (ψ := -176407/500000) 326 231
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t86 : ((532491890851/10000000000000 : ℚ) : ℝ) ≤ stT326 86 := by
  have hc : ((493813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((532491890851/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((493813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c87 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((2209/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3650301/10000000) (δ := 1021/62500000) (ψ := -176407/500000) 326 232
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t87 : ((147884449/12500000000 : ℚ) : ℝ) ≤ stT326 87 := by
  have hc : ((2207/20000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147884449/12500000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((2207/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c88 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-320131/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 566409/1000000) (δ := 16467/1000000000) (ψ := -176407/500000) 326 232
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t88 : ((-85328556681/1250000000000 : ℚ) : ℝ) ≤ stT326 88 := by
  have hc : ((-320181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85328556681/1250000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-320181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c89 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((944767/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -834781/10000000) (δ := 8187/500000000) (ψ := -176407/500000) 326 233
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t89 : ((1001344185999/10000000000000 : ℚ) : ℝ) ≤ stT326 89 := by
  have hc : ((944667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1001344185999/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((944667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c90 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-986089/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1487301/2000000) (δ := 16321/1000000000) (ψ := -176407/500000) 326 234
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t90 : ((-1039534921577/10000000000000 : ℚ) : ℝ) ≤ stT326 90 := by
  have hc : ((-986189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1039534921577/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-986189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c91 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((80941/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1569123/10000000) (δ := 16341/500000000) (ψ := -176407/500000) 326 234
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t91 : ((21209668101/250000000000 : ℚ) : ℝ) ≤ stT326 91 := by
  have hc : ((80931/100000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21209668101/250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((80931/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c92 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-249251/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1046333/2000000) (δ := 8207/500000000) (ψ := -176407/500000) 326 235
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t92 : ((-259914491473/5000000000000 : ℚ) : ℝ) ≤ stT326 92 := by
  have hc : ((-249301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-259914491473/5000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-249301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c93 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((138661/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3579219/10000000) (δ := 16389/1000000000) (ψ := -176407/500000) 326 235
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t93 : ((143680967511/10000000000000 : ℚ) : ℝ) ≤ stT326 93 := by
  have hc : ((138561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143680967511/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((138561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c94 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((204513/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -136483/400000) (δ := 16307/1000000000) (ψ := -176407/500000) 326 236
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t94 : ((210835860873/10000000000000 : ℚ) : ℝ) ≤ stT326 94 := by
  have hc : ((204413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210835860873/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((204413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c95 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-98357/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5212337/10000000) (δ := 1031/62500000) (ψ := -176407/500000) 326 236
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t95 : ((-100932736083/2000000000000 : ℚ) : ℝ) ≤ stT326 95 := by
  have hc : ((-98377/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100932736083/2000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-98377/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c96 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((353833/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1961517/10000000) (δ := 16403/1000000000) (ψ := -176407/500000) 326 237
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t96 : ((18053900273/250000000000 : ℚ) : ℝ) ≤ stT326 96 := by
  have hc : ((353783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18053900273/250000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((353783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c97 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-426803/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1296833/2000000) (δ := 16403/1000000000) (ψ := -176407/500000) 326 237
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t97 : ((-433403912991/5000000000000 : ℚ) : ℝ) ≤ stT326 97 := by
  have hc : ((-426853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-433403912991/5000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-426853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c98 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((940771/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -864751/10000000) (δ := 1631/100000000) (ψ := -176407/500000) 326 238
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t98 : ((118777586499/1250000000000 : ℚ) : ℝ) ≤ stT326 98 := by
  have hc : ((940671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118777586499/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((940671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c99 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-984233/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1481891/2000000) (δ := 1631/100000000) (ψ := -176407/500000) 326 238
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t99 : ((-494646034827/5000000000000 : ℚ) : ℝ) ≤ stT326 99 := by
  have hc : ((-984333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-494646034827/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-984333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c100 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((39963/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53757/5000000) (δ := 8193/500000000) (ψ := -176407/500000) 326 239
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t100 : ((39958960041/400000000000 : ℚ) : ℝ) ≤ stT326 100 := by
  have hc : ((39959/40000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39958960041/400000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((39959/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c101 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-499123/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7705901/10000000) (δ := 653/40000000) (ψ := -176407/500000) 326 240
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t101 : ((-248348051787/2500000000000 : ℚ) : ℝ) ≤ stT326 101 := by
  have hc : ((-499173/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-248348051787/2500000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-499173/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c102 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((247907/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 323723/10000000) (δ := 8239/500000000) (ψ := -176407/500000) 326 240
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t102 : ((122719809327/1250000000000 : ℚ) : ℝ) ≤ stT326 102 := by
  have hc : ((123941/125000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122719809327/1250000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((123941/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c103 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-985857/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3716509/5000000) (δ := 1027/62500000) (ψ := -176407/500000) 326 241
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t103 : ((-97149301081/1000000000000 : ℚ) : ℝ) ≤ stT326 103 := by
  have hc : ((-985957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97149301081/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-985957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c104 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((246113/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44143/1000000) (δ := 16371/1000000000) (ψ := -176407/500000) 326 241
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t104 : ((1508181069/15625000000 : ℚ) : ℝ) ≤ stT326 104 := by
  have hc : ((30761/31250 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1508181069/15625000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((30761/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c105 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-247017/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7467391/10000000) (δ := 1029/62500000) (ψ := -176407/500000) 326 242
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t105 : ((-120544267421/1250000000000 : ℚ) : ℝ) ≤ stT326 105 := by
  have hc : ((-123521/125000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120544267421/1250000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-123521/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c106 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((99469/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1031/40000) (δ := 16339/1000000000) (ψ := -176407/500000) 326 242
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t106 : ((19320606963/200000000000 : ℚ) : ℝ) ≤ stT326 106 := by
  have hc : ((99459/100000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19320606963/200000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((99459/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c107 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-199949/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3898763/5000000) (δ := 8223/500000000) (ψ := -176407/500000) 326 243
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t107 : ((-193317431153/2000000000000 : ℚ) : ℝ) ≤ stT326 107 := by
  have hc : ((-199969/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193317431153/2000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-199969/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c108 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((996267/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21607/1000000) (δ := 8223/500000000) (ψ := -176407/500000) 326 243
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t108 : ((3834246783/40000000000 : ℚ) : ℝ) ≤ stT326 108 := by
  have hc : ((996167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3834246783/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((996167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c109 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-243787/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7295459/10000000) (δ := 8223/500000000) (ψ := -176407/500000) 326 243
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t109 : ((-58382429131/625000000000 : ℚ) : ℝ) ≤ stT326 109 := by
  have hc : ((-60953/62500 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58382429131/625000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-60953/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c110 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((925741/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -969517/10000000) (δ := 16353/1000000000) (ψ := -176407/500000) 326 244
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t110 : ((441281759571/5000000000000 : ℚ) : ℝ) ≤ stT326 110 := by
  have hc : ((925641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((441281759571/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((925641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c111 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-418469/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6406151/10000000) (δ := 329/20000000) (ψ := -176407/500000) 326 244
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t111 : ((-198620328501/2500000000000 : ℚ) : ℝ) ≤ stT326 111 := by
  have hc : ((-418519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198620328501/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-418519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c112 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((698883/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1992403/10000000) (δ := 16343/1000000000) (ψ := -176407/500000) 326 245
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t112 : ((660287743313/10000000000000 : ℚ) : ℝ) ≤ stT326 112 := by
  have hc : ((698783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((660287743313/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((698783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c113 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-252791/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1313033/2500000) (δ := 16343/1000000000) (ψ := -176407/500000) 326 245
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t113 : ((-237852838361/5000000000000 : ℚ) : ℝ) ≤ stT326 113 := by
  have hc : ((-252841/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237852838361/5000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-252841/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c114 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((16111/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -409399/1250000) (δ := 1023/62500000) (ψ := -176407/500000) 326 246
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t114 : ((12066773823/500000000000 : ℚ) : ℝ) ≤ stT326 114 := by
  have hc : ((64419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12066773823/500000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((64419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c115 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((33681/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3842773/10000000) (δ := 3287/200000000) (ψ := -176407/500000) 326 246
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t115 : ((3914302103/1250000000000 : ℚ) : ℝ) ≤ stT326 115 := by
  have hc : ((33581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3914302103/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((33581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c116 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-691/2000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -120223/250000) (δ := 2041/125000000) (ψ := -176407/500000) 326 247
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t116 : ((-25068879/781250000 : ℚ) : ℝ) ≤ stT326 116 := by
  have hc : ((-216/625 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25068879/781250000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-216/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c117 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((160297/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2186877/10000000) (δ := 2041/125000000) (ψ := -176407/500000) 326 247
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t117 : ((18521433/312500000 : ℚ) : ℝ) ≤ stT326 117 := by
  have hc : ((10017/15625 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18521433/312500000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((10017/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c118 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-873891/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3292433/5000000) (δ := 16421/1000000000) (ψ := -176407/500000) 326 248
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t118 : ((-32182970593/400000000000 : ℚ) : ℝ) ≤ stT326 118 := by
  have hc : ((-873991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32182970593/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-873991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c119 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((993151/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73189/2500000) (δ := 16421/1000000000) (ψ := -176407/500000) 326 248
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t119 : ((455163932799/5000000000000 : ℚ) : ℝ) ≤ stT326 119 := by
  have hc : ((993051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((455163932799/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((993051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c120 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-956387/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7112921/10000000) (δ := 8191/500000000) (ψ := -176407/500000) 326 248
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t120 : ((-873149244177/10000000000000 : ℚ) : ℝ) ≤ stT326 120 := by
  have hc : ((-956487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-873149244177/10000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-956487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c121 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((743433/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11447/62500) (δ := 16489/1000000000) (ψ := -176407/500000) 326 249
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t121 : ((67575659697/1000000000000 : ℚ) : ℝ) ≤ stT326 121 := by
  have hc : ((743333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67575659697/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((743333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c122 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-185339/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4876337/10000000) (δ := 8157/500000000) (ψ := -176407/500000) 326 249
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t122 : ((-83921707131/2500000000000 : ℚ) : ℝ) ≤ stT326 122 := by
  have hc : ((-185389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83921707131/2500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-185389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c123 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-100449/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4178537/10000000) (δ := 16407/1000000000) (ψ := -176407/500000) 326 250
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t123 : ((-9066201683/1000000000000 : ℚ) : ℝ) ≤ stT326 123 := by
  have hc : ((-100549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9066201683/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-100549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c124 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((141681/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2420681/10000000) (δ := 16407/1000000000) (ψ := -176407/500000) 326 250
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t124 : ((7950673191/156250000000 : ℚ) : ℝ) ≤ stT326 124 := by
  have hc : ((17707/31250 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7950673191/156250000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((17707/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c125 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-451267/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6741039/10000000) (δ := 1019/62500000) (ψ := -176407/500000) 326 251
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t125 : ((-100917640419/1250000000000 : ℚ) : ℝ) ≤ stT326 125 := by
  have hc : ((-451317/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100917640419/1250000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-451317/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c126 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((7961/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -61739/2500000) (δ := 1019/62500000) (ψ := -176407/500000) 326 251
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t126 : ((3545751687/40000000000 : ℚ) : ℝ) ≤ stT326 126 := by
  have hc : ((39801/40000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3545751687/40000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((39801/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c127 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-787957/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61957/100000) (δ := 16499/1000000000) (ψ := -176407/500000) 326 251
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t127 : ((-699287895349/10000000000000 : ℚ) : ℝ) ≤ stT326 127 := by
  have hc : ((-788057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-699287895349/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-788057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c128 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((317199/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -624011/2000000) (δ := 2049/125000000) (ψ := -176407/500000) 326 252
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t128 : ((280278415417/10000000000000 : ℚ) : ℝ) ≤ stT326 128 := by
  have hc : ((317099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((280278415417/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((317099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c129 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((55621/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1611219/5000000) (δ := 2049/125000000) (ψ := -176407/500000) 326 252
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t129 : ((979078009/40000000000 : ℚ) : ℝ) ≤ stT326 129 := by
  have hc : ((55601/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((979078009/40000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((55601/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c130 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-196767/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1238419/2000000) (δ := 8159/500000000) (ψ := -176407/500000) 326 253
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t130 : ((-21574774341/312500000000 : ℚ) : ℝ) ≤ stT326 130 := by
  have hc : ((-24599/31250 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21574774341/312500000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-24599/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c131 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((499887/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3323/625000) (δ := 3297/200000000) (ψ := -176407/500000) 326 253
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t131 : ((54588698281/625000000000 : ℚ) : ℝ) ≤ stT326 131 := by
  have hc : ((499837/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54588698281/625000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((499837/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c132 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-801363/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6250917/10000000) (δ := 3297/200000000) (ψ := -176407/500000) 326 253
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t132 : ((-697584579107/10000000000000 : ℚ) : ℝ) ≤ stT326 132 := by
  have hc : ((-801463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-697584579107/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-801463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c133 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((12291/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1653039/5000000) (δ := 8189/500000000) (ψ := -176407/500000) 326 254
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t133 : ((5326650587/250000000000 : ℚ) : ℝ) ≤ stT326 133 := by
  have hc : ((6143/25000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5326650587/250000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((6143/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c134 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((218057/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1399401/5000000) (δ := 261/8000000) (ψ := -176407/500000) 326 254
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t134 : ((47082317769/1250000000000 : ℚ) : ℝ) ≤ stT326 134 := by
  have hc : ((218007/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47082317769/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((218007/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c135 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-920389/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6849677/10000000) (δ := 4083/250000000) (ψ := -176407/500000) 326 255
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t135 : ((-792230824207/10000000000000 : ℚ) : ℝ) ≤ stT326 135 := by
  have hc : ((-920489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-792230824207/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-920489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c136 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((59047/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -52181/625000) (δ := 16471/1000000000) (ψ := -176407/500000) 326 255
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t136 : ((50626970799/625000000000 : ℚ) : ℝ) ≤ stT326 136 := by
  have hc : ((236163/250000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50626970799/625000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((236163/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c137 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-464929/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1283969/2500000) (δ := 4083/250000000) (ψ := -176407/500000) 326 255
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t137 : ((-198650623191/5000000000000 : ℚ) : ℝ) ≤ stT326 137 := by
  have hc : ((-465029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198650623191/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-465029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c138 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-283209/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4644837/10000000) (δ := 4091/250000000) (ψ := -176407/500000) 326 256
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t138 : ((-241168769413/10000000000000 : ℚ) : ℝ) ≤ stT326 138 := by
  have hc : ((-283309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-241168769413/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-283309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c139 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((879549/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 309927/2500000) (δ := 16439/1000000000) (ψ := -176407/500000) 326 256
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t139 : ((186484522103/2500000000000 : ℚ) : ℝ) ≤ stT326 139 := by
  have hc : ((879449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((186484522103/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((879449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c140 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-190541/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1416407/2000000) (δ := 4091/250000000) (ψ := -176407/500000) 326 256
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t140 : ((-32210716391/400000000000 : ℚ) : ℝ) ≤ stT326 140 := by
  have hc : ((-190561/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32210716391/400000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-190561/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c141 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((42657/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2825247/10000000) (δ := 16347/1000000000) (ψ := -176407/500000) 326 257
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t141 : ((35915213697/1000000000000 : ℚ) : ℝ) ≤ stT326 141 := by
  have hc : ((42647/100000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35915213697/1000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((42647/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c142 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((193321/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2934521/10000000) (δ := 16347/1000000000) (ψ := -176407/500000) 326 257
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t142 : ((162189351051/5000000000000 : ℚ) : ℝ) ≤ stT326 142 := by
  have hc : ((193271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162189351051/5000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((193271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c143 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-3797/4000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3527049/5000000) (δ := 8227/500000000) (ψ := -176407/500000) 326 258
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t143 : ((-15877745841/200000000000 : ℚ) : ℝ) ≤ stT326 143 := by
  have hc : ((-18987/20000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15877745841/200000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-18987/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c144 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((85259/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1374689/10000000) (δ := 8227/500000000) (ψ := -176407/500000) 326 258
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t144 : ((71040804917/1000000000000 : ℚ) : ℝ) ≤ stT326 144 := by
  have hc : ((85249/100000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71040804917/1000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((85249/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c145 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-134997/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2132759/5000000) (δ := 16349/1000000000) (ψ := -176407/500000) 326 258
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t145 : ((-22438395827/2000000000000 : ℚ) : ℝ) ≤ stT326 145 := by
  have hc : ((-135097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22438395827/2000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-135097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c146 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-346491/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -730129/1250000) (δ := 8221/500000000) (ψ := -176407/500000) 326 259
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t146 : ((-143399705423/2500000000000 : ℚ) : ℝ) ≤ stT326 146 := by
  have hc : ((-346541/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143399705423/2500000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-346541/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c147 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((993827/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -277923/10000000) (δ := 16361/1000000000) (ψ := -176407/500000) 326 259
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t147 : ((409806058711/5000000000000 : ℚ) : ℝ) ≤ stT326 147 := by
  have hc : ((993727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((409806058711/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((993727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c148 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-251997/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1311883/2500000) (δ := 8221/500000000) (ψ := -176407/500000) 326 259
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t148 : ((-41436274753/1000000000000 : ℚ) : ℝ) ≤ stT326 148 := by
  have hc : ((-252047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41436274753/1000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-252047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c149 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-101497/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4972139/10000000) (δ := 4117/250000000) (ψ := -176407/500000) 326 260
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t149 : ((-1299532361/39062500000 : ℚ) : ℝ) ≤ stT326 149 := by
  have hc : ((-50761/125000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1299532361/39062500000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-50761/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c150 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((981677/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 239657/5000000) (δ := 3267/200000000) (ψ := -176407/500000) 326 260
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t150 : ((50090855887/625000000000 : ℚ) : ℝ) ≤ stT326 150 := by
  have hc : ((981577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50090855887/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((981577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c151 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-708287/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5894663/10000000) (δ := 3267/200000000) (ψ := -176407/500000) 326 260
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t151 : ((-576477548343/10000000000000 : ℚ) : ℝ) ≤ stT326 151 := by
  have hc : ((-708387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-576477548343/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-708387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c152 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-201311/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -443373/1000000) (δ := 4107/250000000) (ψ := -176407/500000) 326 261
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t152 : ((-40841518347/2500000000000 : ℚ) : ℝ) ≤ stT326 152 := by
  have hc : ((-201411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40841518347/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-201411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c153 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((467201/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 910551/10000000) (δ := 4107/250000000) (ψ := -176407/500000) 326 261
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t153 : ((94417290063/1250000000000 : ℚ) : ℝ) ≤ stT326 153 := by
  have hc : ((467151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94417290063/1250000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((467151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c154 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-99239/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 48594/78125) (δ := 131/8000000) (ψ := -176407/500000) 326 261
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t154 : ((-159958282969/2500000000000 : ℚ) : ℝ) ≤ stT326 154 := by
  have hc : ((-198503/250000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159958282969/2500000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-198503/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c155 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-28523/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1053211/2500000) (δ := 51/3125000) (ψ := -176407/500000) 326 262
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t155 : ((-286629057/31250000000 : ℚ) : ℝ) ≤ stT326 155 := by
  have hc : ((-7137/62500 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286629057/31250000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-7137/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c156 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((916587/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51417/500000) (δ := 16483/1000000000) (ψ := -176407/500000) 326 262
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t156 : ((1146525237/15625000000 : ℚ) : ℝ) ≤ stT326 156 := by
  have hc : ((916487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1146525237/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((916487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c157 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-398893/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6236027/10000000) (δ := 16483/1000000000) (ψ := -176407/500000) 326 262
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t157 : ((-318391222041/5000000000000 : ℚ) : ℝ) ≤ stT326 157 := by
  have hc : ((-398943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-318391222041/5000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-398943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c158 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-73799/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4297339/10000000) (δ := 16413/1000000000) (ψ := -176407/500000) 326 263
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t158 : ((-29375581371/2500000000000 : ℚ) : ℝ) ≤ stT326 158 := by
  have hc : ((-73849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29375581371/2500000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-73849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c159 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((188693/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 844659/10000000) (δ := 16413/1000000000) (ψ := -176407/500000) 326 263
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t159 : ((149627311323/2000000000000 : ℚ) : ℝ) ≤ stT326 159 := by
  have hc : ((188673/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149627311323/2000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((188673/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c160 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-724947/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5954383/10000000) (δ := 16413/1000000000) (ψ := -176407/500000) 326 263
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t160 : ((-57320040679/1000000000000 : ℚ) : ℝ) ≤ stT326 160 := by
  have hc : ((-725047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57320040679/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-725047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c161 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-59007/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2337861/5000000) (δ := 16497/1000000000) (ψ := -176407/500000) 326 264
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t161 : ((-46519827997/2000000000000 : ℚ) : ℝ) ≤ stT326 161 := by
  have hc : ((-59027/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46519827997/2000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-59027/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c162 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((989023/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 185379/5000000) (δ := 16497/1000000000) (ψ := -176407/500000) 326 264
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t162 : ((388485544551/5000000000000 : ℚ) : ℝ) ≤ stT326 162 := by
  have hc : ((988923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((388485544551/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((988923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c163 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-551097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2693093/5000000) (δ := 8153/500000000) (ψ := -176407/500000) 326 264
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t163 : ((-431731113417/10000000000000 : ℚ) : ℝ) ≤ stT326 163 := by
  have hc : ((-551197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-431731113417/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-551197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c164 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-534599/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2668537/5000000) (δ := 4101/250000000) (ψ := -176407/500000) 326 265
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t164 : ((-417529873431/10000000000000 : ℚ) : ℝ) ≤ stT326 164 := by
  have hc : ((-534699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-417529873431/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-534699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c165 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((988307/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -382689/10000000) (δ := 4101/250000000) (ψ := -176407/500000) 326 265
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t165 : ((384658586543/5000000000000 : ℚ) : ℝ) ≤ stT326 165 := by
  have hc : ((988207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((384658586543/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((988207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c166 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-121723/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 908357/2000000) (δ := 16399/1000000000) (ψ := -176407/500000) 326 265
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t166 : ((-94514235723/5000000000000 : ℚ) : ℝ) ≤ stT326 166 := by
  have hc : ((-121773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94514235723/5000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-121773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c167 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-806191/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6271207/10000000) (δ := 4123/250000000) (ψ := -176407/500000) 326 266
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t167 : ((-9748864481/156250000000 : ℚ) : ℝ) ≤ stT326 167 := by
  have hc : ((-806291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9748864481/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-806291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c168 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((211517/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56223/400000) (δ := 16311/1000000000) (ψ := -176407/500000) 326 266
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t168 : ((10198091367/156250000000 : ℚ) : ℝ) ≤ stT326 168 := by
  have hc : ((52873/62500 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10198091367/156250000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((52873/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c169 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((39397/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3431287/10000000) (δ := 16311/1000000000) (ψ := -176407/500000) 326 266
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t169 : ((3028996971/200000000000 : ℚ) : ℝ) ≤ stT326 169 := by
  have hc : ((39377/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3028996971/200000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((39377/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c170 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-988131/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7468421/10000000) (δ := 3277/200000000) (ψ := -176407/500000) 326 267
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t170 : ((-151587717783/2000000000000 : ℚ) : ℝ) ≤ stT326 170 := by
  have hc : ((-988231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151587717783/2000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-988231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c171 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((118857/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -672091/2500000) (δ := 8209/500000000) (ψ := -176407/500000) 326 267
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t171 : ((5679568013/156250000000 : ℚ) : ℝ) ≤ stT326 171 := by
  have hc : ((7427/15625 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5679568013/156250000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((7427/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c172 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((678169/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2063819/10000000) (δ := 3277/200000000) (ψ := -176407/500000) 326 267
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t172 : ((129255546987/2500000000000 : ℚ) : ℝ) ≤ stT326 172 := by
  have hc : ((678069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129255546987/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((678069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c173 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-910539/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 848557/1250000) (δ := 8209/500000000) (ψ := -176407/500000) 326 267
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t173 : ((-346173041377/5000000000000 : ℚ) : ℝ) ≤ stT326 173 := by
  have hc : ((-910639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-346173041377/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-910639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c174 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-117767/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1055523/2500000) (δ := 8163/500000000) (ψ := -176407/500000) 326 268
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t174 : ((-89354854833/10000000000000 : ℚ) : ℝ) ≤ stT326 174 := by
  have hc : ((-117867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89354854833/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-117867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c175 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((245989/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 112107/2500000) (δ := 16477/1000000000) (ψ := -176407/500000) 326 268
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t175 : ((5810346081/78125000000 : ℚ) : ℝ) ≤ stT326 175 := by
  have hc : ((61491/62500 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5810346081/78125000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((61491/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c176 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-224713/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2546149/5000000) (δ := 16477/1000000000) (ψ := -176407/500000) 326 268
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t176 : ((-169421629377/5000000000000 : ℚ) : ℝ) ≤ stT326 176 := by
  have hc : ((-224763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169421629377/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-224763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c177 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-736863/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2999019/5000000) (δ := 1637/100000000) (ψ := -176407/500000) 326 269
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t177 : ((-553936028061/10000000000000 : ℚ) : ℝ) ≤ stT326 177 := by
  have hc : ((-736963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-553936028061/10000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-736963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c178 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((845873/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1406491/10000000) (δ := 1637/100000000) (ψ := -176407/500000) 326 269
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t178 : ((633933082463/10000000000000 : ℚ) : ℝ) ≤ stT326 178 := by
  have hc : ((845773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((633933082463/10000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((845773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c179 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((302241/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 394923/1250000) (δ := 16433/1000000000) (ψ := -176407/500000) 326 269
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t179 : ((45166151667/2000000000000 : ℚ) : ℝ) ≤ stT326 179 := by
  have hc : ((302141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45166151667/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((302141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c180 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-499049/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7699749/10000000) (δ := 16433/1000000000) (ψ := -176407/500000) 326 269
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t180 : ((-93001608561/1250000000000 : ℚ) : ℝ) ≤ stT326 180 := by
  have hc : ((-499099/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93001608561/1250000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-499099/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c181 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((34549/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -436619/1250000) (δ := 16463/1000000000) (ψ := -176407/500000) 326 270
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t181 : ((12832599263/1000000000000 : ℚ) : ℝ) ≤ stT326 181 := by
  have hc : ((34529/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12832599263/1000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((34529/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c182 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((92147/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 249343/2500000) (δ := 16463/1000000000) (ψ := -176407/500000) 326 270
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t182 : ((68296459113/1000000000000 : ℚ) : ℝ) ≤ stT326 182 := by
  have hc : ((92137/100000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68296459113/1000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((92137/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c183 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-23061/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1092633/2000000) (δ := 817/50000000) (ψ := -176407/500000) 326 270
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t183 : ((-1705015543/40000000000 : ℚ) : ℝ) ≤ stT326 183 := by
  have hc : ((-4613/8000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1705015543/40000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-4613/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c184 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-682043/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2901687/5000000) (δ := 16447/1000000000) (ψ := -176407/500000) 326 271
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t184 : ((-50288264103/1000000000000 : ℚ) : ℝ) ≤ stT326 184 := by
  have hc : ((-682143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50288264103/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-682143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c185 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((425109/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1385993/10000000) (δ := 4089/250000000) (ψ := -176407/500000) 326 271
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t185 : ((156254663813/2500000000000 : ℚ) : ℝ) ≤ stT326 185 := by
  have hc : ((425059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156254663813/2500000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((425059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c186 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((359557/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3007509/10000000) (δ := 4089/250000000) (ψ := -176407/500000) 326 271
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t186 : ((52713290679/2000000000000 : ℚ) : ℝ) ≤ stT326 186 := by
  have hc : ((359457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52713290679/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((359457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c187 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-196379/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7377539/10000000) (δ := 4089/250000000) (ψ := -176407/500000) 326 271
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t187 : ((-143621285927/2000000000000 : ℚ) : ℝ) ≤ stT326 187 := by
  have hc : ((-196399/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143621285927/2000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-196399/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c188 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-5679/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -796757/2000000) (δ := 16449/1000000000) (ψ := -176407/500000) 326 272
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t188 : ((-20800349/12500000000 : ℚ) : ℝ) ≤ stT326 188 := by
  have hc : ((-713/31250 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20800349/12500000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-713/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c189 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((990773/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10621/312500) (δ := 8177/500000000) (ψ := -176407/500000) 326 272
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t189 : ((22518987963/312500000000 : ℚ) : ℝ) ≤ stT326 189 := by
  have hc : ((990673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22518987963/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((990673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c190 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-140797/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4640627/10000000) (δ := 8177/500000000) (ψ := -176407/500000) 326 272
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t190 : ((-102181259019/5000000000000 : ℚ) : ℝ) ≤ stT326 190 := by
  have hc : ((-140847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102181259019/5000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-140847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c191 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-910641/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -271563/400000) (δ := 8231/500000000) (ψ := -176407/500000) 326 273
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t191 : ((-26359576763/400000000000 : ℚ) : ℝ) ≤ stT326 191 := by
  have hc : ((-910741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26359576763/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-910741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c192 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((529071/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2533227/10000000) (δ := 16341/1000000000) (ψ := -176407/500000) 326 273
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t192 : ((381751494077/10000000000000 : ℚ) : ℝ) ≤ stT326 192 := by
  have hc : ((528971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((381751494077/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((528971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c193 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((388719/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 340107/2000000) (δ := 16341/1000000000) (ψ := -176407/500000) 326 273
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t193 : ((55953955247/1000000000000 : ℚ) : ℝ) ≤ stT326 193 := by
  have hc : ((388669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55953955247/1000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((388669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c194 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-713293/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1182491/2000000) (δ := 16341/1000000000) (ψ := -176407/500000) 326 273
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t194 : ((-512186924887/10000000000000 : ℚ) : ℝ) ≤ stT326 194 := by
  have hc : ((-713393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512186924887/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-713393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c195 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-622013/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5605267/10000000) (δ := 16369/1000000000) (ψ := -176407/500000) 326 274
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t195 : ((-89100890199/2000000000000 : ℚ) : ℝ) ≤ stT326 195 := by
  have hc : ((-622113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89100890199/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-622113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c196 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((419709/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1436461/10000000) (δ := 8217/500000000) (ψ := -176407/500000) 326 274
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t196 : ((59951225763/1000000000000 : ℚ) : ℝ) ≤ stT326 196 := by
  have hc : ((419659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59951225763/1000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((419659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c197 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((116847/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 677789/2500000) (δ := 16369/1000000000) (ψ := -176407/500000) 326 274
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t197 : ((4161608517/125000000000 : ℚ) : ℝ) ≤ stT326 197 := by
  have hc : ((58411/125000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4161608517/125000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((58411/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c198 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-57407/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1367549/2000000) (δ := 8217/500000000) (ψ := -176407/500000) 326 274
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t198 : ((-16320749751/250000000000 : ℚ) : ℝ) ≤ stT326 198 := by
  have hc : ((-229653/250000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16320749751/250000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-229653/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c199 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-328739/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4764411/10000000) (δ := 16327/1000000000) (ψ := -176407/500000) 326 275
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t199 : ((-116554023999/5000000000000 : ℚ) : ℝ) ≤ stT326 199 := by
  have hc : ((-328839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116554023999/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-328839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c200 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((963319/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -679223/10000000) (δ := 4119/250000000) (ψ := -176407/500000) 326 275
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t200 : ((340548967107/5000000000000 : ℚ) : ℝ) ≤ stT326 200 := by
  have hc : ((963219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((340548967107/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((963219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c201 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((5371/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3385671/10000000) (δ := 4119/250000000) (ψ := -176407/500000) 326 275
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t201 : ((1514657853/100000000000 : ℚ) : ℝ) ≤ stT326 201 := by
  have hc : ((10737/50000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1514657853/100000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((10737/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c202 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-123209/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7430271/10000000) (δ := 16327/1000000000) (ψ := -176407/500000) 326 275
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t202 : ((-86698400957/1250000000000 : ℚ) : ℝ) ≤ stT326 202 := by
  have hc : ((-246443/250000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86698400957/1250000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-246443/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c203 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-65013/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2126489/5000000) (δ := 821/50000000) (ψ := -176407/500000) 326 276
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t203 : ((-45665312369/5000000000000 : ℚ) : ℝ) ≤ stT326 203 := by
  have hc : ((-65063/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45665312369/5000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-65063/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c204 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((995081/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -62017/2500000) (δ := 821/50000000) (ψ := -176407/500000) 326 276
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t204 : ((34831299867/500000000000 : ℚ) : ℝ) ≤ stT326 204 := by
  have hc : ((994981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34831299867/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((994981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c205 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((75811/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1868641/5000000) (δ := 821/50000000) (ψ := -176407/500000) 326 276
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t205 : ((5287883373/1000000000000 : ℚ) : ℝ) ≤ stT326 205 := by
  have hc : ((75711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5287883373/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((75711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c206 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-998183/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1540647/2000000) (δ := 821/50000000) (ψ := -176407/500000) 326 276
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t206 : ((-347768853861/5000000000000 : ℚ) : ℝ) ≤ stT326 206 := by
  have hc : ((-998283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-347768853861/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-998283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c207 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-52383/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4058009/10000000) (δ := 16313/1000000000) (ψ := -176407/500000) 326 277
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t207 : ((-36478256667/10000000000000 : ℚ) : ℝ) ≤ stT326 207 := by
  have hc : ((-52483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36478256667/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-52483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c208 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((499321/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -130279/10000000) (δ := 1649/100000000) (ψ := -176407/500000) 326 277
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t208 : ((2769456237/40000000000 : ℚ) : ℝ) ≤ stT326 208 := by
  have hc : ((499271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2769456237/40000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((499271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c209 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((3707/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 59041/156250) (δ := 1649/100000000) (ψ := -176407/500000) 326 277
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t209 : ((5119721171/1250000000000 : ℚ) : ℝ) ≤ stT326 209 := by
  have hc : ((14803/250000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5119721171/1250000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((14803/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c210 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-49863/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7668863/10000000) (δ := 16313/1000000000) (ψ := -176407/500000) 326 277
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t210 : ((-4301526411/62500000000 : ℚ) : ℝ) ≤ stT326 210 := by
  have hc : ((-12467/12500 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4301526411/62500000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-12467/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c211 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-12/125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4167361/10000000) (δ := 16397/1000000000) (ψ := -176407/500000) 326 278
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t211 : ((-661580269/100000000000 : ℚ) : ℝ) ≤ stT326 211 := by
  have hc : ((-961/10000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-661580269/100000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-961/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c212 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((7937/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7849/250000) (δ := 8203/500000000) (ψ := -176407/500000) 326 278
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t212 : ((13626495081/200000000000 : ℚ) : ℝ) ≤ stT326 212 := by
  have hc : ((39681/40000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13626495081/200000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((39681/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c213 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((80773/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3521349/10000000) (δ := 16397/1000000000) (ψ := -176407/500000) 326 278
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t213 : ((13827607731/1250000000000 : ℚ) : ℝ) ≤ stT326 213 := by
  have hc : ((80723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13827607731/1250000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((80723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c214 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-244709/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7338727/10000000) (δ := 8203/500000000) (ψ := -176407/500000) 326 278
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t214 : ((-41824184031/625000000000 : ℚ) : ℝ) ≤ stT326 214 := by
  have hc : ((-122367/125000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41824184031/625000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-122367/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c215 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-254263/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2284853/5000000) (δ := 3261/200000000) (ψ := -176407/500000) 326 279
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t215 : ((-34694858837/2000000000000 : ℚ) : ℝ) ≤ stT326 215 := by
  have hc : ((-254363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34694858837/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-254363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c216 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((475381/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -39389/500000) (δ := 3261/200000000) (ψ := -176407/500000) 326 279
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t216 : ((323421391703/5000000000000 : ℚ) : ℝ) ≤ stT326 216 := by
  have hc : ((475331/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((323421391703/5000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((475331/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c217 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((371057/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2976623/10000000) (δ := 8249/500000000) (ψ := -176407/500000) 326 279
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t217 : ((62955483427/2500000000000 : ℚ) : ℝ) ≤ stT326 217 := by
  have hc : ((370957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62955483427/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((370957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c218 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-179907/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6723749/10000000) (δ := 3261/200000000) (ψ := -176407/500000) 326 279
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t218 : ((-60931019061/1000000000000 : ℚ) : ℝ) ≤ stT326 218 := by
  have hc : ((-179927/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60931019061/1000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-179927/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c219 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-506297/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1313551/2500000) (δ := 16391/1000000000) (ψ := -176407/500000) 326 280
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t219 : ((-171095847993/5000000000000 : ℚ) : ℝ) ≤ stT326 219 := by
  have hc : ((-506397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171095847993/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-506397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c220 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((101989/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1541227/10000000) (δ := 16391/1000000000) (ψ := -176407/500000) 326 280
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t220 : ((137504908647/2500000000000 : ℚ) : ℝ) ≤ stT326 220 := by
  have hc : ((203953/250000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137504908647/2500000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((203953/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c221 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((162733/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2154961/10000000) (δ := 16391/1000000000) (ψ := -176407/500000) 326 280
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t221 : ((855071217/19531250000 : ℚ) : ℝ) ≤ stT326 221 := by
  have hc : ((40677/62500 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((855071217/19531250000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((40677/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c222 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-138211/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 145859/250000) (δ := 16391/1000000000) (ψ := -176407/500000) 326 280
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t222 : ((-92774703267/2000000000000 : ℚ) : ℝ) ≤ stT326 222 := by
  have hc : ((-138231/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92774703267/2000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-138231/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c223 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-791629/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6210667/10000000) (δ := 16319/1000000000) (ψ := -176407/500000) 326 281
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t223 : ((-10603626497/200000000000 : ℚ) : ℝ) ≤ stT326 223 := by
  have hc : ((-791729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10603626497/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-791729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c224 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((518547/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2564113/10000000) (δ := 4121/250000000) (ψ := -176407/500000) 326 281
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t224 : ((346401918391/10000000000000 : ℚ) : ℝ) ≤ stT326 224 := by
  have hc : ((518447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((346401918391/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((518447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c225 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((113803/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1066223/10000000) (δ := 4121/250000000) (ψ := -176407/500000) 326 281
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t225 : ((75860257473/1250000000000 : ℚ) : ℝ) ≤ stT326 225 := by
  have hc : ((227581/250000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75860257473/1250000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((227581/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c226 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-18551/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2340191/5000000) (δ := 32719/1000000000) (ψ := -176407/500000) 326 281
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t226 : ((-49376462739/2500000000000 : ℚ) : ℝ) ≤ stT326 226 := by
  have hc : ((-74229/250000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49376462739/2500000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-74229/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c227 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-985607/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1857329/2500000) (δ := 16377/1000000000) (ψ := -176407/500000) 326 282
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t227 : ((-163559348217/2500000000000 : ℚ) : ℝ) ≤ stT326 227 := by
  have hc : ((-985707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163559348217/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-985707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c228 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((3203/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1923451/5000000) (δ := 16377/1000000000) (ψ := -176407/500000) 326 282
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t228 : ((1057307669/500000000000 : ℚ) : ℝ) ≤ stT326 228 := by
  have hc : ((3193/100000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1057307669/500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((3193/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c229 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((15527/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35017/1250000) (δ := 16377/1000000000) (ψ := -176407/500000) 326 282
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t229 : ((82075908463/1250000000000 : ℚ) : ℝ) ≤ stT326 229 := by
  have hc : ((248407/250000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82075908463/1250000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((248407/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c230 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((259371/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 408883/1250000) (δ := 8213/500000000) (ψ := -176407/500000) 326 282
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t230 : ((8547905599/500000000000 : ℚ) : ℝ) ≤ stT326 230 := by
  have hc : ((259271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8547905599/500000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((259271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c231 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-456779/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 340343/500000) (δ := 8213/500000000) (ψ := -176407/500000) 326 282
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t231 : ((-9392861069/156250000000 : ℚ) : ℝ) ≤ stT326 231 := by
  have hc : ((-456829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9392861069/156250000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-456829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c232 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-549241/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -538063/1000000) (δ := 1647/100000000) (ψ := -176407/500000) 326 283
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t232 : ((-360660494753/10000000000000 : ℚ) : ℝ) ≤ stT326 232 := by
  have hc : ((-549341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-360660494753/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-549341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c233 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((5853/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1875233/10000000) (δ := 16333/1000000000) (ψ := -176407/500000) 326 283
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t233 : ((19169495581/400000000000 : ℚ) : ℝ) ≤ stT326 233 := by
  have hc : ((29261/40000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19169495581/400000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((29261/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c234 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((399229/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1615167/10000000) (δ := 1647/100000000) (ψ := -176407/500000) 326 283
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t234 : ((6523782397/125000000000 : ℚ) : ℝ) ≤ stT326 234 := by
  have hc : ((399179/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6523782397/125000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((399179/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c235 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-224419/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5090653/10000000) (δ := 1647/100000000) (ψ := -176407/500000) 326 283
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t235 : ((-146427638301/5000000000000 : ℚ) : ℝ) ≤ stT326 235 := by
  have hc : ((-224469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146427638301/5000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-224469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c236 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-480671/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -286263/400000) (δ := 16441/1000000000) (ψ := -176407/500000) 326 284
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t236 : ((-62584586269/1000000000000 : ℚ) : ℝ) ≤ stT326 236 := by
  have hc : ((-480721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62584586269/1000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-480721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c237 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((21621/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3710511/10000000) (δ := 8181/500000000) (ψ := -176407/500000) 326 284
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t237 : ((3507023031/625000000000 : ℚ) : ℝ) ≤ stT326 237 := by
  have hc : ((5399/62500 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3507023031/625000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((5399/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c238 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((993781/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -278953/10000000) (δ := 16441/1000000000) (ψ := -176407/500000) 326 284
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t238 : ((644107005243/10000000000000 : ℚ) : ℝ) ≤ stT326 238 := by
  have hc : ((993681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((644107005243/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((993681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c239 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((62057/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156913/500000) (δ := 8181/500000000) (ψ := -176407/500000) 326 284
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t239 : ((20064192651/1000000000000 : ℚ) : ℝ) ≤ stT326 239 := by
  have hc : ((62037/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20064192651/1000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((62037/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c240 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-86527/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6541211/10000000) (δ := 8181/500000000) (ψ := -176407/500000) 326 284
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t240 : ((-27929730213/500000000000 : ℚ) : ℝ) ≤ stT326 240 := by
  have hc : ((-86537/100000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27929730213/500000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-86537/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c241 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-674581/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2888991/5000000) (δ := 4087/250000000) (ψ := -176407/500000) 326 285
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t241 : ((-434600488917/10000000000000 : ℚ) : ℝ) ≤ stT326 241 := by
  have hc : ((-674681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-434600488917/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-674681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c242 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((572461/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -240323/1000000) (δ := 4087/250000000) (ψ := -176407/500000) 326 285
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t242 : ((45990923433/1250000000000 : ℚ) : ℝ) ≤ stT326 242 := by
  have hc : ((572361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45990923433/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((572361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c243 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((185507/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 191517/2000000) (δ := 3291/200000000) (ψ := -176407/500000) 326 285
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t243 : ((237979821/4000000000 : ℚ) : ℝ) ≤ stT326 243 := by
  have hc : ((185487/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237979821/4000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((185487/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c244 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-150481/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4304627/10000000) (δ := 3291/200000000) (ψ := -176407/500000) 326 285
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t244 : ((-19279939497/2000000000000 : ℚ) : ℝ) ≤ stT326 244 := by
  have hc : ((-150581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19279939497/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-150581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c245 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-249067/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7637937/10000000) (δ := 8187/250000000) (ψ := -176407/500000) 326 285
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t245 : ((-39784787421/625000000000 : ℚ) : ℝ) ≤ stT326 245 := by
  have hc : ((-62273/62500 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39784787421/625000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-62273/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c246 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-323383/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2375123/5000000) (δ := 3291/200000000) (ψ := -176407/500000) 326 286
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t246 : ((-206245320691/10000000000000 : ℚ) : ℝ) ≤ stT326 246 := by
  have hc : ((-323483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206245320691/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-323483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c247 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((418893/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -721977/5000000) (δ := 3291/200000000) (ψ := -176407/500000) 326 286
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t247 : ((66625774853/1250000000000 : ℚ) : ℝ) ≤ stT326 247 := by
  have hc : ((418843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66625774853/1250000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((418843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c248 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((369373/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 462243/2500000) (δ := 3291/200000000) (ψ := -176407/500000) 326 286
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t248 : ((46904021/1000000000 : ℚ) : ℝ) ≤ stT326 248 := by
  have hc : ((369323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46904021/1000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((369323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c249 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-92471/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5128613/10000000) (δ := 4087/250000000) (ψ := -176407/500000) 326 286
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t249 : ((-2344554359/80000000000 : ℚ) : ℝ) ≤ stT326 249 := by
  have hc : ((-92491/200000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2344554359/80000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-92491/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_c250 :
    |Real.cos (((326 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-976657/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7312749/10000000) (δ := 16441/1000000000) (ψ := -176407/500000) 326 287
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st326_t250 : ((-77219478149/1250000000000 : ℚ) : ℝ) ≤ stT326 250 := by
  have hc : ((-976757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((326 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st326_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77219478149/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-976757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st326_p1 : ((14661/15625 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT326 (i+1) := by
  rw [Finset.sum_range_one]
  exact st326_t1

theorem st326_p2 : ((1024938077871/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT326 (i+1))
      = (∑ i ∈ Finset.range 1, stT326 (i+1)) + stT326 2 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 1
    simpa using h
  have hprev := st326_p1
  have hstep := st326_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p3 : ((10902089569421/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT326 (i+1))
      = (∑ i ∈ Finset.range 2, stT326 (i+1)) + stT326 3 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 2
    simpa using h
  have hprev := st326_p2
  have hstep := st326_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p4 : ((13388184569421/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT326 (i+1))
      = (∑ i ∈ Finset.range 3, stT326 (i+1)) + stT326 4 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 3
    simpa using h
  have hprev := st326_p3
  have hstep := st326_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p5 : ((11314412620929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT326 (i+1))
      = (∑ i ∈ Finset.range 4, stT326 (i+1)) + stT326 5 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 4
    simpa using h
  have hprev := st326_p4
  have hstep := st326_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p6 : ((1333818263921/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT326 (i+1))
      = (∑ i ∈ Finset.range 5, stT326 (i+1)) + stT326 6 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 5
    simpa using h
  have hprev := st326_p5
  have hstep := st326_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p7 : ((1901839662591/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT326 (i+1))
      = (∑ i ∈ Finset.range 6, stT326 (i+1)) + stT326 7 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 6
    simpa using h
  have hprev := st326_p6
  have hstep := st326_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p8 : ((6754019925819/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT326 (i+1))
      = (∑ i ∈ Finset.range 7, stT326 (i+1)) + stT326 8 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 7
    simpa using h
  have hprev := st326_p7
  have hstep := st326_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p9 : ((36883639317741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT326 (i+1))
      = (∑ i ∈ Finset.range 8, stT326 (i+1)) + stT326 9 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 8
    simpa using h
  have hprev := st326_p8
  have hstep := st326_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p10 : ((33758903882157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT326 (i+1))
      = (∑ i ∈ Finset.range 9, stT326 (i+1)) + stT326 10 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 9
    simpa using h
  have hprev := st326_p9
  have hstep := st326_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p11 : ((30797694090249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT326 (i+1))
      = (∑ i ∈ Finset.range 10, stT326 (i+1)) + stT326 11 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 10
    simpa using h
  have hprev := st326_p10
  have hstep := st326_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p12 : ((673403171191/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT326 (i+1))
      = (∑ i ∈ Finset.range 11, stT326 (i+1)) + stT326 12 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 11
    simpa using h
  have hprev := st326_p11
  have hstep := st326_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p13 : ((709476532531/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT326 (i+1))
      = (∑ i ∈ Finset.range 12, stT326 (i+1)) + stT326 13 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 12
    simpa using h
  have hprev := st326_p12
  have hstep := st326_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p14 : ((19064879427529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT326 (i+1))
      = (∑ i ∈ Finset.range 13, stT326 (i+1)) + stT326 14 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 13
    simpa using h
  have hprev := st326_p13
  have hstep := st326_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p15 : ((4467632839447/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT326 (i+1))
      = (∑ i ∈ Finset.range 14, stT326 (i+1)) + stT326 15 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 14
    simpa using h
  have hprev := st326_p14
  have hstep := st326_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p16 : ((4732046589447/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT326 (i+1))
      = (∑ i ∈ Finset.range 15, stT326 (i+1)) + stT326 16 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 15
    simpa using h
  have hprev := st326_p15
  have hstep := st326_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p17 : ((1254145974579/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT326 (i+1))
      = (∑ i ∈ Finset.range 16, stT326 (i+1)) + stT326 17 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 16
    simpa using h
  have hprev := st326_p16
  have hstep := st326_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p18 : ((10616906686641/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT326 (i+1))
      = (∑ i ∈ Finset.range 17, stT326 (i+1)) + stT326 18 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 17
    simpa using h
  have hprev := st326_p17
  have hstep := st326_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p19 : ((8706722735817/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT326 (i+1))
      = (∑ i ∈ Finset.range 18, stT326 (i+1)) + stT326 19 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 18
    simpa using h
  have hprev := st326_p18
  have hstep := st326_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p20 : ((41303406413313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT326 (i+1))
      = (∑ i ∈ Finset.range 19, stT326 (i+1)) + stT326 20 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 19
    simpa using h
  have hprev := st326_p19
  have hstep := st326_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p21 : ((43468650712033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT326 (i+1))
      = (∑ i ∈ Finset.range 20, stT326 (i+1)) + stT326 21 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 20
    simpa using h
  have hprev := st326_p20
  have hstep := st326_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p22 : ((41520500685929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT326 (i+1))
      = (∑ i ∈ Finset.range 21, stT326 (i+1)) + stT326 22 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 21
    simpa using h
  have hprev := st326_p21
  have hstep := st326_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p23 : ((10346489176201/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT326 (i+1))
      = (∑ i ∈ Finset.range 22, stT326 (i+1)) + stT326 23 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 22
    simpa using h
  have hprev := st326_p22
  have hstep := st326_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p24 : ((1353709171819/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT326 (i+1))
      = (∑ i ∈ Finset.range 23, stT326 (i+1)) + stT326 24 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 23
    simpa using h
  have hprev := st326_p23
  have hstep := st326_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p25 : ((1410912921819/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT326 (i+1))
      = (∑ i ∈ Finset.range 24, stT326 (i+1)) + stT326 25 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 24
    simpa using h
  have hprev := st326_p24
  have hstep := st326_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p26 : ((46729087537749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT326 (i+1))
      = (∑ i ∈ Finset.range 25, stT326 (i+1)) + stT326 26 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 25
    simpa using h
  have hprev := st326_p25
  have hstep := st326_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p27 : ((48522504069249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT326 (i+1))
      = (∑ i ∈ Finset.range 26, stT326 (i+1)) + stT326 27 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 26
    simpa using h
  have hprev := st326_p26
  have hstep := st326_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p28 : ((50304230140671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT326 (i+1))
      = (∑ i ∈ Finset.range 27, stT326 (i+1)) + stT326 28 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 27
    simpa using h
  have hprev := st326_p27
  have hstep := st326_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p29 : ((10099596180557/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT326 (i+1))
      = (∑ i ∈ Finset.range 28, stT326 (i+1)) + stT326 29 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 28
    simpa using h
  have hprev := st326_p28
  have hstep := st326_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p30 : ((48695650392451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT326 (i+1))
      = (∑ i ∈ Finset.range 29, stT326 (i+1)) + stT326 30 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 29
    simpa using h
  have hprev := st326_p29
  have hstep := st326_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p31 : ((24477603495873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT326 (i+1))
      = (∑ i ∈ Finset.range 30, stT326 (i+1)) + stT326 31 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 30
    simpa using h
  have hprev := st326_p30
  have hstep := st326_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p32 : ((5019848389061/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT326 (i+1))
      = (∑ i ∈ Finset.range 31, stT326 (i+1)) + stT326 32 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 31
    simpa using h
  have hprev := st326_p31
  have hstep := st326_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p33 : ((12121717967117/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT326 (i+1))
      = (∑ i ∈ Finset.range 32, stT326 (i+1)) + stT326 33 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 32
    simpa using h
  have hprev := st326_p32
  have hstep := st326_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p34 : ((50188636049103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT326 (i+1))
      = (∑ i ∈ Finset.range 33, stT326 (i+1)) + stT326 34 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 33
    simpa using h
  have hprev := st326_p33
  have hstep := st326_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p35 : ((24258391766537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT326 (i+1))
      = (∑ i ∈ Finset.range 34, stT326 (i+1)) + stT326 35 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 34
    simpa using h
  have hprev := st326_p34
  have hstep := st326_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p36 : ((1568005037583/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT326 (i+1))
      = (∑ i ∈ Finset.range 35, stT326 (i+1)) + stT326 36 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 35
    simpa using h
  have hprev := st326_p35
  have hstep := st326_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p37 : ((24402772683893/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT326 (i+1))
      = (∑ i ∈ Finset.range 36, stT326 (i+1)) + stT326 37 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 36
    simpa using h
  have hprev := st326_p36
  have hstep := st326_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p38 : ((24607032137489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT326 (i+1))
      = (∑ i ∈ Finset.range 37, stT326 (i+1)) + stT326 38 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 37
    simpa using h
  have hprev := st326_p37
  have hstep := st326_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p39 : ((10049607727691/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT326 (i+1))
      = (∑ i ∈ Finset.range 38, stT326 (i+1)) + stT326 39 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 38
    simpa using h
  have hprev := st326_p38
  have hstep := st326_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p40 : ((24369260245869/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT326 (i+1))
      = (∑ i ∈ Finset.range 39, stT326 (i+1)) + stT326 40 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 39
    simpa using h
  have hprev := st326_p39
  have hstep := st326_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p41 : ((24286047721753/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT326 (i+1))
      = (∑ i ∈ Finset.range 40, stT326 (i+1)) + stT326 41 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 40
    simpa using h
  have hprev := st326_p40
  have hstep := st326_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p42 : ((12526625722259/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT326 (i+1))
      = (∑ i ∈ Finset.range 41, stT326 (i+1)) + stT326 42 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 41
    simpa using h
  have hprev := st326_p41
  have hstep := st326_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p43 : ((50539307356901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT326 (i+1))
      = (∑ i ∈ Finset.range 42, stT326 (i+1)) + stT326 43 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 42
    simpa using h
  have hprev := st326_p42
  have hstep := st326_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p44 : ((24668265824017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT326 (i+1))
      = (∑ i ∈ Finset.range 43, stT326 (i+1)) + stT326 44 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 43
    simpa using h
  have hprev := st326_p43
  have hstep := st326_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p45 : ((4796084745809/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT326 (i+1))
      = (∑ i ∈ Finset.range 44, stT326 (i+1)) + stT326 45 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 44
    simpa using h
  have hprev := st326_p44
  have hstep := st326_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p46 : ((4753458821283/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT326 (i+1))
      = (∑ i ∈ Finset.range 45, stT326 (i+1)) + stT326 46 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 45
    simpa using h
  have hprev := st326_p45
  have hstep := st326_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p47 : ((48148712990757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT326 (i+1))
      = (∑ i ∈ Finset.range 46, stT326 (i+1)) + stT326 47 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 46
    simpa using h
  have hprev := st326_p46
  have hstep := st326_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p48 : ((24687308061441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT326 (i+1))
      = (∑ i ∈ Finset.range 47, stT326 (i+1)) + stT326 48 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 47
    simpa using h
  have hprev := st326_p47
  have hstep := st326_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p49 : ((2539662070579/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT326 (i+1))
      = (∑ i ∈ Finset.range 48, stT326 (i+1)) + stT326 49 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 48
    simpa using h
  have hprev := st326_p48
  have hstep := st326_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p50 : ((10436599119549/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT326 (i+1))
      = (∑ i ∈ Finset.range 49, stT326 (i+1)) + stT326 50 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 49
    simpa using h
  have hprev := st326_p49
  have hstep := st326_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p51 : ((10698854480133/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT326 (i+1))
      = (∑ i ∈ Finset.range 50, stT326 (i+1)) + stT326 51 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 50
    simpa using h
  have hprev := st326_p50
  have hstep := st326_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p52 : ((10953708344283/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT326 (i+1))
      = (∑ i ∈ Finset.range 51, stT326 (i+1)) + stT326 52 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 51
    simpa using h
  have hprev := st326_p51
  have hstep := st326_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p53 : ((448536655643/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT326 (i+1))
      = (∑ i ∈ Finset.range 52, stT326 (i+1)) + stT326 53 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 52
    simpa using h
  have hprev := st326_p52
  have hstep := st326_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p54 : ((14353506789787/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT326 (i+1))
      = (∑ i ∈ Finset.range 53, stT326 (i+1)) + stT326 54 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 53
    simpa using h
  have hprev := st326_p53
  have hstep := st326_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p55 : ((58745256994681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT326 (i+1))
      = (∑ i ∈ Finset.range 54, stT326 (i+1)) + stT326 55 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 54
    simpa using h
  have hprev := st326_p54
  have hstep := st326_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p56 : ((11974280162751/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT326 (i+1))
      = (∑ i ∈ Finset.range 55, stT326 (i+1)) + stT326 56 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 55
    simpa using h
  have hprev := st326_p55
  have hstep := st326_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p57 : ((60493929529223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT326 (i+1))
      = (∑ i ∈ Finset.range 56, stT326 (i+1)) + stT326 57 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 56
    simpa using h
  have hprev := st326_p56
  have hstep := st326_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p58 : ((30165661749409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT326 (i+1))
      = (∑ i ∈ Finset.range 57, stT326 (i+1)) + stT326 58 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 57
    simpa using h
  have hprev := st326_p57
  have hstep := st326_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p59 : ((29683286768499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT326 (i+1))
      = (∑ i ∈ Finset.range 58, stT326 (i+1)) + stT326 59 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 58
    simpa using h
  have hprev := st326_p58
  have hstep := st326_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p60 : ((14519602745007/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT326 (i+1))
      = (∑ i ∈ Finset.range 59, stT326 (i+1)) + stT326 60 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 59
    simpa using h
  have hprev := st326_p59
  have hstep := st326_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p61 : ((28673228656161/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT326 (i+1))
      = (∑ i ∈ Finset.range 60, stT326 (i+1)) + stT326 61 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 60
    simpa using h
  have hprev := st326_p60
  have hstep := st326_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p62 : ((11562025157483/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT326 (i+1))
      = (∑ i ∈ Finset.range 61, stT326 (i+1)) + stT326 62 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 61
    simpa using h
  have hprev := st326_p61
  have hstep := st326_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p63 : ((5905926630189/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT326 (i+1))
      = (∑ i ∈ Finset.range 62, stT326 (i+1)) + stT326 63 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 62
    simpa using h
  have hprev := st326_p62
  have hstep := st326_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p64 : ((5971405380189/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT326 (i+1))
      = (∑ i ∈ Finset.range 63, stT326 (i+1)) + stT326 64 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 63
    simpa using h
  have hprev := st326_p63
  have hstep := st326_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p65 : ((29468279511481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT326 (i+1))
      = (∑ i ∈ Finset.range 64, stT326 (i+1)) + stT326 65 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 64
    simpa using h
  have hprev := st326_p64
  have hstep := st326_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p66 : ((57808788545387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT326 (i+1))
      = (∑ i ∈ Finset.range 65, stT326 (i+1)) + stT326 66 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 65
    simpa using h
  have hprev := st326_p65
  have hstep := st326_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p67 : ((11615669110587/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT326 (i+1))
      = (∑ i ∈ Finset.range 66, stT326 (i+1)) + stT326 67 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 66
    simpa using h
  have hprev := st326_p66
  have hstep := st326_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p68 : ((59284192537761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT326 (i+1))
      = (∑ i ∈ Finset.range 67, stT326 (i+1)) + stT326 68 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 67
    simpa using h
  have hprev := st326_p67
  have hstep := st326_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p69 : ((5921378002871/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT326 (i+1))
      = (∑ i ∈ Finset.range 68, stT326 (i+1)) + stT326 69 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 68
    simpa using h
  have hprev := st326_p68
  have hstep := st326_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p70 : ((906597865781/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT326 (i+1))
      = (∑ i ∈ Finset.range 69, stT326 (i+1)) + stT326 70 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 69
    simpa using h
  have hprev := st326_p69
  have hstep := st326_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p71 : ((29110471208597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT326 (i+1))
      = (∑ i ∈ Finset.range 70, stT326 (i+1)) + stT326 71 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 70
    simpa using h
  have hprev := st326_p70
  have hstep := st326_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p72 : ((7417384787333/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT326 (i+1))
      = (∑ i ∈ Finset.range 71, stT326 (i+1)) + stT326 72 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 71
    simpa using h
  have hprev := st326_p71
  have hstep := st326_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p73 : ((14685073002057/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT326 (i+1))
      = (∑ i ∈ Finset.range 72, stT326 (i+1)) + stT326 73 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 72
    simpa using h
  have hprev := st326_p72
  have hstep := st326_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p74 : ((57941936516461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT326 (i+1))
      = (∑ i ∈ Finset.range 73, stT326 (i+1)) + stT326 74 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 73
    simpa using h
  have hprev := st326_p73
  have hstep := st326_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p75 : ((58995957068761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT326 (i+1))
      = (∑ i ∈ Finset.range 74, stT326 (i+1)) + stT326 75 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 74
    simpa using h
  have hprev := st326_p74
  have hstep := st326_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p76 : ((59025649182791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT326 (i+1))
      = (∑ i ∈ Finset.range 75, stT326 (i+1)) + stT326 76 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 75
    simpa using h
  have hprev := st326_p75
  have hstep := st326_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p77 : ((57987260708499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT326 (i+1))
      = (∑ i ∈ Finset.range 76, stT326 (i+1)) + stT326 77 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 76
    simpa using h
  have hprev := st326_p76
  have hstep := st326_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p78 : ((58895328746067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT326 (i+1))
      = (∑ i ∈ Finset.range 77, stT326 (i+1)) + stT326 78 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 77
    simpa using h
  have hprev := st326_p77
  have hstep := st326_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p79 : ((58985738487213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT326 (i+1))
      = (∑ i ∈ Finset.range 78, stT326 (i+1)) + stT326 79 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 78
    simpa using h
  have hprev := st326_p78
  have hstep := st326_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p80 : ((11604326634453/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT326 (i+1))
      = (∑ i ∈ Finset.range 79, stT326 (i+1)) + stT326 80 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 79
    simpa using h
  have hprev := st326_p79
  have hstep := st326_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p81 : ((59054608624523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT326 (i+1))
      = (∑ i ∈ Finset.range 80, stT326 (i+1)) + stT326 81 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 80
    simpa using h
  have hprev := st326_p80
  have hstep := st326_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p82 : ((58691068901639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT326 (i+1))
      = (∑ i ∈ Finset.range 81, stT326 (i+1)) + stT326 82 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 81
    simpa using h
  have hprev := st326_p81
  have hstep := st326_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p83 : ((2909466100849/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT326 (i+1))
      = (∑ i ∈ Finset.range 82, stT326 (i+1)) + stT326 83 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 82
    simpa using h
  have hprev := st326_p82
  have hstep := st326_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p84 : ((59220175266557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT326 (i+1))
      = (∑ i ∈ Finset.range 83, stT326 (i+1)) + stT326 84 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 83
    simpa using h
  have hprev := st326_p83
  have hstep := st326_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p85 : ((58213962202211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT326 (i+1))
      = (∑ i ∈ Finset.range 84, stT326 (i+1)) + stT326 85 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 84
    simpa using h
  have hprev := st326_p84
  have hstep := st326_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p86 : ((29373227046531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT326 (i+1))
      = (∑ i ∈ Finset.range 85, stT326 (i+1)) + stT326 86 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 85
    simpa using h
  have hprev := st326_p85
  have hstep := st326_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p87 : ((29432380826131/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT326 (i+1))
      = (∑ i ∈ Finset.range 86, stT326 (i+1)) + stT326 87 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 86
    simpa using h
  have hprev := st326_p86
  have hstep := st326_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p88 : ((29091066599407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT326 (i+1))
      = (∑ i ∈ Finset.range 87, stT326 (i+1)) + stT326 88 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 87
    simpa using h
  have hprev := st326_p87
  have hstep := st326_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p89 : ((59183477384813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT326 (i+1))
      = (∑ i ∈ Finset.range 88, stT326 (i+1)) + stT326 89 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 88
    simpa using h
  have hprev := st326_p88
  have hstep := st326_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p90 : ((14535985615809/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT326 (i+1))
      = (∑ i ∈ Finset.range 89, stT326 (i+1)) + stT326 90 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 89
    simpa using h
  have hprev := st326_p89
  have hstep := st326_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p91 : ((14748082296819/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT326 (i+1))
      = (∑ i ∈ Finset.range 90, stT326 (i+1)) + stT326 91 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 90
    simpa using h
  have hprev := st326_p90
  have hstep := st326_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p92 : ((5847250020433/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT326 (i+1))
      = (∑ i ∈ Finset.range 91, stT326 (i+1)) + stT326 92 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 91
    simpa using h
  have hprev := st326_p91
  have hstep := st326_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p93 : ((58616181171841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT326 (i+1))
      = (∑ i ∈ Finset.range 92, stT326 (i+1)) + stT326 93 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 92
    simpa using h
  have hprev := st326_p92
  have hstep := st326_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p94 : ((29413508516357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT326 (i+1))
      = (∑ i ∈ Finset.range 93, stT326 (i+1)) + stT326 94 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 93
    simpa using h
  have hprev := st326_p93
  have hstep := st326_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p95 : ((58322353352299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT326 (i+1))
      = (∑ i ∈ Finset.range 94, stT326 (i+1)) + stT326 95 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 94
    simpa using h
  have hprev := st326_p94
  have hstep := st326_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p96 : ((59044509363219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT326 (i+1))
      = (∑ i ∈ Finset.range 95, stT326 (i+1)) + stT326 96 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 95
    simpa using h
  have hprev := st326_p95
  have hstep := st326_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p97 : ((58177701537237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT326 (i+1))
      = (∑ i ∈ Finset.range 96, stT326 (i+1)) + stT326 97 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 96
    simpa using h
  have hprev := st326_p96
  have hstep := st326_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p98 : ((59127922229229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT326 (i+1))
      = (∑ i ∈ Finset.range 97, stT326 (i+1)) + stT326 98 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 97
    simpa using h
  have hprev := st326_p97
  have hstep := st326_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p99 : ((2325545206383/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT326 (i+1))
      = (∑ i ∈ Finset.range 98, stT326 (i+1)) + stT326 99 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 98
    simpa using h
  have hprev := st326_p98
  have hstep := st326_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p100 : ((295688020803/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT326 (i+1))
      = (∑ i ∈ Finset.range 99, stT326 (i+1)) + stT326 100 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 99
    simpa using h
  have hprev := st326_p99
  have hstep := st326_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p101 : ((14536052988363/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT326 (i+1))
      = (∑ i ∈ Finset.range 100, stT326 (i+1)) + stT326 101 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 100
    simpa using h
  have hprev := st326_p100
  have hstep := st326_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p102 : ((14781492607017/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT326 (i+1))
      = (∑ i ∈ Finset.range 101, stT326 (i+1)) + stT326 102 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 101
    simpa using h
  have hprev := st326_p101
  have hstep := st326_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p103 : ((29077238708629/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT326 (i+1))
      = (∑ i ∈ Finset.range 102, stT326 (i+1)) + stT326 103 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 102
    simpa using h
  have hprev := st326_p102
  have hstep := st326_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p104 : ((29559856650709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT326 (i+1))
      = (∑ i ∈ Finset.range 103, stT326 (i+1)) + stT326 104 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 103
    simpa using h
  have hprev := st326_p103
  have hstep := st326_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p105 : ((1163107183241/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT326 (i+1))
      = (∑ i ∈ Finset.range 104, stT326 (i+1)) + stT326 105 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 104
    simpa using h
  have hprev := st326_p104
  have hstep := st326_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p106 : ((295606947551/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT326 (i+1))
      = (∑ i ∈ Finset.range 105, stT326 (i+1)) + stT326 106 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 105
    simpa using h
  have hprev := st326_p105
  have hstep := st326_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p107 : ((11630960470887/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT326 (i+1))
      = (∑ i ∈ Finset.range 106, stT326 (i+1)) + stT326 107 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 106
    simpa using h
  have hprev := st326_p106
  have hstep := st326_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p108 : ((11822672810037/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT326 (i+1))
      = (∑ i ∈ Finset.range 107, stT326 (i+1)) + stT326 108 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 107
    simpa using h
  have hprev := st326_p107
  have hstep := st326_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p109 : ((58179245184089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT326 (i+1))
      = (∑ i ∈ Finset.range 108, stT326 (i+1)) + stT326 109 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 108
    simpa using h
  have hprev := st326_p108
  have hstep := st326_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p110 : ((59061808703231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT326 (i+1))
      = (∑ i ∈ Finset.range 109, stT326 (i+1)) + stT326 110 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 109
    simpa using h
  have hprev := st326_p109
  have hstep := st326_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p111 : ((58267327389227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT326 (i+1))
      = (∑ i ∈ Finset.range 110, stT326 (i+1)) + stT326 111 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 110
    simpa using h
  have hprev := st326_p110
  have hstep := st326_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p112 : ((2946380756627/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT326 (i+1))
      = (∑ i ∈ Finset.range 111, stT326 (i+1)) + stT326 112 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 111
    simpa using h
  have hprev := st326_p111
  have hstep := st326_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p113 : ((29225954727909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT326 (i+1))
      = (∑ i ∈ Finset.range 112, stT326 (i+1)) + stT326 113 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 112
    simpa using h
  have hprev := st326_p112
  have hstep := st326_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p114 : ((29346622466139/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT326 (i+1))
      = (∑ i ∈ Finset.range 113, stT326 (i+1)) + stT326 114 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 113
    simpa using h
  have hprev := st326_p113
  have hstep := st326_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p115 : ((29362279674551/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT326 (i+1))
      = (∑ i ∈ Finset.range 114, stT326 (i+1)) + stT326 115 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 114
    simpa using h
  have hprev := st326_p114
  have hstep := st326_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p116 : ((29201838848951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT326 (i+1))
      = (∑ i ∈ Finset.range 115, stT326 (i+1)) + stT326 116 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 115
    simpa using h
  have hprev := st326_p115
  have hstep := st326_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p117 : ((29498181776951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT326 (i+1))
      = (∑ i ∈ Finset.range 116, stT326 (i+1)) + stT326 117 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 116
    simpa using h
  have hprev := st326_p116
  have hstep := st326_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p118 : ((58191789289077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT326 (i+1))
      = (∑ i ∈ Finset.range 117, stT326 (i+1)) + stT326 118 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 117
    simpa using h
  have hprev := st326_p117
  have hstep := st326_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p119 : ((2364084686187/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT326 (i+1))
      = (∑ i ∈ Finset.range 118, stT326 (i+1)) + stT326 119 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 118
    simpa using h
  have hprev := st326_p118
  have hstep := st326_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p120 : ((29114483955249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT326 (i+1))
      = (∑ i ∈ Finset.range 119, stT326 (i+1)) + stT326 120 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 119
    simpa using h
  have hprev := st326_p119
  have hstep := st326_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p121 : ((14726181126867/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT326 (i+1))
      = (∑ i ∈ Finset.range 120, stT326 (i+1)) + stT326 121 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 120
    simpa using h
  have hprev := st326_p120
  have hstep := st326_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p122 : ((1830282427467/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT326 (i+1))
      = (∑ i ∈ Finset.range 121, stT326 (i+1)) + stT326 122 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 121
    simpa using h
  have hprev := st326_p121
  have hstep := st326_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p123 : ((29239187831057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT326 (i+1))
      = (∑ i ∈ Finset.range 122, stT326 (i+1)) + stT326 123 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 122
    simpa using h
  have hprev := st326_p122
  have hstep := st326_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p124 : ((29493609373169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT326 (i+1))
      = (∑ i ∈ Finset.range 123, stT326 (i+1)) + stT326 124 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 123
    simpa using h
  have hprev := st326_p123
  have hstep := st326_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p125 : ((29089938811493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT326 (i+1))
      = (∑ i ∈ Finset.range 124, stT326 (i+1)) + stT326 125 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 124
    simpa using h
  have hprev := st326_p124
  have hstep := st326_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p126 : ((1845822360773/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT326 (i+1))
      = (∑ i ∈ Finset.range 125, stT326 (i+1)) + stT326 126 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 125
    simpa using h
  have hprev := st326_p125
  have hstep := st326_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p127 : ((58367027649387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT326 (i+1))
      = (∑ i ∈ Finset.range 126, stT326 (i+1)) + stT326 127 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 126
    simpa using h
  have hprev := st326_p126
  have hstep := st326_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p128 : ((14661826516201/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT326 (i+1))
      = (∑ i ∈ Finset.range 127, stT326 (i+1)) + stT326 128 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 127
    simpa using h
  have hprev := st326_p127
  have hstep := st326_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p129 : ((29446037783527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT326 (i+1))
      = (∑ i ∈ Finset.range 128, stT326 (i+1)) + stT326 129 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 128
    simpa using h
  have hprev := st326_p128
  have hstep := st326_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p130 : ((29100841394071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT326 (i+1))
      = (∑ i ∈ Finset.range 129, stT326 (i+1)) + stT326 130 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 129
    simpa using h
  have hprev := st326_p129
  have hstep := st326_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p131 : ((29537550980319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT326 (i+1))
      = (∑ i ∈ Finset.range 130, stT326 (i+1)) + stT326 131 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 130
    simpa using h
  have hprev := st326_p130
  have hstep := st326_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p132 : ((58377517381531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT326 (i+1))
      = (∑ i ∈ Finset.range 131, stT326 (i+1)) + stT326 132 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 131
    simpa using h
  have hprev := st326_p131
  have hstep := st326_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p133 : ((58590583405011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT326 (i+1))
      = (∑ i ∈ Finset.range 132, stT326 (i+1)) + stT326 133 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 132
    simpa using h
  have hprev := st326_p132
  have hstep := st326_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p134 : ((58967241947163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT326 (i+1))
      = (∑ i ∈ Finset.range 133, stT326 (i+1)) + stT326 134 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 133
    simpa using h
  have hprev := st326_p133
  have hstep := st326_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p135 : ((14543752780739/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT326 (i+1))
      = (∑ i ∈ Finset.range 134, stT326 (i+1)) + stT326 135 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 134
    simpa using h
  have hprev := st326_p134
  have hstep := st326_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p136 : ((2949252132787/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT326 (i+1))
      = (∑ i ∈ Finset.range 135, stT326 (i+1)) + stT326 136 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 135
    simpa using h
  have hprev := st326_p135
  have hstep := st326_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p137 : ((29293870704679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT326 (i+1))
      = (∑ i ∈ Finset.range 136, stT326 (i+1)) + stT326 137 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 136
    simpa using h
  have hprev := st326_p136
  have hstep := st326_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p138 : ((11669314527989/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT326 (i+1))
      = (∑ i ∈ Finset.range 137, stT326 (i+1)) + stT326 138 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 137
    simpa using h
  have hprev := st326_p137
  have hstep := st326_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p139 : ((59092510728357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT326 (i+1))
      = (∑ i ∈ Finset.range 138, stT326 (i+1)) + stT326 139 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 138
    simpa using h
  have hprev := st326_p138
  have hstep := st326_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p140 : ((29143621409291/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT326 (i+1))
      = (∑ i ∈ Finset.range 139, stT326 (i+1)) + stT326 140 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 139
    simpa using h
  have hprev := st326_p139
  have hstep := st326_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p141 : ((1832699842361/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT326 (i+1))
      = (∑ i ∈ Finset.range 140, stT326 (i+1)) + stT326 141 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 140
    simpa using h
  have hprev := st326_p140
  have hstep := st326_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p142 : ((29485386828827/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT326 (i+1))
      = (∑ i ∈ Finset.range 141, stT326 (i+1)) + stT326 142 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 141
    simpa using h
  have hprev := st326_p141
  have hstep := st326_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p143 : ((14544221591401/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT326 (i+1))
      = (∑ i ∈ Finset.range 142, stT326 (i+1)) + stT326 143 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 142
    simpa using h
  have hprev := st326_p142
  have hstep := st326_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p144 : ((29443647207387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT326 (i+1))
      = (∑ i ∈ Finset.range 143, stT326 (i+1)) + stT326 144 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 143
    simpa using h
  have hprev := st326_p143
  have hstep := st326_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p145 : ((58775102435639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT326 (i+1))
      = (∑ i ∈ Finset.range 144, stT326 (i+1)) + stT326 145 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 144
    simpa using h
  have hprev := st326_p144
  have hstep := st326_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p146 : ((58201503613947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT326 (i+1))
      = (∑ i ∈ Finset.range 145, stT326 (i+1)) + stT326 146 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 145
    simpa using h
  have hprev := st326_p145
  have hstep := st326_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p147 : ((59021115731369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT326 (i+1))
      = (∑ i ∈ Finset.range 146, stT326 (i+1)) + stT326 147 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 146
    simpa using h
  have hprev := st326_p146
  have hstep := st326_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p148 : ((58606752983839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT326 (i+1))
      = (∑ i ∈ Finset.range 147, stT326 (i+1)) + stT326 148 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 147
    simpa using h
  have hprev := st326_p147
  have hstep := st326_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p149 : ((58274072699423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT326 (i+1))
      = (∑ i ∈ Finset.range 148, stT326 (i+1)) + stT326 149 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 148
    simpa using h
  have hprev := st326_p148
  have hstep := st326_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p150 : ((11815105278723/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT326 (i+1))
      = (∑ i ∈ Finset.range 149, stT326 (i+1)) + stT326 150 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 149
    simpa using h
  have hprev := st326_p149
  have hstep := st326_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p151 : ((7312381105659/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT326 (i+1))
      = (∑ i ∈ Finset.range 150, stT326 (i+1)) + stT326 151 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 150
    simpa using h
  have hprev := st326_p150
  have hstep := st326_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p152 : ((14583920692971/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT326 (i+1))
      = (∑ i ∈ Finset.range 151, stT326 (i+1)) + stT326 152 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 151
    simpa using h
  have hprev := st326_p151
  have hstep := st326_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p153 : ((14772755273097/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT326 (i+1))
      = (∑ i ∈ Finset.range 152, stT326 (i+1)) + stT326 153 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 152
    simpa using h
  have hprev := st326_p152
  have hstep := st326_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p154 : ((913299811883/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT326 (i+1))
      = (∑ i ∈ Finset.range 153, stT326 (i+1)) + stT326 154 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 153
    simpa using h
  have hprev := st326_p153
  have hstep := st326_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p155 : ((455933333299/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT326 (i+1))
      = (∑ i ∈ Finset.range 154, stT326 (i+1)) + stT326 155 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 154
    simpa using h
  have hprev := st326_p154
  have hstep := st326_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p156 : ((115416489871/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT326 (i+1))
      = (∑ i ∈ Finset.range 155, stT326 (i+1)) + stT326 156 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 155
    simpa using h
  have hprev := st326_p155
  have hstep := st326_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p157 : ((5845646036987/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT326 (i+1))
      = (∑ i ∈ Finset.range 156, stT326 (i+1)) + stT326 157 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 156
    simpa using h
  have hprev := st326_p156
  have hstep := st326_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p158 : ((29169479022193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT326 (i+1))
      = (∑ i ∈ Finset.range 157, stT326 (i+1)) + stT326 158 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 157
    simpa using h
  have hprev := st326_p157
  have hstep := st326_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p159 : ((59087094601001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT326 (i+1))
      = (∑ i ∈ Finset.range 158, stT326 (i+1)) + stT326 159 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 158
    simpa using h
  have hprev := st326_p158
  have hstep := st326_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p160 : ((58513894194211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT326 (i+1))
      = (∑ i ∈ Finset.range 159, stT326 (i+1)) + stT326 160 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 159
    simpa using h
  have hprev := st326_p159
  have hstep := st326_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p161 : ((29140647527113/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT326 (i+1))
      = (∑ i ∈ Finset.range 160, stT326 (i+1)) + stT326 161 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 160
    simpa using h
  have hprev := st326_p160
  have hstep := st326_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p162 : ((1845570816979/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT326 (i+1))
      = (∑ i ∈ Finset.range 161, stT326 (i+1)) + stT326 162 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 161
    simpa using h
  have hprev := st326_p161
  have hstep := st326_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p163 : ((58626535029911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT326 (i+1))
      = (∑ i ∈ Finset.range 162, stT326 (i+1)) + stT326 163 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 162
    simpa using h
  have hprev := st326_p162
  have hstep := st326_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p164 : ((90951570557/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT326 (i+1))
      = (∑ i ∈ Finset.range 163, stT326 (i+1)) + stT326 164 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 163
    simpa using h
  have hprev := st326_p163
  have hstep := st326_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p165 : ((29489161164783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT326 (i+1))
      = (∑ i ∈ Finset.range 164, stT326 (i+1)) + stT326 165 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 164
    simpa using h
  have hprev := st326_p164
  have hstep := st326_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p166 : ((1469732346453/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT326 (i+1))
      = (∑ i ∈ Finset.range 165, stT326 (i+1)) + stT326 166 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 165
    simpa using h
  have hprev := st326_p165
  have hstep := st326_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p167 : ((7270670816417/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT326 (i+1))
      = (∑ i ∈ Finset.range 166, stT326 (i+1)) + stT326 167 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 166
    simpa using h
  have hprev := st326_p166
  have hstep := st326_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p168 : ((7352255547353/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT326 (i+1))
      = (∑ i ∈ Finset.range 167, stT326 (i+1)) + stT326 168 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 167
    simpa using h
  have hprev := st326_p167
  have hstep := st326_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p169 : ((29484747113687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT326 (i+1))
      = (∑ i ∈ Finset.range 168, stT326 (i+1)) + stT326 169 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 168
    simpa using h
  have hprev := st326_p168
  have hstep := st326_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p170 : ((58211555638459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT326 (i+1))
      = (∑ i ∈ Finset.range 169, stT326 (i+1)) + stT326 170 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 169
    simpa using h
  have hprev := st326_p169
  have hstep := st326_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p171 : ((58575047991291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT326 (i+1))
      = (∑ i ∈ Finset.range 170, stT326 (i+1)) + stT326 171 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 170
    simpa using h
  have hprev := st326_p170
  have hstep := st326_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p172 : ((59092070179239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT326 (i+1))
      = (∑ i ∈ Finset.range 171, stT326 (i+1)) + stT326 172 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 171
    simpa using h
  have hprev := st326_p171
  have hstep := st326_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p173 : ((11679944819297/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT326 (i+1))
      = (∑ i ∈ Finset.range 172, stT326 (i+1)) + stT326 173 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 172
    simpa using h
  have hprev := st326_p172
  have hstep := st326_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p174 : ((14577592310413/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT326 (i+1))
      = (∑ i ∈ Finset.range 173, stT326 (i+1)) + stT326 174 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 173
    simpa using h
  have hprev := st326_p173
  have hstep := st326_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p175 : ((2952704677001/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT326 (i+1))
      = (∑ i ∈ Finset.range 174, stT326 (i+1)) + stT326 175 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 174
    simpa using h
  have hprev := st326_p174
  have hstep := st326_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p176 : ((29357625140633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT326 (i+1))
      = (∑ i ∈ Finset.range 175, stT326 (i+1)) + stT326 176 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 175
    simpa using h
  have hprev := st326_p175
  have hstep := st326_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p177 : ((11632262850641/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT326 (i+1))
      = (∑ i ∈ Finset.range 176, stT326 (i+1)) + stT326 177 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 176
    simpa using h
  have hprev := st326_p176
  have hstep := st326_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p178 : ((14698811833917/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT326 (i+1))
      = (∑ i ∈ Finset.range 177, stT326 (i+1)) + stT326 178 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 177
    simpa using h
  have hprev := st326_p177
  have hstep := st326_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p179 : ((59021078094003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT326 (i+1))
      = (∑ i ∈ Finset.range 178, stT326 (i+1)) + stT326 179 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 178
    simpa using h
  have hprev := st326_p178
  have hstep := st326_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p180 : ((11655413045103/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT326 (i+1))
      = (∑ i ∈ Finset.range 179, stT326 (i+1)) + stT326 180 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 179
    simpa using h
  have hprev := st326_p179
  have hstep := st326_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p181 : ((11681078243629/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT326 (i+1))
      = (∑ i ∈ Finset.range 180, stT326 (i+1)) + stT326 181 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 180
    simpa using h
  have hprev := st326_p180
  have hstep := st326_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p182 : ((2363534232371/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT326 (i+1))
      = (∑ i ∈ Finset.range 181, stT326 (i+1)) + stT326 182 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 181
    simpa using h
  have hprev := st326_p181
  have hstep := st326_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p183 : ((2346484076941/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT326 (i+1))
      = (∑ i ∈ Finset.range 182, stT326 (i+1)) + stT326 183 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 182
    simpa using h
  have hprev := st326_p182
  have hstep := st326_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p184 : ((11631843856499/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT326 (i+1))
      = (∑ i ∈ Finset.range 183, stT326 (i+1)) + stT326 184 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 183
    simpa using h
  have hprev := st326_p183
  have hstep := st326_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p185 : ((58784237937747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT326 (i+1))
      = (∑ i ∈ Finset.range 184, stT326 (i+1)) + stT326 185 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 184
    simpa using h
  have hprev := st326_p184
  have hstep := st326_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p186 : ((29523902195571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT326 (i+1))
      = (∑ i ∈ Finset.range 185, stT326 (i+1)) + stT326 186 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 185
    simpa using h
  have hprev := st326_p185
  have hstep := st326_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p187 : ((58329697961507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT326 (i+1))
      = (∑ i ∈ Finset.range 186, stT326 (i+1)) + stT326 187 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 186
    simpa using h
  have hprev := st326_p186
  have hstep := st326_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p188 : ((58313057682307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT326 (i+1))
      = (∑ i ∈ Finset.range 187, stT326 (i+1)) + stT326 188 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 187
    simpa using h
  have hprev := st326_p187
  have hstep := st326_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p189 : ((59033665297123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT326 (i+1))
      = (∑ i ∈ Finset.range 188, stT326 (i+1)) + stT326 189 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 188
    simpa using h
  have hprev := st326_p188
  have hstep := st326_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p190 : ((11765860555817/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT326 (i+1))
      = (∑ i ∈ Finset.range 189, stT326 (i+1)) + stT326 190 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 189
    simpa using h
  have hprev := st326_p189
  have hstep := st326_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p191 : ((5817031336001/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT326 (i+1))
      = (∑ i ∈ Finset.range 190, stT326 (i+1)) + stT326 191 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 190
    simpa using h
  have hprev := st326_p190
  have hstep := st326_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p192 : ((58552064854087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT326 (i+1))
      = (∑ i ∈ Finset.range 191, stT326 (i+1)) + stT326 192 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 191
    simpa using h
  have hprev := st326_p191
  have hstep := st326_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p193 : ((59111604406557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT326 (i+1))
      = (∑ i ∈ Finset.range 192, stT326 (i+1)) + stT326 193 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 192
    simpa using h
  have hprev := st326_p192
  have hstep := st326_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p194 : ((5859941748167/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT326 (i+1))
      = (∑ i ∈ Finset.range 193, stT326 (i+1)) + stT326 194 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 193
    simpa using h
  have hprev := st326_p193
  have hstep := st326_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p195 : ((2326156521227/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT326 (i+1))
      = (∑ i ∈ Finset.range 194, stT326 (i+1)) + stT326 195 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 194
    simpa using h
  have hprev := st326_p194
  have hstep := st326_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p196 : ((11750685057661/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT326 (i+1))
      = (∑ i ∈ Finset.range 195, stT326 (i+1)) + stT326 196 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 195
    simpa using h
  have hprev := st326_p195
  have hstep := st326_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p197 : ((11817270793933/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT326 (i+1))
      = (∑ i ∈ Finset.range 196, stT326 (i+1)) + stT326 197 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 196
    simpa using h
  have hprev := st326_p196
  have hstep := st326_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p198 : ((467468191837/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT326 (i+1))
      = (∑ i ∈ Finset.range 197, stT326 (i+1)) + stT326 198 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 197
    simpa using h
  have hprev := st326_p197
  have hstep := st326_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p199 : ((58200415931627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT326 (i+1))
      = (∑ i ∈ Finset.range 198, stT326 (i+1)) + stT326 199 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 198
    simpa using h
  have hprev := st326_p198
  have hstep := st326_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p200 : ((58881513865841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT326 (i+1))
      = (∑ i ∈ Finset.range 199, stT326 (i+1)) + stT326 200 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 199
    simpa using h
  have hprev := st326_p199
  have hstep := st326_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p201 : ((59032979651141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT326 (i+1))
      = (∑ i ∈ Finset.range 200, stT326 (i+1)) + stT326 201 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 200
    simpa using h
  have hprev := st326_p200
  have hstep := st326_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p202 : ((11667878488697/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT326 (i+1))
      = (∑ i ∈ Finset.range 201, stT326 (i+1)) + stT326 202 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 201
    simpa using h
  have hprev := st326_p201
  have hstep := st326_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p203 : ((58248061818747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT326 (i+1))
      = (∑ i ∈ Finset.range 202, stT326 (i+1)) + stT326 203 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 202
    simpa using h
  have hprev := st326_p202
  have hstep := st326_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p204 : ((58944687816087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT326 (i+1))
      = (∑ i ∈ Finset.range 203, stT326 (i+1)) + stT326 204 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 203
    simpa using h
  have hprev := st326_p203
  have hstep := st326_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p205 : ((58997566649817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT326 (i+1))
      = (∑ i ∈ Finset.range 204, stT326 (i+1)) + stT326 205 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 204
    simpa using h
  have hprev := st326_p204
  have hstep := st326_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p206 : ((11660405788419/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT326 (i+1))
      = (∑ i ∈ Finset.range 205, stT326 (i+1)) + stT326 206 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 205
    simpa using h
  have hprev := st326_p205
  have hstep := st326_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p207 : ((14566387671357/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT326 (i+1))
      = (∑ i ∈ Finset.range 206, stT326 (i+1)) + stT326 207 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 206
    simpa using h
  have hprev := st326_p206
  have hstep := st326_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p208 : ((29478957372339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT326 (i+1))
      = (∑ i ∈ Finset.range 207, stT326 (i+1)) + stT326 208 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 207
    simpa using h
  have hprev := st326_p207
  have hstep := st326_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p209 : ((29499436257023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT326 (i+1))
      = (∑ i ∈ Finset.range 208, stT326 (i+1)) + stT326 209 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 208
    simpa using h
  have hprev := st326_p208
  have hstep := st326_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p210 : ((29155314144143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT326 (i+1))
      = (∑ i ∈ Finset.range 209, stT326 (i+1)) + stT326 210 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 209
    simpa using h
  have hprev := st326_p209
  have hstep := st326_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p211 : ((29122235130693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT326 (i+1))
      = (∑ i ∈ Finset.range 210, stT326 (i+1)) + stT326 211 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 210
    simpa using h
  have hprev := st326_p210
  have hstep := st326_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p212 : ((14731448753859/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT326 (i+1))
      = (∑ i ∈ Finset.range 211, stT326 (i+1)) + stT326 212 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 211
    simpa using h
  have hprev := st326_p211
  have hstep := st326_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p213 : ((14759103969321/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT326 (i+1))
      = (∑ i ∈ Finset.range 212, stT326 (i+1)) + stT326 213 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 212
    simpa using h
  have hprev := st326_p212
  have hstep := st326_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p214 : ((14591807233197/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT326 (i+1))
      = (∑ i ∈ Finset.range 213, stT326 (i+1)) + stT326 214 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 213
    simpa using h
  have hprev := st326_p213
  have hstep := st326_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p215 : ((58193754638603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT326 (i+1))
      = (∑ i ∈ Finset.range 214, stT326 (i+1)) + stT326 215 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 214
    simpa using h
  have hprev := st326_p214
  have hstep := st326_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p216 : ((58840597422009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT326 (i+1))
      = (∑ i ∈ Finset.range 215, stT326 (i+1)) + stT326 216 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 215
    simpa using h
  have hprev := st326_p215
  have hstep := st326_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p217 : ((59092419355717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT326 (i+1))
      = (∑ i ∈ Finset.range 216, stT326 (i+1)) + stT326 217 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 216
    simpa using h
  have hprev := st326_p216
  have hstep := st326_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p218 : ((58483109165107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT326 (i+1))
      = (∑ i ∈ Finset.range 217, stT326 (i+1)) + stT326 218 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 217
    simpa using h
  have hprev := st326_p217
  have hstep := st326_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p219 : ((58140917469121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT326 (i+1))
      = (∑ i ∈ Finset.range 218, stT326 (i+1)) + stT326 219 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 218
    simpa using h
  have hprev := st326_p218
  have hstep := st326_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p220 : ((58690937103709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT326 (i+1))
      = (∑ i ∈ Finset.range 219, stT326 (i+1)) + stT326 220 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 219
    simpa using h
  have hprev := st326_p219
  have hstep := st326_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p221 : ((59128733566813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT326 (i+1))
      = (∑ i ∈ Finset.range 220, stT326 (i+1)) + stT326 221 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 220
    simpa using h
  have hprev := st326_p220
  have hstep := st326_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p222 : ((29332430025239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT326 (i+1))
      = (∑ i ∈ Finset.range 221, stT326 (i+1)) + stT326 222 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 221
    simpa using h
  have hprev := st326_p221
  have hstep := st326_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p223 : ((14533669681407/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT326 (i+1))
      = (∑ i ∈ Finset.range 222, stT326 (i+1)) + stT326 223 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 222
    simpa using h
  have hprev := st326_p222
  have hstep := st326_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p224 : ((58481080644019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT326 (i+1))
      = (∑ i ∈ Finset.range 223, stT326 (i+1)) + stT326 224 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 223
    simpa using h
  have hprev := st326_p223
  have hstep := st326_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p225 : ((59087962703803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT326 (i+1))
      = (∑ i ∈ Finset.range 224, stT326 (i+1)) + stT326 225 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 224
    simpa using h
  have hprev := st326_p224
  have hstep := st326_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p226 : ((58890456852847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT326 (i+1))
      = (∑ i ∈ Finset.range 225, stT326 (i+1)) + stT326 226 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 225
    simpa using h
  have hprev := st326_p225
  have hstep := st326_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p227 : ((58236219459979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT326 (i+1))
      = (∑ i ∈ Finset.range 226, stT326 (i+1)) + stT326 227 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 226
    simpa using h
  have hprev := st326_p226
  have hstep := st326_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p228 : ((58257365613359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT326 (i+1))
      = (∑ i ∈ Finset.range 227, stT326 (i+1)) + stT326 228 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 227
    simpa using h
  have hprev := st326_p227
  have hstep := st326_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p229 : ((58913972881063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT326 (i+1))
      = (∑ i ∈ Finset.range 228, stT326 (i+1)) + stT326 229 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 228
    simpa using h
  have hprev := st326_p228
  have hstep := st326_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p230 : ((59084930993043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT326 (i+1))
      = (∑ i ∈ Finset.range 229, stT326 (i+1)) + stT326 230 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 229
    simpa using h
  have hprev := st326_p229
  have hstep := st326_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p231 : ((58483787884627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT326 (i+1))
      = (∑ i ∈ Finset.range 230, stT326 (i+1)) + stT326 231 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 230
    simpa using h
  have hprev := st326_p230
  have hstep := st326_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p232 : ((29061563694937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT326 (i+1))
      = (∑ i ∈ Finset.range 231, stT326 (i+1)) + stT326 232 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 231
    simpa using h
  have hprev := st326_p231
  have hstep := st326_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p233 : ((58602364779399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT326 (i+1))
      = (∑ i ∈ Finset.range 232, stT326 (i+1)) + stT326 233 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 232
    simpa using h
  have hprev := st326_p232
  have hstep := st326_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p234 : ((59124267371159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT326 (i+1))
      = (∑ i ∈ Finset.range 233, stT326 (i+1)) + stT326 234 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 233
    simpa using h
  have hprev := st326_p233
  have hstep := st326_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p235 : ((58831412094557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT326 (i+1))
      = (∑ i ∈ Finset.range 234, stT326 (i+1)) + stT326 235 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 234
    simpa using h
  have hprev := st326_p234
  have hstep := st326_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p236 : ((58205566231867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT326 (i+1))
      = (∑ i ∈ Finset.range 235, stT326 (i+1)) + stT326 236 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 235
    simpa using h
  have hprev := st326_p235
  have hstep := st326_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p237 : ((58261678600363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT326 (i+1))
      = (∑ i ∈ Finset.range 236, stT326 (i+1)) + stT326 237 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 236
    simpa using h
  have hprev := st326_p236
  have hstep := st326_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p238 : ((29452892802803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT326 (i+1))
      = (∑ i ∈ Finset.range 237, stT326 (i+1)) + stT326 238 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 237
    simpa using h
  have hprev := st326_p237
  have hstep := st326_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p239 : ((14776606883029/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT326 (i+1))
      = (∑ i ∈ Finset.range 238, stT326 (i+1)) + stT326 239 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 238
    simpa using h
  have hprev := st326_p238
  have hstep := st326_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p240 : ((3659239557991/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT326 (i+1))
      = (∑ i ∈ Finset.range 239, stT326 (i+1)) + stT326 240 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 239
    simpa using h
  have hprev := st326_p239
  have hstep := st326_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p241 : ((58113232438939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT326 (i+1))
      = (∑ i ∈ Finset.range 240, stT326 (i+1)) + stT326 241 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 240
    simpa using h
  have hprev := st326_p240
  have hstep := st326_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p242 : ((58481159826403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT326 (i+1))
      = (∑ i ∈ Finset.range 241, stT326 (i+1)) + stT326 242 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 241
    simpa using h
  have hprev := st326_p241
  have hstep := st326_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p243 : ((59076109378903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT326 (i+1))
      = (∑ i ∈ Finset.range 242, stT326 (i+1)) + stT326 243 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 242
    simpa using h
  have hprev := st326_p242
  have hstep := st326_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p244 : ((29489854840709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT326 (i+1))
      = (∑ i ∈ Finset.range 243, stT326 (i+1)) + stT326 244 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 243
    simpa using h
  have hprev := st326_p243
  have hstep := st326_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p245 : ((29171576541341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT326 (i+1))
      = (∑ i ∈ Finset.range 244, stT326 (i+1)) + stT326 245 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 244
    simpa using h
  have hprev := st326_p244
  have hstep := st326_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p246 : ((58136907761991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT326 (i+1))
      = (∑ i ∈ Finset.range 245, stT326 (i+1)) + stT326 246 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 245
    simpa using h
  have hprev := st326_p245
  have hstep := st326_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p247 : ((11733982792163/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT326 (i+1))
      = (∑ i ∈ Finset.range 246, stT326 (i+1)) + stT326 247 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 246
    simpa using h
  have hprev := st326_p246
  have hstep := st326_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p248 : ((11827790834163/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT326 (i+1))
      = (∑ i ∈ Finset.range 247, stT326 (i+1)) + stT326 248 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 247
    simpa using h
  have hprev := st326_p247
  have hstep := st326_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p249 : ((2942294243797/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT326 (i+1))
      = (∑ i ∈ Finset.range 248, stT326 (i+1)) + stT326 249 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 248
    simpa using h
  have hprev := st326_p248
  have hstep := st326_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_p250 : ((14557032262687/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT326 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT326 (i+1))
      = (∑ i ∈ Finset.range 249, stT326 (i+1)) + stT326 250 := by
    have h := Finset.sum_range_succ (fun i => stT326 (i+1)) 249
    simpa using h
  have hprev := st326_p249
  have hstep := st326_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st326_s250 :
    |Real.sin (((326 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))
      - ((-107403/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -7312749/10000000) (δ := 16441/1000000000) (ψ := -176407/500000) 326 287
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 326`** (evaluated boundary). -/
theorem station_326_sign : hardyG ((((326:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 326 250 (by norm_num) (by norm_num)
    ((-176407/500000 : ℚ) : ℝ)
  have hchain := st326_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT326 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((326 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-176407/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st326_c250
  have hsinb := abs_le.mp st326_s250
  have hbdy_lo : ((17830787244679/1700420000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((326 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-176407/500000 : ℚ) : ℝ))) / 2
          - ((((326:ℕ)):ℝ))
            * Real.sin (((326 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-176407/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((326:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((326:ℝ) * Real.log (250:ℝ) - ((-176407/500000 : ℚ) : ℝ))) / 2
        - ((326:ℝ)) * Real.sin ((326:ℝ) * Real.log (250:ℝ) - ((-176407/500000 : ℚ) : ℝ))
        ≥ ((140964869/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((326:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((140964869/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((140964869/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((140964869/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((326:ℕ)):ℝ))+1) * (((((326:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((180183314949/78125000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((14557032262687/2500000000000 : ℚ) : ℝ) + ((17830787244679/1700420000000000 : ℚ) : ℝ)
      - ((180183314949/78125000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-176407/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((326:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-176407/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((326:ℕ)):ℝ)))).re
      - Real.sin ((-176407/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((326:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((326:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((326:ℕ)):ℝ))
      = (((((326:ℕ)):ℝ)) * (Real.log ((((326:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((326:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_326
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
  have hθwin : |(((-176407/500000 : ℚ) : ℝ) + ((77:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((326:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((326:ℕ)):ℝ)))
    (φ := ((-176407/500000 : ℚ) : ℝ) + ((77:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-176407/500000 : ℚ) : ℝ) + ((77:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-176407/500000 : ℚ)) : ℝ) - Real.pi) + ((77:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-176407/500000 : ℚ)) : ℝ) - Real.pi) 77).1,
    (cos_sin_shift ((((-176407/500000 : ℚ)) : ℝ) - Real.pi) 77).2]
  exact cos_sin_flip ((-176407/500000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_326_sign
end AxiomAudit
