import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 217` (rung-217.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT217 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((217 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-515201/500000 : ℚ) : ℝ))

theorem st217_c1 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((257237/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 515201/2000000) (δ := 1/1000000000) (ψ := -515201/500000) 217 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t1 : ((64303/125000 : ℚ) : ℝ) ≤ stT217 1 := by
  have hc : ((64303/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64303/125000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((64303/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c2 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((199491/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 323443/2000000) (δ := 11029/1000000000) (ψ := -515201/500000) 217 24
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t2 : ((2821051677119/5000000000000 : ℚ) : ℝ) ≤ stT217 2 := by
  have hc : ((398957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2821051677119/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((398957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c3 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((784927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 835273/5000000) (δ := 11029/1000000000) (ψ := -515201/500000) 217 38
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t3 : ((2265744464627/5000000000000 : ℚ) : ℝ) ≤ stT217 3 := by
  have hc : ((784877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2265744464627/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((784877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c4 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((193103/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 658453/10000000) (δ := 10857/1000000000) (ψ := -515201/500000) 217 48
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t4 : ((193093/400000 : ℚ) : ℝ) ≤ stT217 4 := by
  have hc : ((193093/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193093/400000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((193093/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c5 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-1143/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -78997/200000) (δ := 1363/125000000) (ψ := -515201/500000) 217 56
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t5 : ((-2569801149/625000000000 : ℚ) : ℝ) ≤ stT217 5 := by
  have hc : ((-4597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2569801149/625000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-4597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c6 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((479871/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 88973/1250000) (δ := 1357/125000000) (ψ := -515201/500000) 217 62
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t6 : ((489740664443/1250000000000 : ℚ) : ℝ) ≤ stT217 6 := by
  have hc : ((239923/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((489740664443/1250000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((239923/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c7 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-680681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2899361/5000000) (δ := 551/50000000) (ψ := -515201/500000) 217 67
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t7 : ((-514584304099/2000000000000 : ℚ) : ℝ) ≤ stT217 7 := by
  have hc : ((-680731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-514584304099/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-680731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c8 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((496397/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -300309/10000000) (δ := 5509/500000000) (ψ := -515201/500000) 217 72
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t8 : ((438734896569/1250000000000 : ℚ) : ℝ) ≤ stT217 8 := by
  have hc : ((124093/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((438734896569/1250000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((124093/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c9 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((238383/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 153023/2000000) (δ := 1357/125000000) (ψ := -515201/500000) 217 76
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t9 : ((1589136507753/5000000000000 : ℚ) : ℝ) ≤ stT217 9 := by
  have hc : ((476741/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1589136507753/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((476741/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c10 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-382657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4908667/10000000) (δ := 10927/1000000000) (ψ := -515201/500000) 217 80
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t10 : ((-605112963273/5000000000000 : ℚ) : ℝ) ≤ stT217 10 := by
  have hc : ((-382707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-605112963273/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-382707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c11 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((99147/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -326773/10000000) (δ := 10897/1000000000) (ψ := -515201/500000) 217 83
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t11 : ((149462166523/500000000000 : ℚ) : ℝ) ≤ stT217 11 := by
  have hc : ((49571/50000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149462166523/500000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((49571/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c12 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((248781/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -123489/5000000) (δ := 11019/1000000000) (ψ := -515201/500000) 217 86
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t12 : ((1436265432287/5000000000000 : ℚ) : ℝ) ≤ stT217 12 := by
  have hc : ((497537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1436265432287/5000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((497537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c13 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-1657/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3947703/10000000) (δ := 69/6250000) (ψ := -515201/500000) 217 89
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t13 : ((-4623426167/2000000000000 : ℚ) : ℝ) ≤ stT217 13 := by
  have hc : ((-1667/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4623426167/2000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-1667/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c14 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-2857/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 120999/250000) (δ := 2171/200000000) (ψ := -515201/500000) 217 91
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t14 : ((-38183621931/400000000000 : ℚ) : ℝ) ≤ stT217 14 := by
  have hc : ((-14287/40000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38183621931/400000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-14287/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c15 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-362843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2427641/5000000) (δ := 11027/1000000000) (ψ := -515201/500000) 217 94
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t15 : ((-936985734177/10000000000000 : ℚ) : ℝ) ≤ stT217 15 := by
  have hc : ((-362893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-936985734177/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-362893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c16 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((875837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19673/156250) (δ := 341/31250000) (ψ := -515201/500000) 217 96
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t16 : ((875787/4000000 : ℚ) : ℝ) ≤ stT217 16 := by
  have hc : ((875787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((875787/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((875787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c17 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((124543/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 213847/10000000) (δ := 5449/500000000) (ψ := -515201/500000) 217 98
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t17 : ((302045953833/1250000000000 : ℚ) : ℝ) ≤ stT217 17 := by
  have hc : ((498147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((302045953833/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((498147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c18 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((498501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -193647/10000000) (δ := 11019/1000000000) (ψ := -515201/500000) 217 100
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t18 : ((146864862309/625000000000 : ℚ) : ℝ) ≤ stT217 18 := by
  have hc : ((124619/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146864862309/625000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((124619/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c19 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((612761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1139059/5000000) (δ := 10869/1000000000) (ψ := -515201/500000) 217 102
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t19 : ((1405655229627/10000000000000 : ℚ) : ℝ) ≤ stT217 19 := by
  have hc : ((612711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1405655229627/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((612711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c20 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-140111/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5867429/10000000) (δ := 2737/250000000) (ψ := -515201/500000) 217 104
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t20 : ((-78330021057/500000000000 : ℚ) : ℝ) ≤ stT217 20 := by
  have hc : ((-140121/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78330021057/500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-140121/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c21 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-47121/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4893291/10000000) (δ := 2171/200000000) (ψ := -515201/500000) 217 105
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t21 : ((-411360381111/5000000000000 : ℚ) : ℝ) ≤ stT217 21 := by
  have hc : ((-188509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-411360381111/5000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-188509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c22 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((870679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40173/312500) (δ := 11033/1000000000) (ψ := -515201/500000) 217 107
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t22 : ((1856187122403/10000000000000 : ℚ) : ℝ) ≤ stT217 22 := by
  have hc : ((870629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1856187122403/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((870629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c23 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-239349/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7121603/10000000) (δ := 10977/1000000000) (ψ := -515201/500000) 217 108
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t23 : ((-199641373967/1000000000000 : ℚ) : ℝ) ≤ stT217 23 := by
  have hc : ((-478723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199641373967/1000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-478723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c24 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((221483/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1205741/10000000) (δ := 341/31250000) (ψ := -515201/500000) 217 110
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t24 : ((904149329781/5000000000000 : ℚ) : ℝ) ≤ stT217 24 := by
  have hc : ((442941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((904149329781/5000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((442941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c25 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-249349/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5232231/10000000) (δ := 5449/500000000) (ψ := -515201/500000) 217 111
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t25 : ((-249374124687/2500000000000 : ℚ) : ℝ) ≤ stT217 25 := by
  have hc : ((-124687/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-249374124687/2500000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-124687/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c26 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-381843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2453233/5000000) (δ := 1089/100000000) (ψ := -515201/500000) 217 113
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t26 : ((-374477019833/5000000000000 : ℚ) : ℝ) ≤ stT217 26 := by
  have hc : ((-381893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-374477019833/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-381893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c27 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((39937/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35079/2500000) (δ := 551/50000000) (ψ := -515201/500000) 217 114
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t27 : ((30741963/160000000 : ℚ) : ℝ) ≤ stT217 27 := by
  have hc : ((7987/8000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30741963/160000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((7987/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c28 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((4579/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1940599/5000000) (δ := 11027/1000000000) (ψ := -515201/500000) 217 115
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t28 : ((8629872163/2500000000000 : ℚ) : ℝ) ≤ stT217 28 := by
  have hc : ((9133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8629872163/2500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((9133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c29 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-967033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1442053/2000000) (δ := 5517/500000000) (ψ := -515201/500000) 217 116
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t29 : ((-897914322591/5000000000000 : ℚ) : ℝ) ≤ stT217 29 := by
  have hc : ((-967083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-897914322591/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-967083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c30 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-342587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2907049/5000000) (δ := 10949/1000000000) (ψ := -515201/500000) 217 118
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t30 : ((-78190139763/625000000000 : ℚ) : ℝ) ≤ stT217 30 := by
  have hc : ((-85653/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78190139763/625000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-85653/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c31 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((77303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3733541/10000000) (δ := 10947/1000000000) (ψ := -515201/500000) 217 119
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t31 : ((138750482409/10000000000000 : ℚ) : ℝ) ≤ stT217 31 := by
  have hc : ((77253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138750482409/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((77253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c32 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((631637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1108917/5000000) (δ := 10963/1000000000) (ψ := -515201/500000) 217 120
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t32 : ((558249012321/5000000000000 : ℚ) : ℝ) ≤ stT217 32 := by
  have hc : ((631587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((558249012321/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((631587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c33 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((880973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -246441/2000000) (δ := 11033/1000000000) (ψ := -515201/500000) 217 121
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t33 : ((191686202031/1250000000000 : ℚ) : ℝ) ≤ stT217 33 := by
  have hc : ((880923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191686202031/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((880923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c34 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((29873/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -148983/2000000) (δ := 10977/1000000000) (ψ := -515201/500000) 217 122
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t34 : ((163933015171/1000000000000 : ℚ) : ℝ) ≤ stT217 34 := by
  have hc : ((477943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163933015171/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((477943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c35 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((239499/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18179/250000) (δ := 5459/500000000) (ψ := -515201/500000) 217 123
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t35 : ((202402973421/1250000000000 : ℚ) : ℝ) ≤ stT217 35 := by
  have hc : ((478973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202402973421/1250000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((478973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c36 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((111953/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115241/1000000) (δ := 10911/1000000000) (ψ := -515201/500000) 217 124
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t36 : ((373155684071/2500000000000 : ℚ) : ℝ) ≤ stT217 36 := by
  have hc : ((447787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((373155684071/2500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((447787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c37 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((348867/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15597/78125) (δ := 2751/250000000) (ψ := -515201/500000) 217 125
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t37 : ((286746205369/2500000000000 : ℚ) : ℝ) ≤ stT217 37 := by
  have hc : ((174421/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((286746205369/2500000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((174421/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c38 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((34069/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40461/125000) (δ := 5503/500000000) (ψ := -515201/500000) 217 126
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t38 : ((110514139857/2500000000000 : ℚ) : ℝ) ≤ stT217 38 := by
  have hc : ((136251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110514139857/2500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((136251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c39 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-181021/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -970627/2000000) (δ := 1089/100000000) (ψ := -515201/500000) 217 127
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t39 : ((-72476425243/1250000000000 : ℚ) : ℝ) ≤ stT217 39 := by
  have hc : ((-90523/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72476425243/1250000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-90523/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c40 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-36667/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -426637/625000) (δ := 10983/1000000000) (ψ := -515201/500000) 217 128
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t40 : ((-57978785991/400000000000 : ℚ) : ℝ) ≤ stT217 40 := by
  have hc : ((-36669/40000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57978785991/400000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-36669/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c41 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-174179/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 821193/1250000) (δ := 273/25000000) (ψ := -515201/500000) 217 128
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t41 : ((-136018790241/1000000000000 : ℚ) : ℝ) ≤ stT217 41 := by
  have hc : ((-174189/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136018790241/1000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-174189/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c42 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-603/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3934529/10000000) (δ := 2757/250000000) (ψ := -515201/500000) 217 129
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t42 : ((-472939921/1000000000000 : ℚ) : ℝ) ≤ stT217 42 := by
  have hc : ((-613/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-472939921/1000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-613/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c43 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((230581/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 495931/5000000) (δ := 2207/200000000) (ψ := -515201/500000) 217 130
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t43 : ((140645401589/1000000000000 : ℚ) : ℝ) ≤ stT217 43 := by
  have hc : ((461137/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140645401589/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((461137/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c44 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((124679/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1122149/5000000) (δ := 10861/1000000000) (ψ := -515201/500000) 217 131
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t44 : ((46986374741/500000000000 : ℚ) : ℝ) ≤ stT217 44 := by
  have hc : ((124669/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46986374741/500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((124669/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c45 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-669481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5760767/10000000) (δ := 10949/1000000000) (ψ := -515201/500000) 217 132
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t45 : ((-124759737009/1250000000000 : ℚ) : ℝ) ≤ stT217 45 := by
  have hc : ((-669531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124759737009/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-669531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c46 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-389891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3081393/5000000) (δ := 5427/500000000) (ψ := -515201/500000) 217 132
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t46 : ((-7186249359/62500000000 : ℚ) : ℝ) ≤ stT217 46 := by
  have hc : ((-97479/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7186249359/62500000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-97479/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c47 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((660887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 212199/1000000) (δ := 11047/1000000000) (ψ := -515201/500000) 217 133
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t47 : ((963929229213/10000000000000 : ℚ) : ℝ) ≤ stT217 47 := by
  have hc : ((660837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((963929229213/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((660837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c48 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((64803/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2164503/10000000) (δ := 2741/250000000) (ψ := -515201/500000) 217 134
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t48 : ((374111253/4000000000 : ℚ) : ℝ) ≤ stT217 48 := by
  have hc : ((32399/50000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((374111253/4000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((32399/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c49 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-178587/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6686551/10000000) (δ := 1379/125000000) (ψ := -515201/500000) 217 135
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t49 : ((-63784668371/500000000000 : ℚ) : ℝ) ≤ stT217 49 := by
  have hc : ((-178597/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63784668371/500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-178597/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c50 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-34537/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1068367/2500000) (δ := 1379/125000000) (ψ := -515201/500000) 217 135
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t50 : ((-48860386593/2500000000000 : ℚ) : ℝ) ≤ stT217 50 := by
  have hc : ((-69099/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48860386593/2500000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-69099/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c51 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((48099/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5403/78125) (δ := 5489/500000000) (ψ := -515201/500000) 217 136
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t51 : ((3367428351/25000000000 : ℚ) : ℝ) ≤ stT217 51 := by
  have hc : ((96193/100000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3367428351/25000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((96193/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c52 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-699927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1466307/2500000) (δ := 2197/200000000) (ψ := -515201/500000) 217 137
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t52 : ((-970693804727/10000000000000 : ℚ) : ℝ) ≤ stT217 52 := by
  have hc : ((-699977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-970693804727/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-699977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c53 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-214883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 223421/500000) (δ := 5459/500000000) (ψ := -515201/500000) 217 137
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t53 : ((-147616629199/5000000000000 : ℚ) : ℝ) ≤ stT217 53 := by
  have hc : ((-214933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147616629199/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-214933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c54 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((904909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1099079/10000000) (δ := 10911/1000000000) (ψ := -515201/500000) 217 138
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t54 : ((1231356558393/10000000000000 : ℚ) : ℝ) ≤ stT217 54 := by
  have hc : ((904859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1231356558393/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((904859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c55 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-460427/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1370531/2000000) (δ := 10999/1000000000) (ψ := -515201/500000) 217 139
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t55 : ((-388045923/3125000000 : ℚ) : ℝ) ≤ stT217 55 := by
  have hc : ((-115113/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-388045923/3125000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-115113/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c56 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((97779/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2922381/10000000) (δ := 10899/1000000000) (ψ := -515201/500000) 217 139
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t56 : ((130645960549/2500000000000 : ℚ) : ℝ) ≤ stT217 56 := by
  have hc : ((195533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130645960549/2500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((195533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c57 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((293013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3183549/10000000) (δ := 11007/1000000000) (ψ := -515201/500000) 217 140
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t57 : ((97009717079/2500000000000 : ℚ) : ℝ) ≤ stT217 57 := by
  have hc : ((292963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97009717079/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((292963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c58 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-801503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3125751/5000000) (δ := 681/62500000) (ψ := -515201/500000) 217 140
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t58 : ((-210498237989/2000000000000 : ℚ) : ℝ) ≤ stT217 58 := by
  have hc : ((-801553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-210498237989/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-801553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c59 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((997329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -182749/10000000) (δ := 5457/500000000) (ψ := -515201/500000) 217 141
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t59 : ((1298346560031/10000000000000 : ℚ) : ℝ) ≤ stT217 59 := by
  have hc : ((997279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1298346560031/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((997279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c60 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-453971/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6772861/10000000) (δ := 5491/500000000) (ψ := -515201/500000) 217 142
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t60 : ((-29305328301/250000000000 : ℚ) : ℝ) ≤ stT217 60 := by
  have hc : ((-113499/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29305328301/250000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-113499/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c61 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((638911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 438857/2000000) (δ := 11021/1000000000) (ψ := -515201/500000) 217 142
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t61 : ((51123573803/625000000000 : ℚ) : ℝ) ≤ stT217 61 := by
  have hc : ((638861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51123573803/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((638861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c62 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-301387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4692357/10000000) (δ := 2757/250000000) (ψ := -515201/500000) 217 143
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t62 : ((-191412796437/5000000000000 : ℚ) : ℝ) ≤ stT217 62 := by
  have hc : ((-301437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191412796437/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-301437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c63 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-4869/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 199393/500000) (δ := 2757/250000000) (ψ := -515201/500000) 217 143
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t63 : ((-3073482139/1000000000000 : ℚ) : ℝ) ≤ stT217 63 := by
  have hc : ((-4879/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3073482139/1000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-4879/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c64 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((5913/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3176651/10000000) (δ := 2717/250000000) (ψ := -515201/500000) 217 144
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t64 : ((739/20000 : ℚ) : ℝ) ≤ stT217 64 := by
  have hc : ((739/2500 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((739/20000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((739/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c65 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-249721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2617189/5000000) (δ := 2207/200000000) (ψ := -515201/500000) 217 144
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t65 : ((-38721493951/625000000000 : ℚ) : ℝ) ≤ stT217 65 := by
  have hc : ((-124873/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38721493951/625000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-124873/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c66 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((159983/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2190967/10000000) (δ := 543/50000000) (ψ := -515201/500000) 217 145
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t66 : ((196909928037/2500000000000 : ℚ) : ℝ) ≤ stT217 66 := by
  have hc : ((319941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196909928037/2500000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((319941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c67 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-728439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2983547/5000000) (δ := 10943/1000000000) (ψ := -515201/500000) 217 145
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t67 : ((-177998273771/2000000000000 : ℚ) : ℝ) ≤ stT217 67 := by
  have hc : ((-728489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177998273771/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-728489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c68 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((776647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -851839/5000000) (δ := 10953/1000000000) (ψ := -515201/500000) 217 146
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t68 : ((470881048383/5000000000000 : ℚ) : ℝ) ≤ stT217 68 := by
  have hc : ((776597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((470881048383/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((776597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c69 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-198243/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6216171/10000000) (δ := 10953/1000000000) (ψ := -515201/500000) 217 146
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t69 : ((-477343335949/5000000000000 : ℚ) : ℝ) ≤ stT217 69 := by
  have hc : ((-396511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-477343335949/5000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-396511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c70 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((781101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -842961/5000000) (δ := 10957/1000000000) (ψ := -515201/500000) 217 147
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t70 : ((233383506157/2500000000000 : ℚ) : ℝ) ≤ stT217 70 := by
  have hc : ((781051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233383506157/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((781051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c71 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-739881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6009223/10000000) (δ := 5473/500000000) (ψ := -515201/500000) 217 147
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t71 : ((-439068396021/5000000000000 : ℚ) : ℝ) ≤ stT217 71 := by
  have hc : ((-739931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-439068396021/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-739931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c72 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((664129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -527793/2500000) (δ := 2741/250000000) (ψ := -515201/500000) 217 148
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t72 : ((782624406369/10000000000000 : ℚ) : ℝ) ≤ stT217 72 := by
  have hc : ((664079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((782624406369/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((664079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c73 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-437/800 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5371693/10000000) (δ := 679/62500000) (ψ := -515201/500000) 217 148
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t73 : ((-1598490189/25000000000 : ℚ) : ℝ) ≤ stT217 73 := by
  have hc : ((-5463/10000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1598490189/25000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-5463/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c74 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((378989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -92351/312500) (δ := 10971/1000000000) (ψ := -515201/500000) 217 149
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t74 : ((110126873241/2500000000000 : ℚ) : ℝ) ≤ stT217 74 := by
  have hc : ((378939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110126873241/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((378939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c75 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-79621/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4326799/10000000) (δ := 1379/125000000) (ψ := -515201/500000) 217 149
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t75 : ((-45983657923/2500000000000 : ℚ) : ℝ) ≤ stT217 75 := by
  have hc : ((-39823/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45983657923/2500000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-39823/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c76 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-53627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4195643/10000000) (δ := 437/40000000) (ψ := -515201/500000) 217 150
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t76 : ((-15385770627/1250000000000 : ℚ) : ℝ) ≤ stT217 76 := by
  have hc : ((-13413/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15385770627/1250000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-13413/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c77 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((400817/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2895971/10000000) (δ := 441/40000000) (ψ := -515201/500000) 217 150
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t77 : ((91343215407/2000000000000 : ℚ) : ℝ) ≤ stT217 77 := by
  have hc : ((400767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91343215407/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((400767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c78 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-684533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5811897/10000000) (δ := 5493/500000000) (ψ := -515201/500000) 217 151
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t78 : ((-387569135037/5000000000000 : ℚ) : ℝ) ≤ stT217 78 := by
  have hc : ((-684583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-387569135037/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-684583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c79 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((22623/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109901/1000000) (δ := 10917/1000000000) (ψ := -515201/500000) 217 151
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t79 : ((101805747369/1000000000000 : ℚ) : ℝ) ≤ stT217 79 := by
  have hc : ((90487/100000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101805747369/1000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((90487/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c80 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-999619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3892477/5000000) (δ := 10893/1000000000) (ψ := -515201/500000) 217 152
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t80 : ((-558831965373/5000000000000 : ℚ) : ℝ) ≤ stT217 80 := by
  have hc : ((-999669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-558831965373/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-999669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c81 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((913781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -261437/2500000) (δ := 1091/100000000) (ψ := -515201/500000) 217 152
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t81 : ((1015256565141/10000000000000 : ℚ) : ℝ) ≤ stT217 81 := by
  have hc : ((913731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1015256565141/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((913731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c82 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-311869/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5610781/10000000) (δ := 1101/100000000) (ψ := -515201/500000) 217 152
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t82 : ((-43053691813/625000000000 : ℚ) : ℝ) ≤ stT217 82 := by
  have hc : ((-155947/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43053691813/625000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-155947/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c83 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((40389/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1760661/5000000) (δ := 11/1000000) (ψ := -515201/500000) 217 153
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t83 : ((44318942213/2500000000000 : ℚ) : ℝ) ≤ stT217 83 := by
  have hc : ((80753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44318942213/2500000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((80753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c84 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((74277/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2975739/10000000) (δ := 21703/1000000000) (ψ := -515201/500000) 217 153
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t84 : ((81031906763/2000000000000 : ℚ) : ℝ) ≤ stT217 84 := by
  have hc : ((74267/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81031906763/2000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((74267/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c85 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-407873/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1262407/2000000) (δ := 10907/1000000000) (ψ := -515201/500000) 217 154
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t85 : ((-221213894697/2500000000000 : ℚ) : ℝ) ≤ stT217 85 := by
  have hc : ((-203949/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221213894697/2500000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-203949/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c86 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((999913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6609/2000000) (δ := 10907/1000000000) (ψ := -515201/500000) 217 154
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t86 : ((1078179269201/10000000000000 : ℚ) : ℝ) ≤ stT217 86 := by
  have hc : ((999863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1078179269201/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((999863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c87 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-203519/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6304833/10000000) (δ := 681/62500000) (ψ := -515201/500000) 217 154
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t87 : ((-436417534119/5000000000000 : ℚ) : ℝ) ≤ stT217 87 := by
  have hc : ((-407063/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-436417534119/5000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-407063/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c88 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((142771/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -160153/500000) (δ := 5507/500000000) (ψ := -515201/500000) 217 155
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t88 : ((76083832119/2500000000000 : ℚ) : ℝ) ≤ stT217 88 := by
  have hc : ((71373/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76083832119/2500000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((71373/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c89 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((77889/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1463459/5000000) (δ := 10989/1000000000) (ψ := -515201/500000) 217 155
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t89 : ((82551506363/2000000000000 : ℚ) : ℝ) ≤ stT217 89 := by
  have hc : ((77879/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82551506363/2000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((77879/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c90 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-224699/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -671953/1000000) (δ := 10981/1000000000) (ψ := -515201/500000) 217 156
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t90 : ((-473733638339/5000000000000 : ℚ) : ℝ) ≤ stT217 90 := by
  have hc : ((-449423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-473733638339/5000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-449423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c91 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((191649/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -362493/5000000) (δ := 10861/500000000) (ψ := -515201/500000) 217 156
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t91 : ((50223024369/500000000000 : ℚ) : ℝ) ≤ stT217 91 := by
  have hc : ((191639/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50223024369/500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((191639/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c92 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-488887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 650503/1250000) (δ := 5511/500000000) (ψ := -515201/500000) 217 156
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t92 : ((-509752514901/10000000000000 : ℚ) : ℝ) ≤ stT217 92 := by
  have hc : ((-488937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-509752514901/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-488937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c93 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-280979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2319513/5000000) (δ := 11029/1000000000) (ψ := -515201/500000) 217 157
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t93 : ((-36426697951/1250000000000 : ℚ) : ℝ) ≤ stT217 93 := by
  have hc : ((-281029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36426697951/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-281029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c94 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((893701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 581587/5000000) (δ := 10929/1000000000) (ψ := -515201/500000) 217 157
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t94 : ((921730408071/10000000000000 : ℚ) : ℝ) ≤ stT217 94 := by
  have hc : ((893651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((921730408071/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((893651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c95 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-464331/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6903963/10000000) (δ := 5437/500000000) (ψ := -515201/500000) 217 157
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t95 : ((-119104876131/1250000000000 : ℚ) : ℝ) ≤ stT217 95 := by
  have hc : ((-116089/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119104876131/1250000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-116089/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c96 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((7899/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -78083/250000) (δ := 10867/1000000000) (ψ := -515201/500000) 217 158
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t96 : ((1612120321/50000000000 : ℚ) : ℝ) ≤ stT217 96 := by
  have hc : ((31591/100000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1612120321/50000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((31591/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c97 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((540807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2498499/10000000) (δ := 10867/1000000000) (ψ := -515201/500000) 217 158
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t97 : ((274527728461/5000000000000 : ℚ) : ℝ) ≤ stT217 97 := by
  have hc : ((540757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274527728461/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((540757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c98 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-996519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7645313/10000000) (δ := 543/50000000) (ψ := -515201/500000) 217 159
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t98 : ((-1006687165057/10000000000000 : ℚ) : ℝ) ≤ stT217 98 := by
  have hc : ((-996569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1006687165057/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-996569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c99 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((656177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -534409/2500000) (δ := 543/50000000) (ψ := -515201/500000) 217 159
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t99 : ((659431911699/10000000000000 : ℚ) : ℝ) ≤ stT217 99 := by
  have hc : ((656127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((659431911699/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((656127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c100 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((121247/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 828663/2500000) (δ := 10943/1000000000) (ψ := -515201/500000) 217 159
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t100 : ((60610939389/2500000000000 : ℚ) : ℝ) ≤ stT217 100 := by
  have hc : ((60611/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60610939389/2500000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((60611/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c101 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-47079/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6995219/10000000) (δ := 221/20000000) (ψ := -515201/500000) 217 160
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t101 : ((-46847881597/500000000000 : ℚ) : ℝ) ≤ stT217 101 := by
  have hc : ((-94163/100000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46847881597/500000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-94163/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c102 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((789907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1650347/10000000) (δ := 10953/1000000000) (ψ := -515201/500000) 217 160
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t102 : ((782074538979/10000000000000 : ℚ) : ℝ) ≤ stT217 102 := by
  have hc : ((789857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((782074538979/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((789857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c103 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((22723/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1821169/5000000) (δ := 221/20000000) (ψ := -515201/500000) 217 160
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t103 : ((22379777577/2000000000000 : ℚ) : ℝ) ≤ stT217 103 := by
  have hc : ((22713/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22379777577/2000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((22713/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c104 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-229083/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1364809/2000000) (δ := 10857/1000000000) (ψ := -515201/500000) 217 161
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t104 : ((-449293388971/5000000000000 : ℚ) : ℝ) ≤ stT217 104 := by
  have hc : ((-458191/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-449293388971/5000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-458191/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c105 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((794243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1632591/10000000) (δ := 10957/1000000000) (ψ := -515201/500000) 217 161
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t105 : ((7750529487/100000000000 : ℚ) : ℝ) ≤ stT217 105 := by
  have hc : ((794193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7750529487/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((794193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c106 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((166181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3509603/10000000) (δ := 5523/500000000) (ψ := -515201/500000) 217 161
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t106 : ((32272109667/2000000000000 : ℚ) : ℝ) ≤ stT217 106 := by
  have hc : ((166131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32272109667/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((166131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c107 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-191077/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7104393/10000000) (δ := 2193/200000000) (ψ := -515201/500000) 217 162
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t107 : ((-184730873119/2000000000000 : ℚ) : ℝ) ≤ stT217 107 := by
  have hc : ((-191087/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184730873119/2000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-191087/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c108 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((27197/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2057841/10000000) (δ := 2193/200000000) (ψ := -515201/500000) 217 162
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t108 : ((20934711/320000000 : ℚ) : ℝ) ≤ stT217 108 := by
  have hc : ((5439/8000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20934711/320000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((5439/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c109 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((383821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 735541/2500000) (δ := 5469/500000000) (ψ := -515201/500000) 217 162
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t109 : ((183792920923/5000000000000 : ℚ) : ℝ) ≤ stT217 109 := by
  have hc : ((383771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183792920923/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((383771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c110 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-199971/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3905709/5000000) (δ := 10931/1000000000) (ψ := -515201/500000) 217 163
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t110 : ((-190674484203/2000000000000 : ℚ) : ℝ) ≤ stT217 110 := by
  have hc : ((-199981/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190674484203/2000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-199981/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c111 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((199331/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2901847/10000000) (δ := 1359/125000000) (ψ := -515201/500000) 217 163
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t111 : ((94586342521/2500000000000 : ℚ) : ℝ) ≤ stT217 111 := by
  have hc : ((99653/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94586342521/2500000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((99653/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c112 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((11048/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 981809/5000000) (δ := 11031/1000000000) (ψ := -515201/500000) 217 163
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t112 : ((334036432521/5000000000000 : ℚ) : ℝ) ≤ stT217 112 := by
  have hc : ((353511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334036432521/5000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((353511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c113 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-227529/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6785901/10000000) (δ := 1359/125000000) (ψ := -515201/500000) 217 163
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t113 : ((-428106134843/5000000000000 : ℚ) : ℝ) ≤ stT217 113 := by
  have hc : ((-455083/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-428106134843/5000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-455083/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c114 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-43011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -517789/1250000) (δ := 2731/250000000) (ψ := -515201/500000) 217 164
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t114 : ((-5038364387/625000000000 : ℚ) : ℝ) ≤ stT217 114 := by
  have hc : ((-10759/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5038364387/625000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-10759/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c115 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((971743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14893/250000) (δ := 689/62500000) (ψ := -515201/500000) 217 164
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t115 : ((113263451159/1250000000000 : ℚ) : ℝ) ≤ stT217 115 := by
  have hc : ((971693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113263451159/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((971693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c116 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-51951/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1058537/2000000) (δ := 689/62500000) (ψ := -515201/500000) 217 164
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t116 : ((-12059987753/250000000000 : ℚ) : ℝ) ≤ stT217 116 := by
  have hc : ((-12989/25000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12059987753/250000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-12989/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c117 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-668827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2879283/5000000) (δ := 5493/500000000) (ψ := -515201/500000) 217 165
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t117 : ((-618377455377/10000000000000 : ℚ) : ℝ) ≤ stT217 117 := by
  have hc : ((-668877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-618377455377/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-668877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c118 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((179511/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -142689/1250000) (δ := 11017/1000000000) (ψ := -515201/500000) 217 165
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t118 : ((82621976787/1000000000000 : ℚ) : ℝ) ≤ stT217 118 := by
  have hc : ((179501/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82621976787/1000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((179501/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c119 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((97463/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3436537/10000000) (δ := 11017/1000000000) (ψ := -515201/500000) 217 165
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t119 : ((22330304931/1250000000000 : ℚ) : ℝ) ≤ stT217 119 := by
  have hc : ((48719/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22330304931/1250000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((48719/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c120 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-998803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7731623/10000000) (δ := 10893/1000000000) (ψ := -515201/500000) 217 166
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t120 : ((-911823936963/10000000000000 : ℚ) : ℝ) ≤ stT217 120 := by
  have hc : ((-998853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-911823936963/10000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-998853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c121 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((137691/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -807381/2500000) (δ := 10893/1000000000) (ψ := -515201/500000) 217 166
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t121 : ((6257539197/250000000000 : ℚ) : ℝ) ≤ stT217 121 := by
  have hc : ((68833/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6257539197/250000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((68833/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c122 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((110043/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 617761/5000000) (δ := 1091/100000000) (ψ := -515201/500000) 217 166
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t122 : ((398490167479/5000000000000 : ℚ) : ℝ) ≤ stT217 122 := by
  have hc : ((440147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((398490167479/5000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((440147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c123 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-640269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 354007/625000) (δ := 1101/100000000) (ψ := -515201/500000) 217 166
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t123 : ((-57735643273/1000000000000 : ℚ) : ℝ) ≤ stT217 123 := by
  have hc : ((-640319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57735643273/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-640319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c124 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-159067/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -70639/125000) (δ := 10903/1000000000) (ψ := -515201/500000) 217 167
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t124 : ((-285715372293/5000000000000 : ℚ) : ℝ) ≤ stT217 124 := by
  have hc : ((-318159/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285715372293/5000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-318159/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c125 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((434539/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1293651/10000000) (δ := 11/1000000) (ψ := -515201/500000) 217 167
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t125 : ((194320526739/2500000000000 : ℚ) : ℝ) ≤ stT217 125 := by
  have hc : ((217257/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194320526739/2500000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((217257/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c126 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((175743/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3029097/10000000) (δ := 10903/1000000000) (ψ := -515201/500000) 217 167
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t126 : ((7827094733/250000000000 : ℚ) : ℝ) ≤ stT217 126 := by
  have hc : ((87859/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7827094733/250000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((87859/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c127 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-977073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3658807/5000000) (δ := 109/10000000) (ψ := -515201/500000) 217 167
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t127 : ((-867056933911/10000000000000 : ℚ) : ℝ) ≤ stT217 127 := by
  have hc : ((-977123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-867056933911/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-977123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c128 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-10409/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4135413/10000000) (δ := 43/3906250) (ψ := -515201/500000) 217 168
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t128 : ((-9205872831/1250000000000 : ℚ) : ℝ) ≤ stT217 128 := by
  have hc : ((-41661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9205872831/1250000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-41661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c129 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((499701/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8643/1000000) (δ := 2179/200000000) (ψ := -515201/500000) 217 168
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t129 : ((2199698671/25000000000 : ℚ) : ℝ) ≤ stT217 129 := by
  have hc : ((124919/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2199698671/25000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((124919/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c130 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-69499/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 855123/2000000) (δ := 2179/200000000) (ψ := -515201/500000) 217 168
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t130 : ((-15244162479/1250000000000 : ℚ) : ℝ) ≤ stT217 130 := by
  have hc : ((-17381/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15244162479/1250000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-17381/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c131 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-973323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -291009/400000) (δ := 1361/125000000) (ψ := -515201/500000) 217 169
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t131 : ((-170088171393/2000000000000 : ℚ) : ℝ) ≤ stT217 131 := by
  have hc : ((-973373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170088171393/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-973373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c132 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((956/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3149729/10000000) (δ := 2203/200000000) (ψ := -515201/500000) 217 169
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t132 : ((6655639439/250000000000 : ℚ) : ℝ) ≤ stT217 132 := by
  have hc : ((30587/100000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6655639439/250000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((30587/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c133 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((46473/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 944627/10000000) (δ := 2203/200000000) (ψ := -515201/500000) 217 169
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t133 : ((80589977569/1000000000000 : ℚ) : ℝ) ≤ stT217 133 := by
  have hc : ((92941/100000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80589977569/1000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((92941/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c134 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-83833/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 313019/625000) (δ := 5447/250000000) (ψ := -515201/500000) 217 169
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t134 : ((-72429368567/2000000000000 : ℚ) : ℝ) ≤ stT217 134 := by
  have hc : ((-83843/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72429368567/2000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-83843/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c135 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-889241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6666199/10000000) (δ := 10981/1000000000) (ψ := -515201/500000) 217 170
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t135 : ((-765379859933/10000000000000 : ℚ) : ℝ) ≤ stT217 135 := by
  have hc : ((-889291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-765379859933/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-889291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c136 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((242253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1331247/5000000) (δ := 5511/500000000) (ψ := -515201/500000) 217 170
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t136 : ((12981785761/312500000000 : ℚ) : ℝ) ≤ stT217 136 := by
  have hc : ((60557/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12981785761/312500000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((60557/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c137 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((865441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 262383/2000000) (δ := 5461/500000000) (ψ := -515201/500000) 217 170
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t137 : ((739352858587/10000000000000 : ℚ) : ℝ) ≤ stT217 137 := by
  have hc : ((865391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((739352858587/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((865391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c138 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-507383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1051471/2000000) (δ := 5511/500000000) (ψ := -515201/500000) 217 170
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t138 : ((-431955893281/10000000000000 : ℚ) : ℝ) ≤ stT217 138 := by
  have hc : ((-507433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-431955893281/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-507433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c139 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-863739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1633399/2500000) (δ := 5437/500000000) (ψ := -515201/500000) 217 171
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t139 : ((-732656328121/10000000000000 : ℚ) : ℝ) ≤ stT217 139 := by
  have hc : ((-863789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-732656328121/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-863789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c140 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((245363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -528937/2000000) (δ := 5487/500000000) (ψ := -515201/500000) 217 171
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t140 : ((51837098013/1250000000000 : ℚ) : ℝ) ≤ stT217 140 := by
  have hc : ((122669/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51837098013/1250000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((122669/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c141 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((883927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 243301/2000000) (δ := 10929/1000000000) (ψ := -515201/500000) 217 171
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t141 : ((744357899427/10000000000000 : ℚ) : ℝ) ≤ stT217 141 := by
  have hc : ((883877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((744357899427/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((883877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c142 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-217207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5050461/10000000) (δ := 10929/1000000000) (ψ := -515201/500000) 217 171
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t142 : ((-5696787007/156250000000 : ℚ) : ℝ) ≤ stT217 142 := by
  have hc : ((-13577/31250 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5696787007/156250000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-13577/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c143 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-920511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3425227/5000000) (δ := 2759/250000000) (ψ := -515201/500000) 217 172
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t143 : ((-769812692323/10000000000000 : ℚ) : ℝ) ≤ stT217 143 := by
  have hc : ((-920561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-769812692323/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-920561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c144 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((168063/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3069989/10000000) (δ := 10867/1000000000) (ψ := -515201/500000) 217 172
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t144 : ((70015805327/2500000000000 : ℚ) : ℝ) ≤ stT217 144 := by
  have hc : ((84019/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70015805327/2500000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((84019/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c145 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((962763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 342191/5000000) (δ := 10967/1000000000) (ψ := -515201/500000) 217 172
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t145 : ((399744430851/5000000000000 : ℚ) : ℝ) ≤ stT217 145 := by
  have hc : ((962713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((399744430851/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((962713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c146 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-96577/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4412931/10000000) (δ := 2759/250000000) (ψ := -515201/500000) 217 172
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t146 : ((-19987098703/1250000000000 : ℚ) : ℝ) ≤ stT217 146 := by
  have hc : ((-48301/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19987098703/1250000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-48301/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c147 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-497257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3795991/5000000) (δ := 10859/1000000000) (ψ := -515201/500000) 217 173
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t147 : ((-205075864467/2500000000000 : ℚ) : ℝ) ≤ stT217 147 := by
  have hc : ((-248641/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205075864467/2500000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-248641/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c148 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((2599/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -782799/2000000) (δ := 10959/1000000000) (ψ := -515201/500000) 217 173
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t148 : ((528953139/1250000000000 : ℚ) : ℝ) ≤ stT217 148 := by
  have hc : ((1287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((528953139/1250000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((1287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c149 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((497283/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -52149/2000000) (δ := 2761/250000000) (ψ := -515201/500000) 217 173
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t149 : ((203684584299/2500000000000 : ℚ) : ℝ) ≤ stT217 149 := by
  have hc : ((248629/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203684584299/2500000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((248629/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c150 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((13859/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3367983/10000000) (δ := 171/15625000) (ψ := -515201/500000) 217 173
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t150 : ((5656633257/312500000000 : ℚ) : ℝ) ≤ stT217 150 := by
  have hc : ((110847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5656633257/312500000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((110847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c151 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-187701/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3486339/5000000) (δ := 10959/1000000000) (ψ := -515201/500000) 217 173
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t151 : ((-152757146979/2000000000000 : ℚ) : ℝ) ≤ stT217 151 := by
  have hc : ((-187711/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152757146979/2000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-187711/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c152 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-235739/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1030881/2000000) (δ := 10951/1000000000) (ψ := -515201/500000) 217 174
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t152 : ((-11951879157/312500000000 : ℚ) : ℝ) ≤ stT217 152 := by
  have hc : ((-58941/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11951879157/312500000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-58941/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c153 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((100351/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -199627/1250000) (δ := 1369/125000000) (ψ := -515201/500000) 217 174
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t153 : ((81123913827/1250000000000 : ℚ) : ℝ) ≤ stT217 153 := by
  have hc : ((401379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81123913827/1250000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((401379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c154 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((357251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1937209/10000000) (δ := 2713/250000000) (ψ := -515201/500000) 217 174
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t154 : ((71965142443/1250000000000 : ℚ) : ℝ) ≤ stT217 154 := by
  have hc : ((178613/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71965142443/1250000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((178613/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c155 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-71467/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 272427/500000) (δ := 1369/125000000) (ψ := -515201/500000) 217 174
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t155 : ((-11481748773/250000000000 : ℚ) : ℝ) ≤ stT217 155 := by
  have hc : ((-285893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11481748773/250000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-285893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c156 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-907573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -338533/500000) (δ := 2189/200000000) (ψ := -515201/500000) 217 175
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t156 : ((-726680186343/10000000000000 : ℚ) : ℝ) ≤ stT217 156 := by
  have hc : ((-907623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-726680186343/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-907623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c157 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((4931/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3304193/10000000) (δ := 5479/500000000) (ψ := -515201/500000) 217 175
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t157 : ((196728199/10000000000 : ℚ) : ℝ) ≤ stT217 157 := by
  have hc : ((493/2000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196728199/10000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((493/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c158 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((998427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 17531/1250000) (δ := 5479/500000000) (ψ := -515201/500000) 217 175
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t158 : ((794265810989/10000000000000 : ℚ) : ℝ) ≤ stT217 158 := by
  have hc : ((998377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((794265810989/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((998377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c159 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((145087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3562989/10000000) (δ := 5479/500000000) (ψ := -515201/500000) 217 175
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t159 : ((115021737887/10000000000000 : ℚ) : ℝ) ≤ stT217 159 := by
  have hc : ((145037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115021737887/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((145037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c160 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-187467/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6964247/10000000) (δ := 5479/500000000) (ψ := -515201/500000) 217 175
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t160 : ((-14821369189/200000000000 : ℚ) : ℝ) ≤ stT217 160 := by
  have hc : ((-187477/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14821369189/200000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-187477/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c161 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-543559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -536367/1000000) (δ := 2193/200000000) (ψ := -515201/500000) 217 176
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t161 : ((-428424232599/10000000000000 : ℚ) : ℝ) ≤ stT217 161 := by
  have hc : ((-543609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-428424232599/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-543609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c162 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((695411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -200451/1000000) (δ := 2193/200000000) (ψ := -515201/500000) 217 176
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t162 : ((273163529157/5000000000000 : ℚ) : ℝ) ≤ stT217 162 := by
  have hc : ((695361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((273163529157/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((695361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c163 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((430493/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66699/500000) (δ := 5519/500000000) (ψ := -515201/500000) 217 176
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t163 : ((4214604571/62500000000 : ℚ) : ℝ) ≤ stT217 163 := by
  have hc : ((107617/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4214604571/62500000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((107617/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c164 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-285963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4652019/10000000) (δ := 2173/200000000) (ψ := -515201/500000) 217 176
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t164 : ((-223338685297/10000000000000 : ℚ) : ℝ) ≤ stT217 164 := by
  have hc : ((-286013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223338685297/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-286013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c165 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-31227/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7758087/10000000) (δ := 10931/1000000000) (ψ := -515201/500000) 217 177
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t165 : ((-388982474843/5000000000000 : ℚ) : ℝ) ≤ stT217 165 := by
  have hc : ((-499657/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-388982474843/5000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-499657/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c166 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-109729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4480139/10000000) (δ := 1359/125000000) (ψ := -515201/500000) 217 177
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t166 : ((-42592838427/2500000000000 : ℚ) : ℝ) ≤ stT217 166 := by
  have hc : ((-54877/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42592838427/2500000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-54877/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c167 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((882929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -122183/1000000) (δ := 10931/1000000000) (ψ := -515201/500000) 217 177
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t167 : ((683192076417/10000000000000 : ℚ) : ℝ) ≤ stT217 167 := by
  have hc : ((882879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((683192076417/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((882879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c168 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((691827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2016949/10000000) (δ := 11031/1000000000) (ψ := -515201/500000) 217 177
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t168 : ((133429255983/2500000000000 : ℚ) : ℝ) ≤ stT217 168 := by
  have hc : ((691777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133429255983/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((691777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c169 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-125051/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2618289/5000000) (δ := 11031/1000000000) (ψ := -515201/500000) 217 177
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t169 : ((-192405442337/5000000000000 : ℚ) : ℝ) ≤ stT217 169 := by
  have hc : ((-250127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192405442337/5000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-250127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c170 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-194583/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3635399/5000000) (δ := 689/62500000) (ψ := -515201/500000) 217 178
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t170 : ((-29849204049/400000000000 : ℚ) : ℝ) ≤ stT217 170 := by
  have hc : ((-194593/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29849204049/400000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-194593/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c171 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-64751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4088981/10000000) (δ := 2731/250000000) (ψ := -515201/500000) 217 178
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t171 : ((-619432759/125000000000 : ℚ) : ℝ) ≤ stT217 171 := by
  have hc : ((-64801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-619432759/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-64801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c172 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((932223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -462859/5000000) (δ := 689/62500000) (ψ := -515201/500000) 217 178
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t172 : ((177693613779/2500000000000 : ℚ) : ℝ) ≤ stT217 172 := by
  have hc : ((932173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177693613779/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((932173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c173 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((63121/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2219209/10000000) (δ := 2731/250000000) (ψ := -515201/500000) 217 178
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t173 : ((2399307403/50000000000 : ℚ) : ℝ) ≤ stT217 173 := by
  have hc : ((15779/25000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2399307403/50000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((15779/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c174 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-268809/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 167063/312500) (δ := 689/62500000) (ψ := -515201/500000) 217 178
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t174 : ((-101901393283/2500000000000 : ℚ) : ℝ) ≤ stT217 174 := by
  have hc : ((-134417/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101901393283/2500000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-134417/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c175 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-971249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3626521/5000000) (δ := 10887/1000000000) (ψ := -515201/500000) 217 179
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t175 : ((-734233081771/10000000000000 : ℚ) : ℝ) ≤ stT217 175 := by
  have hc : ((-971299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-734233081771/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-971299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c176 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-11727/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4161877/10000000) (δ := 10887/1000000000) (ψ := -515201/500000) 217 179
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t176 : ((-35377109807/5000000000000 : ℚ) : ℝ) ≤ stT217 176 := by
  have hc : ((-46933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35377109807/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-46933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c177 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((181351/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1088181/10000000) (δ := 1377/125000000) (ψ := -515201/500000) 217 179
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t177 : ((68152118643/1000000000000 : ℚ) : ℝ) ≤ stT217 177 := by
  have hc : ((181341/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68152118643/1000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((181341/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c178 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((705787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 492039/2500000) (δ := 10887/1000000000) (ψ := -515201/500000) 217 179
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t178 : ((528971759347/10000000000000 : ℚ) : ℝ) ≤ stT217 178 := by
  have hc : ((705737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((528971759347/10000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((705737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c179 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-209419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1251851/2500000) (δ := 10987/1000000000) (ψ := -515201/500000) 217 179
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t179 : ((-9784124099/312500000000 : ℚ) : ℝ) ≤ stT217 179 := by
  have hc : ((-52361/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9784124099/312500000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-52361/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c180 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-249383/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1919573/2500000) (δ := 5447/500000000) (ψ := -515201/500000) 217 180
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t180 : ((-92944216149/1250000000000 : ℚ) : ℝ) ≤ stT217 180 := by
  have hc : ((-498791/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92944216149/1250000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-498791/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c181 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-293893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2336367/5000000) (δ := 11009/1000000000) (ψ := -515201/500000) 217 180
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t181 : ((-43697272437/2000000000000 : ℚ) : ℝ) ≤ stT217 181 := by
  have hc : ((-293943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43697272437/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-293943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c182 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((781637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -26309/156250) (δ := 11009/1000000000) (ψ := -515201/500000) 217 180
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t182 : ((579350582163/10000000000000 : ℚ) : ℝ) ≤ stT217 182 := by
  have hc : ((781587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((579350582163/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((781587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c183 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((435013/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1288853/10000000) (δ := 10909/1000000000) (ψ := -515201/500000) 217 180
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t183 : ((80388066087/1250000000000 : ℚ) : ℝ) ≤ stT217 183 := by
  have hc : ((108747/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80388066087/1250000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((108747/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c184 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-31741/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4245261/10000000) (δ := 10909/1000000000) (ψ := -515201/500000) 217 180
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t184 : ((-4681799547/500000000000 : ℚ) : ℝ) ≤ stT217 184 := by
  have hc : ((-63507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4681799547/500000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-63507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c185 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-964481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1437133/2000000) (δ := 11009/1000000000) (ψ := -515201/500000) 217 180
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t185 : ((-141827531833/2000000000000 : ℚ) : ℝ) ≤ stT217 185 := by
  have hc : ((-964531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141827531833/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-964531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c186 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-154917/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5597789/10000000) (δ := 5451/500000000) (ψ := -515201/500000) 217 181
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t186 : ((-56799943431/1250000000000 : ℚ) : ℝ) ≤ stT217 186 := by
  have hc : ((-309859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56799943431/1250000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-309859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c187 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((237619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -336113/1250000) (δ := 5451/500000000) (ψ := -515201/500000) 217 181
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t187 : ((10859114973/312500000000 : ℚ) : ℝ) ≤ stT217 187 := by
  have hc : ((118797/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10859114973/312500000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((118797/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c188 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((996659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 204411/10000000) (δ := 5501/500000000) (ψ := -515201/500000) 217 181
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t188 : ((181712715579/2500000000000 : ℚ) : ℝ) ≤ stT217 188 := by
  have hc : ((996609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181712715579/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((996609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c189 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((82859/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 770607/2500000) (δ := 5451/500000000) (ψ := -515201/500000) 217 181
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t189 : ((3766367583/156250000000 : ℚ) : ℝ) ≤ stT217 189 := by
  have hc : ((165693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3766367583/156250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((165693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c190 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-180603/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5945201/10000000) (δ := 11001/1000000000) (ψ := -515201/500000) 217 181
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t190 : ((-262064782187/5000000000000 : ℚ) : ℝ) ≤ stT217 190 := by
  have hc : ((-361231/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-262064782187/5000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-361231/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c191 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-186057/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6914963/10000000) (δ := 2727/250000000) (ψ := -515201/500000) 217 182
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t191 : ((-5385337181/80000000000 : ℚ) : ℝ) ≤ stT217 191 := by
  have hc : ((-186067/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5385337181/80000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-186067/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c192 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-61997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2041041/5000000) (δ := 43/3906250) (ψ := -515201/500000) 217 182
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t192 : ((-5597321917/1250000000000 : ℚ) : ℝ) ≤ stT217 192 := by
  have hc : ((-62047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5597321917/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-62047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c193 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((874903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1263903/10000000) (δ := 43/3906250) (ψ := -515201/500000) 217 182
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t193 : ((125946462439/2000000000000 : ℚ) : ℝ) ≤ stT217 193 := by
  have hc : ((874853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125946462439/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((874853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c194 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((816257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1539737/10000000) (δ := 43/3906250) (ψ := -515201/500000) 217 182
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t194 : ((293001172653/5000000000000 : ℚ) : ℝ) ≤ stT217 194 := by
  have hc : ((816207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((293001172653/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((816207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c195 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-16009/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2164473/5000000) (δ := 2179/200000000) (ψ := -515201/500000) 217 182
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t195 : ((-1146786561/100000000000 : ℚ) : ℝ) ≤ stT217 195 := by
  have hc : ((-8007/50000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1146786561/100000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-8007/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c196 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-38213/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 443993/625000) (δ := 2727/250000000) (ψ := -515201/500000) 217 182
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t196 : ((-2729643949/40000000000 : ℚ) : ℝ) ≤ stT217 196 := by
  have hc : ((-7643/8000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2729643949/40000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-7643/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c197 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-346809/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5843239/10000000) (δ := 2747/250000000) (ψ := -515201/500000) 217 183
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t197 : ((-123554583407/2500000000000 : ℚ) : ℝ) ≤ stT217 197 := by
  have hc : ((-173417/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123554583407/2500000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-173417/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c198 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((326159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1548199/5000000) (δ := 2203/200000000) (ψ := -515201/500000) 217 183
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t198 : ((231755556921/10000000000000 : ℚ) : ℝ) ≤ stT217 198 := by
  have hc : ((326109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((231755556921/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((326109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c199 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((494727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2839/78125) (δ := 1361/125000000) (ψ := -515201/500000) 217 183
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t199 : ((175342424231/2500000000000 : ℚ) : ℝ) ≤ stT217 199 := by
  have hc : ((247351/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175342424231/2500000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((247351/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c200 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((146971/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2355889/10000000) (δ := 2747/250000000) (ψ := -515201/500000) 217 183
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t200 : ((103915237101/2500000000000 : ℚ) : ℝ) ≤ stT217 200 := by
  have hc : ((293917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103915237101/2500000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((293917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c201 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-219223/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2530831/5000000) (δ := 2747/250000000) (ψ := -515201/500000) 217 183
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t201 : ((-4832678119/156250000000 : ℚ) : ℝ) ≤ stT217 201 := by
  have hc : ((-13703/31250 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4832678119/156250000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-13703/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c202 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-999199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7753927/10000000) (δ := 1361/125000000) (ψ := -515201/500000) 217 183
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t202 : ((-351534798951/5000000000000 : ℚ) : ℝ) ≤ stT217 202 := by
  have hc : ((-999249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-351534798951/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-999249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c203 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-32091/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41211/78125) (δ := 11023/1000000000) (ψ := -515201/500000) 217 184
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t203 : ((-180205430839/5000000000000 : ℚ) : ℝ) ≤ stT217 203 := by
  have hc : ((-256753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180205430839/5000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-256753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c204 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((31441/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2609163/10000000) (δ := 11023/1000000000) (ψ := -515201/500000) 217 184
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t204 : ((8804365521/250000000000 : ℚ) : ℝ) ≤ stT217 204 := by
  have hc : ((251503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8804365521/250000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((251503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c205 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((999847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21831/5000000) (δ := 11023/1000000000) (ψ := -515201/500000) 217 184
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t205 : ((69828821871/1000000000000 : ℚ) : ℝ) ≤ stT217 205 := by
  have hc : ((999797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69828821871/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((999797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c206 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((477113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 107343/400000) (δ := 17/1562500) (ψ := -515201/500000) 217 184
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t206 : ((332385535179/10000000000000 : ℚ) : ℝ) ≤ stT217 206 := by
  have hc : ((477063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((332385535179/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((477063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c207 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-525649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2655343/5000000) (δ := 11023/1000000000) (ψ := -515201/500000) 217 184
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t207 : ((-365386564251/10000000000000 : ℚ) : ℝ) ≤ stT217 207 := by
  have hc : ((-525699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-365386564251/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-525699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c208 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-199919/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7782807/10000000) (δ := 1103/100000000) (ψ := -515201/500000) 217 185
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t208 : ((-1083015393/15625000000 : ℚ) : ℝ) ≤ stT217 208 := by
  have hc : ((-199929/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1083015393/15625000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-199929/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c209 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-240393/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5180869/10000000) (δ := 10873/1000000000) (ψ := -515201/500000) 217 185
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t209 : ((-16630073687/500000000000 : ℚ) : ℝ) ≤ stT217 209 := by
  have hc : ((-120209/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16630073687/500000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-120209/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c210 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((1273/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1295677/5000000) (δ := 10973/1000000000) (ψ := -515201/500000) 217 185
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t210 : ((1405386379/40000000000 : ℚ) : ℝ) ≤ stT217 210 := by
  have hc : ((10183/20000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1405386379/40000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((10183/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c211 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((62499/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14153/10000000) (δ := 1093/100000000) (ψ := -515201/500000) 217 185
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t211 : ((86047820469/1250000000000 : ℚ) : ℝ) ≤ stT217 211 := by
  have hc : ((499967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86047820469/1250000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((499967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c212 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((523079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2550841/10000000) (δ := 10873/1000000000) (ψ := -515201/500000) 217 185
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t212 : ((179608681629/5000000000000 : ℚ) : ℝ) ≤ stT217 212 := by
  have hc : ((523029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179608681629/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((523029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c213 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-453529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 318987/625000) (δ := 1093/100000000) (ψ := -515201/500000) 217 185
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t213 : ((-310787341431/10000000000000 : ℚ) : ℝ) ≤ stT217 213 := by
  have hc : ((-453579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-310787341431/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-453579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c214 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-498251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 955601/1250000) (δ := 1103/100000000) (ψ := -515201/500000) 217 185
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t214 : ((-42576812217/625000000000 : ℚ) : ℝ) ≤ stT217 214 := by
  have hc : ((-124569/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42576812217/625000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-124569/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c215 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-599449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5534021/10000000) (δ := 5483/500000000) (ψ := -515201/500000) 217 186
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t215 : ((-81771064101/2000000000000 : ℚ) : ℝ) ≤ stT217 215 := by
  have hc : ((-599499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81771064101/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-599499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c216 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((1113/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -754151/2500000) (δ := 5483/500000000) (ψ := -515201/500000) 217 186
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t216 : ((24230187343/1000000000000 : ℚ) : ℝ) ≤ stT217 216 := by
  have hc : ((35611/100000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24230187343/1000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((35611/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c217 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((195839/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10217/200000) (δ := 11037/1000000000) (ψ := -515201/500000) 217 186
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t217 : ((33234335419/500000000000 : ℚ) : ℝ) ≤ stT217 217 := by
  have hc : ((195829/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33234335419/500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((195829/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c218 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((350727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 991701/5000000) (δ := 10937/1000000000) (ψ := -515201/500000) 217 186
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t218 : ((23752520407/500000000000 : ℚ) : ℝ) ≤ stT217 218 := by
  have hc : ((175351/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23752520407/500000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((175351/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c219 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-5351/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2233131/5000000) (δ := 11037/1000000000) (ψ := -515201/500000) 217 186
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t219 : ((-7233437421/500000000000 : ℚ) : ℝ) ≤ stT217 219 := by
  have hc : ((-21409/100000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7233437421/500000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-21409/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c220 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-186719/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6937783/10000000) (δ := 5433/500000000) (ψ := -515201/500000) 217 186
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t220 : ((-629463459/10000000000 : ℚ) : ℝ) ≤ stT217 220 := by
  have hc : ((-186729/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-629463459/10000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-186729/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c221 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-203809/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3154917/5000000) (δ := 171/15625000) (ψ := -515201/500000) 217 187
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t221 : ((-274210439739/5000000000000 : ℚ) : ℝ) ≤ stT217 221 := by
  have hc : ((-407643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274210439739/5000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-407643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c222 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((829/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -482583/1250000) (δ := 10959/1000000000) (ψ := -515201/500000) 217 187
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t222 : ((2221358571/1250000000000 : ℚ) : ℝ) ≤ stT217 222 := by
  have hc : ((13239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2221358571/1250000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((13239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c223 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((842451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -355613/2500000) (δ := 10959/1000000000) (ψ := -515201/500000) 217 187
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t223 : ((564112987249/10000000000000 : ℚ) : ℝ) ≤ stT217 223 := by
  have hc : ((842401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((564112987249/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((842401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c224 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((920303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 125607/1250000) (δ := 10859/1000000000) (ψ := -515201/500000) 217 187
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t224 : ((614869802709/10000000000000 : ℚ) : ℝ) ≤ stT217 224 := by
  have hc : ((920253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((614869802709/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((920253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c225 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((200873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 427671/1250000) (δ := 10859/1000000000) (ψ := -515201/500000) 217 187
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t225 : ((66940933059/5000000000000 : ℚ) : ℝ) ≤ stT217 225 := by
  have hc : ((200823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66940933059/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((200823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c226 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-172239/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5827111/10000000) (δ := 21859/1000000000) (ψ := -515201/500000) 217 187
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t226 : ((-229160295073/5000000000000 : ℚ) : ℝ) ≤ stT217 226 := by
  have hc : ((-344503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229160295073/5000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-344503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c227 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-61823/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7485687/10000000) (δ := 10951/1000000000) (ψ := -515201/500000) 217 188
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t227 : ((-82070965979/1250000000000 : ℚ) : ℝ) ≤ stT217 227 := by
  have hc : ((-494609/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82070965979/1250000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-494609/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c228 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-452559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2550537/5000000) (δ := 10951/1000000000) (ψ := -515201/500000) 217 188
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t228 : ((-299748004603/10000000000000 : ℚ) : ℝ) ≤ stT217 228 := by
  have hc : ((-452609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-299748004603/10000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-452609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c229 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((23091/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2726877/10000000) (δ := 10951/1000000000) (ψ := -515201/500000) 217 188
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t229 : ((15257296393/500000000000 : ℚ) : ℝ) ≤ stT217 229 := by
  have hc : ((46177/100000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15257296393/500000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((46177/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c230 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((39579/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -181521/5000000) (δ := 2713/250000000) (ψ := -515201/500000) 217 188
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t230 : ((1304814113/20000000000 : ℚ) : ℝ) ≤ stT217 230 := by
  have hc : ((39577/40000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1304814113/20000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((39577/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c231 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((87427/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 99527/500000) (δ := 2713/250000000) (ψ := -515201/500000) 217 188
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t231 : ((230074279533/5000000000000 : ℚ) : ℝ) ≤ stT217 231 := by
  have hc : ((349683/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230074279533/5000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((349683/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c232 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-32411/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4333923/10000000) (δ := 2713/250000000) (ψ := -515201/500000) 217 188
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t232 : ((-21285456393/2000000000000 : ℚ) : ℝ) ≤ stT217 232 := by
  have hc : ((-32421/200000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21285456393/2000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-32421/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c233 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-889437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 666727/1000000) (δ := 10951/1000000000) (ψ := -515201/500000) 217 188
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t233 : ((-291361251207/5000000000000 : ℚ) : ℝ) ≤ stT217 233 := by
  have hc : ((-889487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291361251207/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-889487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c234 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-89841/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6717329/10000000) (δ := 2189/200000000) (ψ := -515201/500000) 217 189
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t234 : ((-29367108483/500000000000 : ℚ) : ℝ) ≤ stT217 234 := by
  have hc : ((-44923/50000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29367108483/500000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-44923/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c235 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-94803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1100973/2500000) (δ := 2189/200000000) (ψ := -515201/500000) 217 189
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t235 : ((-15464763603/1250000000000 : ℚ) : ℝ) ≤ stT217 235 := by
  have hc : ((-23707/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15464763603/1250000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-23707/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c236 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((667381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1050137/5000000) (δ := 5429/500000000) (ψ := -515201/500000) 217 189
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t236 : ((6787423601/156250000000 : ℚ) : ℝ) ≤ stT217 236 := by
  have hc : ((667331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6787423601/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((667331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c237 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((249251/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 193579/10000000) (δ := 5479/500000000) (ψ := -515201/500000) 217 189
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t237 : ((323795206413/5000000000000 : ℚ) : ℝ) ≤ stT217 237 := by
  have hc : ((498477/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((323795206413/5000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((498477/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c238 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((273881/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 99111/400000) (δ := 5429/500000000) (ψ := -515201/500000) 217 189
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t238 : ((2773660637/78125000000 : ℚ) : ℝ) ≤ stT217 238 := by
  have hc : ((8558/15625 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2773660637/78125000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((8558/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c239 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-324207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4752423/10000000) (δ := 2189/200000000) (ψ := -515201/500000) 217 189
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t239 : ((-209744667679/10000000000000 : ℚ) : ℝ) ≤ stT217 239 := by
  have hc : ((-324257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209744667679/10000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-324257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c240 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-472277/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3508789/5000000) (δ := 5479/500000000) (ψ := -515201/500000) 217 189
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t240 : ((-76217499099/1250000000000 : ℚ) : ℝ) ≤ stT217 240 := by
  have hc : ((-236151/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76217499099/1250000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-236151/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c241 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-843127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6434671/10000000) (δ := 11037/1000000000) (ψ := -515201/500000) 217 190
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t241 : ((-543138366789/10000000000000 : ℚ) : ℝ) ≤ stT217 241 := by
  have hc : ((-843177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-543138366789/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-843177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c242 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-13041/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4188287/10000000) (δ := 11037/1000000000) (ψ := -515201/500000) 217 190
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t242 : ((-1341935757/200000000000 : ℚ) : ℝ) ≤ stT217 242 := by
  have hc : ((-52189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1341935757/200000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-52189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c243 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((355291/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1951179/10000000) (δ := 5483/500000000) (ψ := -515201/500000) 217 190
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t243 : ((227903139/5000000000 : ℚ) : ℝ) ≤ stT217 243 := by
  have hc : ((177633/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227903139/5000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((177633/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c244 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((993879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6919/250000) (δ := 5483/500000000) (ψ := -515201/500000) 217 190
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t244 : ((79529178067/1250000000000 : ℚ) : ℝ) ≤ stT217 244 := by
  have hc : ((993829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79529178067/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((993829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c245 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((541797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1247779/5000000) (δ := 10933/500000000) (ψ := -515201/500000) 217 190
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t245 : ((86527289093/2500000000000 : ℚ) : ℝ) ≤ stT217 245 := by
  have hc : ((541747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86527289093/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((541747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c246 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-153169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94107/200000) (δ := 5433/500000000) (ψ := -515201/500000) 217 190
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t246 : ((-48836485469/2500000000000 : ℚ) : ℝ) ≤ stT217 246 := by
  have hc : ((-76597/250000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48836485469/2500000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-76597/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c247 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-232247/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1726541/2500000) (δ := 5433/500000000) (ψ := -515201/500000) 217 190
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t247 : ((-59113294383/1000000000000 : ℚ) : ℝ) ≤ stT217 247 := by
  have hc : ((-464519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59113294383/1000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-464519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c248 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-109839/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3304941/5000000) (δ := 10973/1000000000) (ψ := -515201/500000) 217 191
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t248 : ((-279007374381/5000000000000 : ℚ) : ℝ) ≤ stT217 248 := by
  have hc : ((-439381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-279007374381/5000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-439381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c249 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-99299/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -553351/1250000) (δ := 10873/1000000000) (ψ := -515201/500000) 217 191
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t249 : ((-629441019/50000000000 : ℚ) : ℝ) ≤ stT217 249 := by
  have hc : ((-24831/125000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-629441019/50000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-24831/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_c250 :
    |Real.cos (((217 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((620853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1126207/5000000) (δ := 1093/100000000) (ψ := -515201/500000) 217 191
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st217_t250 : ((78525992273/2000000000000 : ℚ) : ℝ) ≤ stT217 250 := by
  have hc : ((620803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((217 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st217_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78525992273/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((620803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st217_p1 : ((64303/125000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT217 (i+1) := by
  rw [Finset.sum_range_one]
  exact st217_t1

theorem st217_p2 : ((5393171677119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT217 (i+1))
      = (∑ i ∈ Finset.range 1, stT217 (i+1)) + stT217 2 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 1
    simpa using h
  have hprev := st217_p1
  have hstep := st217_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p3 : ((3829458070873/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT217 (i+1))
      = (∑ i ∈ Finset.range 2, stT217 (i+1)) + stT217 3 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 2
    simpa using h
  have hprev := st217_p2
  have hstep := st217_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p4 : ((5036289320873/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT217 (i+1))
      = (∑ i ∈ Finset.range 3, stT217 (i+1)) + stT217 4 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 3
    simpa using h
  have hprev := st217_p3
  have hstep := st217_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p5 : ((5026010116277/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT217 (i+1))
      = (∑ i ∈ Finset.range 4, stT217 (i+1)) + stT217 5 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 4
    simpa using h
  have hprev := st217_p4
  have hstep := st217_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p6 : ((6005491445163/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT217 (i+1))
      = (∑ i ∈ Finset.range 5, stT217 (i+1)) + stT217 6 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 5
    simpa using h
  have hprev := st217_p5
  have hstep := st217_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p7 : ((21449044260157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT217 (i+1))
      = (∑ i ∈ Finset.range 6, stT217 (i+1)) + stT217 7 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 6
    simpa using h
  have hprev := st217_p6
  have hstep := st217_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p8 : ((24958923432709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT217 (i+1))
      = (∑ i ∈ Finset.range 7, stT217 (i+1)) + stT217 8 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 7
    simpa using h
  have hprev := st217_p7
  have hstep := st217_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p9 : ((5627439289643/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT217 (i+1))
      = (∑ i ∈ Finset.range 8, stT217 (i+1)) + stT217 9 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 8
    simpa using h
  have hprev := st217_p8
  have hstep := st217_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p10 : ((26926970521669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT217 (i+1))
      = (∑ i ∈ Finset.range 9, stT217 (i+1)) + stT217 10 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 9
    simpa using h
  have hprev := st217_p9
  have hstep := st217_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p11 : ((29916213852129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT217 (i+1))
      = (∑ i ∈ Finset.range 10, stT217 (i+1)) + stT217 11 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 10
    simpa using h
  have hprev := st217_p10
  have hstep := st217_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p12 : ((32788744716703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT217 (i+1))
      = (∑ i ∈ Finset.range 11, stT217 (i+1)) + stT217 12 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 11
    simpa using h
  have hprev := st217_p11
  have hstep := st217_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p13 : ((8191406896467/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT217 (i+1))
      = (∑ i ∈ Finset.range 12, stT217 (i+1)) + stT217 13 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 12
    simpa using h
  have hprev := st217_p12
  have hstep := st217_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p14 : ((31811037037593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT217 (i+1))
      = (∑ i ∈ Finset.range 13, stT217 (i+1)) + stT217 14 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 13
    simpa using h
  have hprev := st217_p13
  have hstep := st217_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p15 : ((3859256412927/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT217 (i+1))
      = (∑ i ∈ Finset.range 14, stT217 (i+1)) + stT217 15 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 14
    simpa using h
  have hprev := st217_p14
  have hstep := st217_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p16 : ((4132939850427/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT217 (i+1))
      = (∑ i ∈ Finset.range 15, stT217 (i+1)) + stT217 16 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 15
    simpa using h
  have hprev := st217_p15
  have hstep := st217_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p17 : ((221749290213/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT217 (i+1))
      = (∑ i ∈ Finset.range 16, stT217 (i+1)) + stT217 17 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 16
    simpa using h
  have hprev := st217_p16
  have hstep := st217_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p18 : ((2364357764439/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT217 (i+1))
      = (∑ i ∈ Finset.range 17, stT217 (i+1)) + stT217 18 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 17
    simpa using h
  have hprev := st217_p17
  have hstep := st217_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p19 : ((39235379460651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT217 (i+1))
      = (∑ i ∈ Finset.range 18, stT217 (i+1)) + stT217 19 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 18
    simpa using h
  have hprev := st217_p18
  have hstep := st217_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p20 : ((37668779039511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT217 (i+1))
      = (∑ i ∈ Finset.range 19, stT217 (i+1)) + stT217 20 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 19
    simpa using h
  have hprev := st217_p19
  have hstep := st217_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p21 : ((36846058277289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT217 (i+1))
      = (∑ i ∈ Finset.range 20, stT217 (i+1)) + stT217 21 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 20
    simpa using h
  have hprev := st217_p20
  have hstep := st217_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p22 : ((9675561349923/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT217 (i+1))
      = (∑ i ∈ Finset.range 21, stT217 (i+1)) + stT217 22 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 21
    simpa using h
  have hprev := st217_p21
  have hstep := st217_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p23 : ((18352915830011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT217 (i+1))
      = (∑ i ∈ Finset.range 22, stT217 (i+1)) + stT217 23 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 22
    simpa using h
  have hprev := st217_p22
  have hstep := st217_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p24 : ((1203566572487/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT217 (i+1))
      = (∑ i ∈ Finset.range 23, stT217 (i+1)) + stT217 24 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 23
    simpa using h
  have hprev := st217_p23
  have hstep := st217_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p25 : ((9379158455209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT217 (i+1))
      = (∑ i ∈ Finset.range 24, stT217 (i+1)) + stT217 25 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 24
    simpa using h
  have hprev := st217_p24
  have hstep := st217_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p26 : ((3676767978117/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT217 (i+1))
      = (∑ i ∈ Finset.range 25, stT217 (i+1)) + stT217 26 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 25
    simpa using h
  have hprev := st217_p25
  have hstep := st217_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p27 : ((3868905246867/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT217 (i+1))
      = (∑ i ∈ Finset.range 26, stT217 (i+1)) + stT217 27 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 26
    simpa using h
  have hprev := st217_p26
  have hstep := st217_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p28 : ((19361785978661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT217 (i+1))
      = (∑ i ∈ Finset.range 27, stT217 (i+1)) + stT217 28 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 27
    simpa using h
  have hprev := st217_p27
  have hstep := st217_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p29 : ((1846387165607/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT217 (i+1))
      = (∑ i ∈ Finset.range 28, stT217 (i+1)) + stT217 29 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 28
    simpa using h
  have hprev := st217_p28
  have hstep := st217_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p30 : ((8919175268983/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT217 (i+1))
      = (∑ i ∈ Finset.range 29, stT217 (i+1)) + stT217 30 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 29
    simpa using h
  have hprev := st217_p29
  have hstep := st217_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p31 : ((35815451558341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT217 (i+1))
      = (∑ i ∈ Finset.range 30, stT217 (i+1)) + stT217 31 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 30
    simpa using h
  have hprev := st217_p30
  have hstep := st217_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p32 : ((36931949582983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT217 (i+1))
      = (∑ i ∈ Finset.range 31, stT217 (i+1)) + stT217 32 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 31
    simpa using h
  have hprev := st217_p31
  have hstep := st217_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p33 : ((38465439199231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT217 (i+1))
      = (∑ i ∈ Finset.range 32, stT217 (i+1)) + stT217 33 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 32
    simpa using h
  have hprev := st217_p32
  have hstep := st217_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p34 : ((40104769350941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT217 (i+1))
      = (∑ i ∈ Finset.range 33, stT217 (i+1)) + stT217 34 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 33
    simpa using h
  have hprev := st217_p33
  have hstep := st217_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p35 : ((41723993138309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT217 (i+1))
      = (∑ i ∈ Finset.range 34, stT217 (i+1)) + stT217 35 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 34
    simpa using h
  have hprev := st217_p34
  have hstep := st217_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p36 : ((43216615874593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT217 (i+1))
      = (∑ i ∈ Finset.range 35, stT217 (i+1)) + stT217 36 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 35
    simpa using h
  have hprev := st217_p35
  have hstep := st217_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p37 : ((44363600696069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT217 (i+1))
      = (∑ i ∈ Finset.range 36, stT217 (i+1)) + stT217 37 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 36
    simpa using h
  have hprev := st217_p36
  have hstep := st217_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p38 : ((44805657255497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT217 (i+1))
      = (∑ i ∈ Finset.range 37, stT217 (i+1)) + stT217 38 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 37
    simpa using h
  have hprev := st217_p37
  have hstep := st217_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p39 : ((44225845853553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT217 (i+1))
      = (∑ i ∈ Finset.range 38, stT217 (i+1)) + stT217 39 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 38
    simpa using h
  have hprev := st217_p38
  have hstep := st217_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p40 : ((21388188101889/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT217 (i+1))
      = (∑ i ∈ Finset.range 39, stT217 (i+1)) + stT217 40 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 39
    simpa using h
  have hprev := st217_p39
  have hstep := st217_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p41 : ((5177023537671/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT217 (i+1))
      = (∑ i ∈ Finset.range 40, stT217 (i+1)) + stT217 41 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 40
    simpa using h
  have hprev := st217_p40
  have hstep := st217_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p42 : ((20705729451079/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT217 (i+1))
      = (∑ i ∈ Finset.range 41, stT217 (i+1)) + stT217 42 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 41
    simpa using h
  have hprev := st217_p41
  have hstep := st217_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p43 : ((1338059778689/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT217 (i+1))
      = (∑ i ∈ Finset.range 42, stT217 (i+1)) + stT217 43 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 42
    simpa using h
  have hprev := st217_p42
  have hstep := st217_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p44 : ((10939410103217/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT217 (i+1))
      = (∑ i ∈ Finset.range 43, stT217 (i+1)) + stT217 44 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 43
    simpa using h
  have hprev := st217_p43
  have hstep := st217_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p45 : ((10689890629199/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT217 (i+1))
      = (∑ i ∈ Finset.range 44, stT217 (i+1)) + stT217 45 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 44
    simpa using h
  have hprev := st217_p44
  have hstep := st217_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p46 : ((10402440654839/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT217 (i+1))
      = (∑ i ∈ Finset.range 45, stT217 (i+1)) + stT217 46 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 45
    simpa using h
  have hprev := st217_p45
  have hstep := st217_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p47 : ((42573691848569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT217 (i+1))
      = (∑ i ∈ Finset.range 46, stT217 (i+1)) + stT217 47 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 46
    simpa using h
  have hprev := st217_p46
  have hstep := st217_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p48 : ((43508969981069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT217 (i+1))
      = (∑ i ∈ Finset.range 47, stT217 (i+1)) + stT217 48 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 47
    simpa using h
  have hprev := st217_p47
  have hstep := st217_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p49 : ((42233276613649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT217 (i+1))
      = (∑ i ∈ Finset.range 48, stT217 (i+1)) + stT217 49 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 48
    simpa using h
  have hprev := st217_p48
  have hstep := st217_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p50 : ((42037835067277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT217 (i+1))
      = (∑ i ∈ Finset.range 49, stT217 (i+1)) + stT217 50 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 49
    simpa using h
  have hprev := st217_p49
  have hstep := st217_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p51 : ((43384806407677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT217 (i+1))
      = (∑ i ∈ Finset.range 50, stT217 (i+1)) + stT217 51 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 50
    simpa using h
  have hprev := st217_p50
  have hstep := st217_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p52 : ((848282252059/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT217 (i+1))
      = (∑ i ∈ Finset.range 51, stT217 (i+1)) + stT217 52 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 51
    simpa using h
  have hprev := st217_p51
  have hstep := st217_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p53 : ((5264859918069/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT217 (i+1))
      = (∑ i ∈ Finset.range 52, stT217 (i+1)) + stT217 53 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 52
    simpa using h
  have hprev := st217_p52
  have hstep := st217_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p54 : ((8670047180589/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT217 (i+1))
      = (∑ i ∈ Finset.range 53, stT217 (i+1)) + stT217 54 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 53
    simpa using h
  have hprev := st217_p53
  have hstep := st217_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p55 : ((8421697789869/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT217 (i+1))
      = (∑ i ∈ Finset.range 54, stT217 (i+1)) + stT217 55 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 54
    simpa using h
  have hprev := st217_p54
  have hstep := st217_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p56 : ((42631072791541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT217 (i+1))
      = (∑ i ∈ Finset.range 55, stT217 (i+1)) + stT217 56 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 55
    simpa using h
  have hprev := st217_p55
  have hstep := st217_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p57 : ((43019111659857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT217 (i+1))
      = (∑ i ∈ Finset.range 56, stT217 (i+1)) + stT217 57 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 56
    simpa using h
  have hprev := st217_p56
  have hstep := st217_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p58 : ((5245827558739/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT217 (i+1))
      = (∑ i ∈ Finset.range 57, stT217 (i+1)) + stT217 58 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 57
    simpa using h
  have hprev := st217_p57
  have hstep := st217_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p59 : ((43264967029943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT217 (i+1))
      = (∑ i ∈ Finset.range 58, stT217 (i+1)) + stT217 59 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 58
    simpa using h
  have hprev := st217_p58
  have hstep := st217_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p60 : ((42092753897903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT217 (i+1))
      = (∑ i ∈ Finset.range 59, stT217 (i+1)) + stT217 60 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 59
    simpa using h
  have hprev := st217_p59
  have hstep := st217_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p61 : ((42910731078751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT217 (i+1))
      = (∑ i ∈ Finset.range 60, stT217 (i+1)) + stT217 61 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 60
    simpa using h
  have hprev := st217_p60
  have hstep := st217_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p62 : ((42527905485877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT217 (i+1))
      = (∑ i ∈ Finset.range 61, stT217 (i+1)) + stT217 62 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 61
    simpa using h
  have hprev := st217_p61
  have hstep := st217_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p63 : ((42497170664487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT217 (i+1))
      = (∑ i ∈ Finset.range 62, stT217 (i+1)) + stT217 63 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 62
    simpa using h
  have hprev := st217_p62
  have hstep := st217_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p64 : ((42866670664487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT217 (i+1))
      = (∑ i ∈ Finset.range 63, stT217 (i+1)) + stT217 64 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 63
    simpa using h
  have hprev := st217_p63
  have hstep := st217_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p65 : ((42247126761271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT217 (i+1))
      = (∑ i ∈ Finset.range 64, stT217 (i+1)) + stT217 65 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 64
    simpa using h
  have hprev := st217_p64
  have hstep := st217_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p66 : ((43034766473419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT217 (i+1))
      = (∑ i ∈ Finset.range 65, stT217 (i+1)) + stT217 66 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 65
    simpa using h
  have hprev := st217_p65
  have hstep := st217_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p67 : ((10536193776141/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT217 (i+1))
      = (∑ i ∈ Finset.range 66, stT217 (i+1)) + stT217 67 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 66
    simpa using h
  have hprev := st217_p66
  have hstep := st217_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p68 : ((4308653720133/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT217 (i+1))
      = (∑ i ∈ Finset.range 67, stT217 (i+1)) + stT217 68 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 67
    simpa using h
  have hprev := st217_p67
  have hstep := st217_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p69 : ((5266481316179/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT217 (i+1))
      = (∑ i ∈ Finset.range 68, stT217 (i+1)) + stT217 69 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 68
    simpa using h
  have hprev := st217_p68
  have hstep := st217_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p70 : ((2153269227703/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT217 (i+1))
      = (∑ i ∈ Finset.range 69, stT217 (i+1)) + stT217 70 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 69
    simpa using h
  have hprev := st217_p69
  have hstep := st217_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p71 : ((21093623881009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT217 (i+1))
      = (∑ i ∈ Finset.range 70, stT217 (i+1)) + stT217 71 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 70
    simpa using h
  have hprev := st217_p70
  have hstep := st217_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p72 : ((42969872168387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT217 (i+1))
      = (∑ i ∈ Finset.range 71, stT217 (i+1)) + stT217 72 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 71
    simpa using h
  have hprev := st217_p71
  have hstep := st217_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p73 : ((42330476092787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT217 (i+1))
      = (∑ i ∈ Finset.range 72, stT217 (i+1)) + stT217 73 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 72
    simpa using h
  have hprev := st217_p72
  have hstep := st217_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p74 : ((42770983585751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT217 (i+1))
      = (∑ i ∈ Finset.range 73, stT217 (i+1)) + stT217 74 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 73
    simpa using h
  have hprev := st217_p73
  have hstep := st217_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p75 : ((42587048954059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT217 (i+1))
      = (∑ i ∈ Finset.range 74, stT217 (i+1)) + stT217 75 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 74
    simpa using h
  have hprev := st217_p74
  have hstep := st217_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p76 : ((42463962789043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT217 (i+1))
      = (∑ i ∈ Finset.range 75, stT217 (i+1)) + stT217 76 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 75
    simpa using h
  have hprev := st217_p75
  have hstep := st217_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p77 : ((21460339433039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT217 (i+1))
      = (∑ i ∈ Finset.range 76, stT217 (i+1)) + stT217 77 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 76
    simpa using h
  have hprev := st217_p76
  have hstep := st217_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p78 : ((10536385149001/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT217 (i+1))
      = (∑ i ∈ Finset.range 77, stT217 (i+1)) + stT217 78 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 77
    simpa using h
  have hprev := st217_p77
  have hstep := st217_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p79 : ((21581799034847/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT217 (i+1))
      = (∑ i ∈ Finset.range 78, stT217 (i+1)) + stT217 79 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 78
    simpa using h
  have hprev := st217_p78
  have hstep := st217_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p80 : ((10511483534737/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT217 (i+1))
      = (∑ i ∈ Finset.range 79, stT217 (i+1)) + stT217 80 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 79
    simpa using h
  have hprev := st217_p79
  have hstep := st217_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p81 : ((43061190704089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT217 (i+1))
      = (∑ i ∈ Finset.range 80, stT217 (i+1)) + stT217 81 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 80
    simpa using h
  have hprev := st217_p80
  have hstep := st217_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p82 : ((42372331635081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT217 (i+1))
      = (∑ i ∈ Finset.range 81, stT217 (i+1)) + stT217 82 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 81
    simpa using h
  have hprev := st217_p81
  have hstep := st217_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p83 : ((42549607403933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT217 (i+1))
      = (∑ i ∈ Finset.range 82, stT217 (i+1)) + stT217 83 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 82
    simpa using h
  have hprev := st217_p82
  have hstep := st217_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p84 : ((10738691734437/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT217 (i+1))
      = (∑ i ∈ Finset.range 83, stT217 (i+1)) + stT217 84 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 83
    simpa using h
  have hprev := st217_p83
  have hstep := st217_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p85 : ((525873891987/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT217 (i+1))
      = (∑ i ∈ Finset.range 84, stT217 (i+1)) + stT217 85 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 84
    simpa using h
  have hprev := st217_p84
  have hstep := st217_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p86 : ((43148090628161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT217 (i+1))
      = (∑ i ∈ Finset.range 85, stT217 (i+1)) + stT217 86 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 85
    simpa using h
  have hprev := st217_p85
  have hstep := st217_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p87 : ((42275255559923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT217 (i+1))
      = (∑ i ∈ Finset.range 86, stT217 (i+1)) + stT217 87 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 86
    simpa using h
  have hprev := st217_p86
  have hstep := st217_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p88 : ((42579590888399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT217 (i+1))
      = (∑ i ∈ Finset.range 87, stT217 (i+1)) + stT217 88 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 87
    simpa using h
  have hprev := st217_p87
  have hstep := st217_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p89 : ((21496174210107/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT217 (i+1))
      = (∑ i ∈ Finset.range 88, stT217 (i+1)) + stT217 89 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 88
    simpa using h
  have hprev := st217_p88
  have hstep := st217_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p90 : ((2627805071471/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT217 (i+1))
      = (∑ i ∈ Finset.range 89, stT217 (i+1)) + stT217 90 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 89
    simpa using h
  have hprev := st217_p89
  have hstep := st217_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p91 : ((10762335407729/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT217 (i+1))
      = (∑ i ∈ Finset.range 90, stT217 (i+1)) + stT217 91 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 90
    simpa using h
  have hprev := st217_p90
  have hstep := st217_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p92 : ((8507917823203/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT217 (i+1))
      = (∑ i ∈ Finset.range 91, stT217 (i+1)) + stT217 92 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 91
    simpa using h
  have hprev := st217_p91
  have hstep := st217_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p93 : ((42248175532407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT217 (i+1))
      = (∑ i ∈ Finset.range 92, stT217 (i+1)) + stT217 93 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 92
    simpa using h
  have hprev := st217_p92
  have hstep := st217_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p94 : ((21584952970239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT217 (i+1))
      = (∑ i ∈ Finset.range 93, stT217 (i+1)) + stT217 94 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 93
    simpa using h
  have hprev := st217_p93
  have hstep := st217_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p95 : ((4221706693143/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT217 (i+1))
      = (∑ i ∈ Finset.range 94, stT217 (i+1)) + stT217 95 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 94
    simpa using h
  have hprev := st217_p94
  have hstep := st217_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p96 : ((4253949099563/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT217 (i+1))
      = (∑ i ∈ Finset.range 95, stT217 (i+1)) + stT217 96 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 95
    simpa using h
  have hprev := st217_p95
  have hstep := st217_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p97 : ((5386068306569/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT217 (i+1))
      = (∑ i ∈ Finset.range 96, stT217 (i+1)) + stT217 97 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 96
    simpa using h
  have hprev := st217_p96
  have hstep := st217_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p98 : ((8416371857499/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT217 (i+1))
      = (∑ i ∈ Finset.range 97, stT217 (i+1)) + stT217 98 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 97
    simpa using h
  have hprev := st217_p97
  have hstep := st217_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p99 : ((21370645599597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT217 (i+1))
      = (∑ i ∈ Finset.range 98, stT217 (i+1)) + stT217 99 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 98
    simpa using h
  have hprev := st217_p98
  have hstep := st217_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p100 : ((171934939827/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT217 (i+1))
      = (∑ i ∈ Finset.range 99, stT217 (i+1)) + stT217 100 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 99
    simpa using h
  have hprev := st217_p99
  have hstep := st217_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p101 : ((4204677732481/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT217 (i+1))
      = (∑ i ∈ Finset.range 100, stT217 (i+1)) + stT217 101 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 100
    simpa using h
  have hprev := st217_p100
  have hstep := st217_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p102 : ((42828851863789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT217 (i+1))
      = (∑ i ∈ Finset.range 101, stT217 (i+1)) + stT217 102 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 101
    simpa using h
  have hprev := st217_p101
  have hstep := st217_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p103 : ((21470375375837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT217 (i+1))
      = (∑ i ∈ Finset.range 102, stT217 (i+1)) + stT217 103 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 102
    simpa using h
  have hprev := st217_p102
  have hstep := st217_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p104 : ((10510540993433/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT217 (i+1))
      = (∑ i ∈ Finset.range 103, stT217 (i+1)) + stT217 104 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 103
    simpa using h
  have hprev := st217_p103
  have hstep := st217_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p105 : ((669019014413/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT217 (i+1))
      = (∑ i ∈ Finset.range 104, stT217 (i+1)) + stT217 105 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 104
    simpa using h
  have hprev := st217_p104
  have hstep := st217_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p106 : ((42978577470767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT217 (i+1))
      = (∑ i ∈ Finset.range 105, stT217 (i+1)) + stT217 106 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 105
    simpa using h
  have hprev := st217_p105
  have hstep := st217_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p107 : ((10513730776293/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT217 (i+1))
      = (∑ i ∈ Finset.range 106, stT217 (i+1)) + stT217 107 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 106
    simpa using h
  have hprev := st217_p106
  have hstep := st217_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p108 : ((21354566411961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT217 (i+1))
      = (∑ i ∈ Finset.range 107, stT217 (i+1)) + stT217 108 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 107
    simpa using h
  have hprev := st217_p107
  have hstep := st217_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p109 : ((5384589833221/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT217 (i+1))
      = (∑ i ∈ Finset.range 108, stT217 (i+1)) + stT217 109 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 108
    simpa using h
  have hprev := st217_p108
  have hstep := st217_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p110 : ((42123346244753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT217 (i+1))
      = (∑ i ∈ Finset.range 109, stT217 (i+1)) + stT217 110 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 109
    simpa using h
  have hprev := st217_p109
  have hstep := st217_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p111 : ((42501691614837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT217 (i+1))
      = (∑ i ∈ Finset.range 110, stT217 (i+1)) + stT217 111 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 110
    simpa using h
  have hprev := st217_p110
  have hstep := st217_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p112 : ((43169764479879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT217 (i+1))
      = (∑ i ∈ Finset.range 111, stT217 (i+1)) + stT217 112 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 111
    simpa using h
  have hprev := st217_p111
  have hstep := st217_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p113 : ((42313552210193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT217 (i+1))
      = (∑ i ∈ Finset.range 112, stT217 (i+1)) + stT217 113 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 112
    simpa using h
  have hprev := st217_p112
  have hstep := st217_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p114 : ((42232938380001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT217 (i+1))
      = (∑ i ∈ Finset.range 113, stT217 (i+1)) + stT217 114 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 113
    simpa using h
  have hprev := st217_p113
  have hstep := st217_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p115 : ((43139045989273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT217 (i+1))
      = (∑ i ∈ Finset.range 114, stT217 (i+1)) + stT217 115 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 114
    simpa using h
  have hprev := st217_p114
  have hstep := st217_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p116 : ((42656646479153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT217 (i+1))
      = (∑ i ∈ Finset.range 115, stT217 (i+1)) + stT217 116 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 115
    simpa using h
  have hprev := st217_p115
  have hstep := st217_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p117 : ((1313695906993/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT217 (i+1))
      = (∑ i ∈ Finset.range 116, stT217 (i+1)) + stT217 117 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 116
    simpa using h
  have hprev := st217_p116
  have hstep := st217_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p118 : ((21432244395823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT217 (i+1))
      = (∑ i ∈ Finset.range 117, stT217 (i+1)) + stT217 118 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 117
    simpa using h
  have hprev := st217_p117
  have hstep := st217_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p119 : ((21521565615547/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT217 (i+1))
      = (∑ i ∈ Finset.range 118, stT217 (i+1)) + stT217 119 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 118
    simpa using h
  have hprev := st217_p118
  have hstep := st217_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p120 : ((42131307294131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT217 (i+1))
      = (∑ i ∈ Finset.range 119, stT217 (i+1)) + stT217 120 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 119
    simpa using h
  have hprev := st217_p119
  have hstep := st217_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p121 : ((42381608862011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT217 (i+1))
      = (∑ i ∈ Finset.range 120, stT217 (i+1)) + stT217 121 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 120
    simpa using h
  have hprev := st217_p120
  have hstep := st217_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p122 : ((43178589196969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT217 (i+1))
      = (∑ i ∈ Finset.range 121, stT217 (i+1)) + stT217 122 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 121
    simpa using h
  have hprev := st217_p121
  have hstep := st217_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p123 : ((42601232764239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT217 (i+1))
      = (∑ i ∈ Finset.range 122, stT217 (i+1)) + stT217 123 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 122
    simpa using h
  have hprev := st217_p122
  have hstep := st217_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p124 : ((42029802019653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT217 (i+1))
      = (∑ i ∈ Finset.range 123, stT217 (i+1)) + stT217 124 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 123
    simpa using h
  have hprev := st217_p123
  have hstep := st217_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p125 : ((42807084126609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT217 (i+1))
      = (∑ i ∈ Finset.range 124, stT217 (i+1)) + stT217 125 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 124
    simpa using h
  have hprev := st217_p124
  have hstep := st217_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p126 : ((43120167915929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT217 (i+1))
      = (∑ i ∈ Finset.range 125, stT217 (i+1)) + stT217 126 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 125
    simpa using h
  have hprev := st217_p125
  have hstep := st217_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p127 : ((21126555491009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT217 (i+1))
      = (∑ i ∈ Finset.range 126, stT217 (i+1)) + stT217 127 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 126
    simpa using h
  have hprev := st217_p126
  have hstep := st217_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p128 : ((4217946399937/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT217 (i+1))
      = (∑ i ∈ Finset.range 127, stT217 (i+1)) + stT217 128 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 127
    simpa using h
  have hprev := st217_p127
  have hstep := st217_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p129 : ((4305934346777/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT217 (i+1))
      = (∑ i ∈ Finset.range 128, stT217 (i+1)) + stT217 129 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 128
    simpa using h
  have hprev := st217_p128
  have hstep := st217_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p130 : ((21468695083969/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT217 (i+1))
      = (∑ i ∈ Finset.range 129, stT217 (i+1)) + stT217 130 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 129
    simpa using h
  have hprev := st217_p129
  have hstep := st217_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p131 : ((42086949310973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT217 (i+1))
      = (∑ i ∈ Finset.range 130, stT217 (i+1)) + stT217 131 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 130
    simpa using h
  have hprev := st217_p130
  have hstep := st217_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p132 : ((42353174888533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT217 (i+1))
      = (∑ i ∈ Finset.range 131, stT217 (i+1)) + stT217 132 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 131
    simpa using h
  have hprev := st217_p131
  have hstep := st217_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p133 : ((43159074664223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT217 (i+1))
      = (∑ i ∈ Finset.range 132, stT217 (i+1)) + stT217 133 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 132
    simpa using h
  have hprev := st217_p132
  have hstep := st217_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p134 : ((10699231955347/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT217 (i+1))
      = (∑ i ∈ Finset.range 133, stT217 (i+1)) + stT217 134 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 133
    simpa using h
  have hprev := st217_p133
  have hstep := st217_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p135 : ((8406309592291/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT217 (i+1))
      = (∑ i ∈ Finset.range 134, stT217 (i+1)) + stT217 135 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 134
    simpa using h
  have hprev := st217_p134
  have hstep := st217_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p136 : ((42446965105807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT217 (i+1))
      = (∑ i ∈ Finset.range 135, stT217 (i+1)) + stT217 136 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 135
    simpa using h
  have hprev := st217_p135
  have hstep := st217_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p137 : ((21593158982197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT217 (i+1))
      = (∑ i ∈ Finset.range 136, stT217 (i+1)) + stT217 137 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 136
    simpa using h
  have hprev := st217_p136
  have hstep := st217_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p138 : ((42754362071113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT217 (i+1))
      = (∑ i ∈ Finset.range 137, stT217 (i+1)) + stT217 138 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 137
    simpa using h
  have hprev := st217_p137
  have hstep := st217_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p139 : ((2626356608937/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT217 (i+1))
      = (∑ i ∈ Finset.range 138, stT217 (i+1)) + stT217 139 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 138
    simpa using h
  have hprev := st217_p138
  have hstep := st217_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p140 : ((5304550315887/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT217 (i+1))
      = (∑ i ∈ Finset.range 139, stT217 (i+1)) + stT217 140 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 139
    simpa using h
  have hprev := st217_p139
  have hstep := st217_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p141 : ((43180760426523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT217 (i+1))
      = (∑ i ∈ Finset.range 140, stT217 (i+1)) + stT217 141 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 140
    simpa using h
  have hprev := st217_p140
  have hstep := st217_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p142 : ((1712646642323/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT217 (i+1))
      = (∑ i ∈ Finset.range 141, stT217 (i+1)) + stT217 142 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 141
    simpa using h
  have hprev := st217_p141
  have hstep := st217_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p143 : ((5255794170719/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT217 (i+1))
      = (∑ i ∈ Finset.range 142, stT217 (i+1)) + stT217 143 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 142
    simpa using h
  have hprev := st217_p142
  have hstep := st217_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p144 : ((2116320829353/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT217 (i+1))
      = (∑ i ∈ Finset.range 143, stT217 (i+1)) + stT217 144 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 143
    simpa using h
  have hprev := st217_p143
  have hstep := st217_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p145 : ((21562952724381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT217 (i+1))
      = (∑ i ∈ Finset.range 144, stT217 (i+1)) + stT217 145 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 144
    simpa using h
  have hprev := st217_p144
  have hstep := st217_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p146 : ((21483004329569/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT217 (i+1))
      = (∑ i ∈ Finset.range 145, stT217 (i+1)) + stT217 146 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 145
    simpa using h
  have hprev := st217_p145
  have hstep := st217_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p147 : ((4214570520127/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT217 (i+1))
      = (∑ i ∈ Finset.range 146, stT217 (i+1)) + stT217 147 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 146
    simpa using h
  have hprev := st217_p146
  have hstep := st217_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p148 : ((21074968413191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT217 (i+1))
      = (∑ i ∈ Finset.range 147, stT217 (i+1)) + stT217 148 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 147
    simpa using h
  have hprev := st217_p147
  have hstep := st217_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p149 : ((21482337581789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT217 (i+1))
      = (∑ i ∈ Finset.range 148, stT217 (i+1)) + stT217 149 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 148
    simpa using h
  have hprev := st217_p148
  have hstep := st217_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p150 : ((21572843713901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT217 (i+1))
      = (∑ i ∈ Finset.range 149, stT217 (i+1)) + stT217 150 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 149
    simpa using h
  have hprev := st217_p149
  have hstep := st217_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p151 : ((42381901692907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT217 (i+1))
      = (∑ i ∈ Finset.range 150, stT217 (i+1)) + stT217 151 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 150
    simpa using h
  have hprev := st217_p150
  have hstep := st217_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p152 : ((41999441559883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT217 (i+1))
      = (∑ i ∈ Finset.range 151, stT217 (i+1)) + stT217 152 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 151
    simpa using h
  have hprev := st217_p151
  have hstep := st217_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p153 : ((42648432870499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT217 (i+1))
      = (∑ i ∈ Finset.range 152, stT217 (i+1)) + stT217 153 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 152
    simpa using h
  have hprev := st217_p152
  have hstep := st217_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p154 : ((43224154010043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT217 (i+1))
      = (∑ i ∈ Finset.range 153, stT217 (i+1)) + stT217 154 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 153
    simpa using h
  have hprev := st217_p153
  have hstep := st217_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p155 : ((42764884059123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT217 (i+1))
      = (∑ i ∈ Finset.range 154, stT217 (i+1)) + stT217 155 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 154
    simpa using h
  have hprev := st217_p154
  have hstep := st217_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p156 : ((2101910193639/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT217 (i+1))
      = (∑ i ∈ Finset.range 155, stT217 (i+1)) + stT217 156 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 155
    simpa using h
  have hprev := st217_p155
  have hstep := st217_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p157 : ((2111746603589/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT217 (i+1))
      = (∑ i ∈ Finset.range 156, stT217 (i+1)) + stT217 157 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 156
    simpa using h
  have hprev := st217_p156
  have hstep := st217_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p158 : ((43029197882769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT217 (i+1))
      = (∑ i ∈ Finset.range 157, stT217 (i+1)) + stT217 158 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 157
    simpa using h
  have hprev := st217_p157
  have hstep := st217_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p159 : ((2696513726291/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT217 (i+1))
      = (∑ i ∈ Finset.range 158, stT217 (i+1)) + stT217 159 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 158
    simpa using h
  have hprev := st217_p158
  have hstep := st217_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p160 : ((21201575580603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT217 (i+1))
      = (∑ i ∈ Finset.range 159, stT217 (i+1)) + stT217 160 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 159
    simpa using h
  have hprev := st217_p159
  have hstep := st217_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p161 : ((41974726928607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT217 (i+1))
      = (∑ i ∈ Finset.range 160, stT217 (i+1)) + stT217 161 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 160
    simpa using h
  have hprev := st217_p160
  have hstep := st217_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p162 : ((42521053986921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT217 (i+1))
      = (∑ i ∈ Finset.range 161, stT217 (i+1)) + stT217 162 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 161
    simpa using h
  have hprev := st217_p161
  have hstep := st217_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p163 : ((43195390718281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT217 (i+1))
      = (∑ i ∈ Finset.range 162, stT217 (i+1)) + stT217 163 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 162
    simpa using h
  have hprev := st217_p162
  have hstep := st217_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p164 : ((5371506504123/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT217 (i+1))
      = (∑ i ∈ Finset.range 163, stT217 (i+1)) + stT217 164 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 163
    simpa using h
  have hprev := st217_p163
  have hstep := st217_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p165 : ((21097043541649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT217 (i+1))
      = (∑ i ∈ Finset.range 164, stT217 (i+1)) + stT217 165 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 164
    simpa using h
  have hprev := st217_p164
  have hstep := st217_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p166 : ((4202371572959/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT217 (i+1))
      = (∑ i ∈ Finset.range 165, stT217 (i+1)) + stT217 166 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 165
    simpa using h
  have hprev := st217_p165
  have hstep := st217_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p167 : ((42706907806007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT217 (i+1))
      = (∑ i ∈ Finset.range 166, stT217 (i+1)) + stT217 167 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 166
    simpa using h
  have hprev := st217_p166
  have hstep := st217_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p168 : ((43240624829939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT217 (i+1))
      = (∑ i ∈ Finset.range 167, stT217 (i+1)) + stT217 168 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 167
    simpa using h
  have hprev := st217_p167
  have hstep := st217_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p169 : ((8571162789053/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT217 (i+1))
      = (∑ i ∈ Finset.range 168, stT217 (i+1)) + stT217 169 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 168
    simpa using h
  have hprev := st217_p168
  have hstep := st217_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p170 : ((1052739596101/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT217 (i+1))
      = (∑ i ∈ Finset.range 169, stT217 (i+1)) + stT217 170 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 169
    simpa using h
  have hprev := st217_p169
  have hstep := st217_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p171 : ((1051500730583/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT217 (i+1))
      = (∑ i ∈ Finset.range 170, stT217 (i+1)) + stT217 171 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 170
    simpa using h
  have hprev := st217_p170
  have hstep := st217_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p172 : ((10692700919609/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT217 (i+1))
      = (∑ i ∈ Finset.range 171, stT217 (i+1)) + stT217 172 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 171
    simpa using h
  have hprev := st217_p171
  have hstep := st217_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p173 : ((10812666289759/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT217 (i+1))
      = (∑ i ∈ Finset.range 172, stT217 (i+1)) + stT217 173 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 172
    simpa using h
  have hprev := st217_p172
  have hstep := st217_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p174 : ((2677691224119/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT217 (i+1))
      = (∑ i ∈ Finset.range 173, stT217 (i+1)) + stT217 174 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 173
    simpa using h
  have hprev := st217_p173
  have hstep := st217_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p175 : ((42108826504133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT217 (i+1))
      = (∑ i ∈ Finset.range 174, stT217 (i+1)) + stT217 175 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 174
    simpa using h
  have hprev := st217_p174
  have hstep := st217_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p176 : ((42038072284519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT217 (i+1))
      = (∑ i ∈ Finset.range 175, stT217 (i+1)) + stT217 176 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 175
    simpa using h
  have hprev := st217_p175
  have hstep := st217_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p177 : ((42719593470949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT217 (i+1))
      = (∑ i ∈ Finset.range 176, stT217 (i+1)) + stT217 177 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 176
    simpa using h
  have hprev := st217_p176
  have hstep := st217_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p178 : ((5406070653787/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT217 (i+1))
      = (∑ i ∈ Finset.range 177, stT217 (i+1)) + stT217 178 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 177
    simpa using h
  have hprev := st217_p177
  have hstep := st217_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p179 : ((5366934157391/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT217 (i+1))
      = (∑ i ∈ Finset.range 178, stT217 (i+1)) + stT217 179 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 178
    simpa using h
  have hprev := st217_p178
  have hstep := st217_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p180 : ((2636994970621/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT217 (i+1))
      = (∑ i ∈ Finset.range 179, stT217 (i+1)) + stT217 180 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 179
    simpa using h
  have hprev := st217_p179
  have hstep := st217_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p181 : ((41973433167751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT217 (i+1))
      = (∑ i ∈ Finset.range 180, stT217 (i+1)) + stT217 181 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 180
    simpa using h
  have hprev := st217_p180
  have hstep := st217_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p182 : ((21276391874957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT217 (i+1))
      = (∑ i ∈ Finset.range 181, stT217 (i+1)) + stT217 182 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 181
    simpa using h
  have hprev := st217_p181
  have hstep := st217_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p183 : ((4319588827861/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT217 (i+1))
      = (∑ i ∈ Finset.range 182, stT217 (i+1)) + stT217 183 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 182
    simpa using h
  have hprev := st217_p182
  have hstep := st217_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p184 : ((4310225228767/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT217 (i+1))
      = (∑ i ∈ Finset.range 183, stT217 (i+1)) + stT217 184 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 183
    simpa using h
  have hprev := st217_p183
  have hstep := st217_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p185 : ((8478622925701/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT217 (i+1))
      = (∑ i ∈ Finset.range 184, stT217 (i+1)) + stT217 185 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 184
    simpa using h
  have hprev := st217_p184
  have hstep := st217_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p186 : ((41938715081057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT217 (i+1))
      = (∑ i ∈ Finset.range 185, stT217 (i+1)) + stT217 186 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 185
    simpa using h
  have hprev := st217_p185
  have hstep := st217_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p187 : ((42286206760193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT217 (i+1))
      = (∑ i ∈ Finset.range 186, stT217 (i+1)) + stT217 187 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 186
    simpa using h
  have hprev := st217_p186
  have hstep := st217_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p188 : ((43013057622509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT217 (i+1))
      = (∑ i ∈ Finset.range 187, stT217 (i+1)) + stT217 188 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 187
    simpa using h
  have hprev := st217_p187
  have hstep := st217_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p189 : ((43254105147821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT217 (i+1))
      = (∑ i ∈ Finset.range 188, stT217 (i+1)) + stT217 189 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 188
    simpa using h
  have hprev := st217_p188
  have hstep := st217_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p190 : ((42729975583447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT217 (i+1))
      = (∑ i ∈ Finset.range 189, stT217 (i+1)) + stT217 190 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 189
    simpa using h
  have hprev := st217_p189
  have hstep := st217_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p191 : ((21028404217911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT217 (i+1))
      = (∑ i ∈ Finset.range 190, stT217 (i+1)) + stT217 191 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 190
    simpa using h
  have hprev := st217_p190
  have hstep := st217_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p192 : ((21006014930243/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT217 (i+1))
      = (∑ i ∈ Finset.range 191, stT217 (i+1)) + stT217 192 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 191
    simpa using h
  have hprev := st217_p191
  have hstep := st217_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p193 : ((42641762172681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT217 (i+1))
      = (∑ i ∈ Finset.range 192, stT217 (i+1)) + stT217 193 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 192
    simpa using h
  have hprev := st217_p192
  have hstep := st217_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p194 : ((43227764517987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT217 (i+1))
      = (∑ i ∈ Finset.range 193, stT217 (i+1)) + stT217 194 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 193
    simpa using h
  have hprev := st217_p193
  have hstep := st217_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p195 : ((43113085861887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT217 (i+1))
      = (∑ i ∈ Finset.range 194, stT217 (i+1)) + stT217 195 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 194
    simpa using h
  have hprev := st217_p194
  have hstep := st217_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p196 : ((42430674874637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT217 (i+1))
      = (∑ i ∈ Finset.range 195, stT217 (i+1)) + stT217 196 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 195
    simpa using h
  have hprev := st217_p195
  have hstep := st217_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p197 : ((41936456541009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT217 (i+1))
      = (∑ i ∈ Finset.range 196, stT217 (i+1)) + stT217 197 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 196
    simpa using h
  have hprev := st217_p196
  have hstep := st217_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p198 : ((4216821209793/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT217 (i+1))
      = (∑ i ∈ Finset.range 197, stT217 (i+1)) + stT217 198 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 197
    simpa using h
  have hprev := st217_p197
  have hstep := st217_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p199 : ((21434790897427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT217 (i+1))
      = (∑ i ∈ Finset.range 198, stT217 (i+1)) + stT217 199 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 198
    simpa using h
  have hprev := st217_p198
  have hstep := st217_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p200 : ((21642621371629/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT217 (i+1))
      = (∑ i ∈ Finset.range 199, stT217 (i+1)) + stT217 200 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 199
    simpa using h
  have hprev := st217_p199
  have hstep := st217_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p201 : ((21487975671821/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT217 (i+1))
      = (∑ i ∈ Finset.range 200, stT217 (i+1)) + stT217 201 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 200
    simpa using h
  have hprev := st217_p200
  have hstep := st217_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p202 : ((2113644087287/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT217 (i+1))
      = (∑ i ∈ Finset.range 201, stT217 (i+1)) + stT217 202 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 201
    simpa using h
  have hprev := st217_p201
  have hstep := st217_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p203 : ((20956235442031/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT217 (i+1))
      = (∑ i ∈ Finset.range 202, stT217 (i+1)) + stT217 203 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 202
    simpa using h
  have hprev := st217_p202
  have hstep := st217_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p204 : ((21132322752451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT217 (i+1))
      = (∑ i ∈ Finset.range 203, stT217 (i+1)) + stT217 204 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 203
    simpa using h
  have hprev := st217_p203
  have hstep := st217_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p205 : ((10740733430903/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT217 (i+1))
      = (∑ i ∈ Finset.range 204, stT217 (i+1)) + stT217 205 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 204
    simpa using h
  have hprev := st217_p204
  have hstep := st217_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p206 : ((43295319258791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT217 (i+1))
      = (∑ i ∈ Finset.range 205, stT217 (i+1)) + stT217 206 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 205
    simpa using h
  have hprev := st217_p205
  have hstep := st217_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p207 : ((2146496634727/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT217 (i+1))
      = (∑ i ∈ Finset.range 206, stT217 (i+1)) + stT217 207 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 206
    simpa using h
  have hprev := st217_p206
  have hstep := st217_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p208 : ((2111840142151/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT217 (i+1))
      = (∑ i ∈ Finset.range 207, stT217 (i+1)) + stT217 208 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 207
    simpa using h
  have hprev := st217_p207
  have hstep := st217_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p209 : ((130950629279/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT217 (i+1))
      = (∑ i ∈ Finset.range 208, stT217 (i+1)) + stT217 209 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 208
    simpa using h
  have hprev := st217_p208
  have hstep := st217_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p210 : ((4225554796403/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT217 (i+1))
      = (∑ i ∈ Finset.range 209, stT217 (i+1)) + stT217 210 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 209
    simpa using h
  have hprev := st217_p209
  have hstep := st217_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p211 : ((21471965263891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT217 (i+1))
      = (∑ i ∈ Finset.range 210, stT217 (i+1)) + stT217 211 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 210
    simpa using h
  have hprev := st217_p210
  have hstep := st217_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p212 : ((270644674319/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT217 (i+1))
      = (∑ i ∈ Finset.range 211, stT217 (i+1)) + stT217 212 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 211
    simpa using h
  have hprev := st217_p211
  have hstep := st217_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p213 : ((42992360549609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT217 (i+1))
      = (∑ i ∈ Finset.range 212, stT217 (i+1)) + stT217 213 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 212
    simpa using h
  have hprev := st217_p212
  have hstep := st217_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p214 : ((42311131554137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT217 (i+1))
      = (∑ i ∈ Finset.range 213, stT217 (i+1)) + stT217 214 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 213
    simpa using h
  have hprev := st217_p213
  have hstep := st217_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p215 : ((1309446132301/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT217 (i+1))
      = (∑ i ∈ Finset.range 214, stT217 (i+1)) + stT217 215 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 214
    simpa using h
  have hprev := st217_p214
  have hstep := st217_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p216 : ((21072289053531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT217 (i+1))
      = (∑ i ∈ Finset.range 215, stT217 (i+1)) + stT217 216 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 215
    simpa using h
  have hprev := st217_p215
  have hstep := st217_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p217 : ((21404632407721/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT217 (i+1))
      = (∑ i ∈ Finset.range 216, stT217 (i+1)) + stT217 217 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 216
    simpa using h
  have hprev := st217_p216
  have hstep := st217_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p218 : ((21642157611791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT217 (i+1))
      = (∑ i ∈ Finset.range 217, stT217 (i+1)) + stT217 218 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 217
    simpa using h
  have hprev := st217_p217
  have hstep := st217_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p219 : ((21569823237581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT217 (i+1))
      = (∑ i ∈ Finset.range 218, stT217 (i+1)) + stT217 219 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 218
    simpa using h
  have hprev := st217_p218
  have hstep := st217_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p220 : ((21255091508081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT217 (i+1))
      = (∑ i ∈ Finset.range 219, stT217 (i+1)) + stT217 220 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 219
    simpa using h
  have hprev := st217_p219
  have hstep := st217_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p221 : ((10490440534171/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT217 (i+1))
      = (∑ i ∈ Finset.range 220, stT217 (i+1)) + stT217 221 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 220
    simpa using h
  have hprev := st217_p220
  have hstep := st217_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p222 : ((10494883251313/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT217 (i+1))
      = (∑ i ∈ Finset.range 221, stT217 (i+1)) + stT217 222 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 221
    simpa using h
  have hprev := st217_p221
  have hstep := st217_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p223 : ((42543645992501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT217 (i+1))
      = (∑ i ∈ Finset.range 222, stT217 (i+1)) + stT217 223 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 222
    simpa using h
  have hprev := st217_p222
  have hstep := st217_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p224 : ((4315851579521/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT217 (i+1))
      = (∑ i ∈ Finset.range 223, stT217 (i+1)) + stT217 224 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 223
    simpa using h
  have hprev := st217_p223
  have hstep := st217_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p225 : ((2705774853833/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT217 (i+1))
      = (∑ i ∈ Finset.range 224, stT217 (i+1)) + stT217 225 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 224
    simpa using h
  have hprev := st217_p224
  have hstep := st217_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p226 : ((21417038535591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT217 (i+1))
      = (∑ i ∈ Finset.range 225, stT217 (i+1)) + stT217 226 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 225
    simpa using h
  have hprev := st217_p225
  have hstep := st217_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p227 : ((843550186867/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT217 (i+1))
      = (∑ i ∈ Finset.range 226, stT217 (i+1)) + stT217 227 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 226
    simpa using h
  have hprev := st217_p226
  have hstep := st217_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p228 : ((41877761338747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT217 (i+1))
      = (∑ i ∈ Finset.range 227, stT217 (i+1)) + stT217 228 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 227
    simpa using h
  have hprev := st217_p227
  have hstep := st217_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p229 : ((42182907266607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT217 (i+1))
      = (∑ i ∈ Finset.range 228, stT217 (i+1)) + stT217 229 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 228
    simpa using h
  have hprev := st217_p228
  have hstep := st217_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p230 : ((42835314323107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT217 (i+1))
      = (∑ i ∈ Finset.range 229, stT217 (i+1)) + stT217 230 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 229
    simpa using h
  have hprev := st217_p229
  have hstep := st217_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p231 : ((43295462882173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT217 (i+1))
      = (∑ i ∈ Finset.range 230, stT217 (i+1)) + stT217 231 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 230
    simpa using h
  have hprev := st217_p230
  have hstep := st217_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p232 : ((2699314725013/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT217 (i+1))
      = (∑ i ∈ Finset.range 231, stT217 (i+1)) + stT217 232 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 231
    simpa using h
  have hprev := st217_p231
  have hstep := st217_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p233 : ((21303156548897/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT217 (i+1))
      = (∑ i ∈ Finset.range 232, stT217 (i+1)) + stT217 233 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 232
    simpa using h
  have hprev := st217_p232
  have hstep := st217_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p234 : ((21009485464067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT217 (i+1))
      = (∑ i ∈ Finset.range 233, stT217 (i+1)) + stT217 234 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 233
    simpa using h
  have hprev := st217_p233
  have hstep := st217_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p235 : ((4189525281931/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT217 (i+1))
      = (∑ i ∈ Finset.range 234, stT217 (i+1)) + stT217 235 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 234
    simpa using h
  have hprev := st217_p234
  have hstep := st217_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p236 : ((21164823964887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT217 (i+1))
      = (∑ i ∈ Finset.range 235, stT217 (i+1)) + stT217 236 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 235
    simpa using h
  have hprev := st217_p235
  have hstep := st217_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p237 : ((214886191713/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT217 (i+1))
      = (∑ i ∈ Finset.range 236, stT217 (i+1)) + stT217 237 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 236
    simpa using h
  have hprev := st217_p236
  have hstep := st217_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p238 : ((5416533363017/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT217 (i+1))
      = (∑ i ∈ Finset.range 237, stT217 (i+1)) + stT217 238 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 237
    simpa using h
  have hprev := st217_p237
  have hstep := st217_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p239 : ((43122522236457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT217 (i+1))
      = (∑ i ∈ Finset.range 238, stT217 (i+1)) + stT217 239 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 238
    simpa using h
  have hprev := st217_p238
  have hstep := st217_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p240 : ((8502556448733/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT217 (i+1))
      = (∑ i ∈ Finset.range 239, stT217 (i+1)) + stT217 240 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 239
    simpa using h
  have hprev := st217_p239
  have hstep := st217_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p241 : ((10492410969219/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT217 (i+1))
      = (∑ i ∈ Finset.range 240, stT217 (i+1)) + stT217 241 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 240
    simpa using h
  have hprev := st217_p240
  have hstep := st217_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p242 : ((20951273544513/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT217 (i+1))
      = (∑ i ∈ Finset.range 241, stT217 (i+1)) + stT217 242 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 241
    simpa using h
  have hprev := st217_p241
  have hstep := st217_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p243 : ((21179176683513/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT217 (i+1))
      = (∑ i ∈ Finset.range 242, stT217 (i+1)) + stT217 243 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 242
    simpa using h
  have hprev := st217_p242
  have hstep := st217_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p244 : ((21497293395781/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT217 (i+1))
      = (∑ i ∈ Finset.range 243, stT217 (i+1)) + stT217 244 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 243
    simpa using h
  have hprev := st217_p243
  have hstep := st217_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p245 : ((21670347973967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT217 (i+1))
      = (∑ i ∈ Finset.range 244, stT217 (i+1)) + stT217 245 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 244
    simpa using h
  have hprev := st217_p244
  have hstep := st217_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p246 : ((21572675003029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT217 (i+1))
      = (∑ i ∈ Finset.range 245, stT217 (i+1)) + stT217 246 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 245
    simpa using h
  have hprev := st217_p245
  have hstep := st217_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p247 : ((10638554265557/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT217 (i+1))
      = (∑ i ∈ Finset.range 246, stT217 (i+1)) + stT217 247 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 246
    simpa using h
  have hprev := st217_p246
  have hstep := st217_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p248 : ((20998101156733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT217 (i+1))
      = (∑ i ∈ Finset.range 247, stT217 (i+1)) + stT217 248 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 247
    simpa using h
  have hprev := st217_p247
  have hstep := st217_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p249 : ((20935157054833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT217 (i+1))
      = (∑ i ∈ Finset.range 248, stT217 (i+1)) + stT217 249 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 248
    simpa using h
  have hprev := st217_p248
  have hstep := st217_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_p250 : ((42262944071031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT217 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT217 (i+1))
      = (∑ i ∈ Finset.range 249, stT217 (i+1)) + stT217 250 := by
    have h := Finset.sum_range_succ (fun i => stT217 (i+1)) 249
    simpa using h
  have hprev := st217_p249
  have hstep := st217_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st217_s250 :
    |Real.sin (((217 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))
      - ((-783927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -1126207/5000000) (δ := 1093/100000000) (ψ := -515201/500000) 217 191
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 217`** (evaluated boundary). -/
theorem station_217_sign : 0 < hardyG ((((217:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 217 250 (by norm_num) (by norm_num)
    ((-515201/500000 : ℚ) : ℝ)
  have hchain := st217_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT217 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((217 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-515201/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st217_c250
  have hsinb := abs_le.mp st217_s250
  have hbdy_lo : ((8590806142413/150685600000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((217 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-515201/500000 : ℚ) : ℝ))) / 2
          - ((((217:ℕ)):ℝ))
            * Real.sin (((217 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-515201/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((217:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((217:ℝ) * Real.log (250:ℝ) - ((-515201/500000 : ℚ) : ℝ))) / 2
        - ((217:ℝ)) * Real.sin ((217:ℝ) * Real.log (250:ℝ) - ((-515201/500000 : ℚ) : ℝ))
        ≥ ((67916343/400000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((217:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((67916343/400000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((67916343/400000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((67916343/400000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((217:ℕ)):ℝ))+1) * (((((217:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((326297569147/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((42262944071031/10000000000000 : ℚ) : ℝ) + ((8590806142413/150685600000000 : ℚ) : ℝ)
      - ((326297569147/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-515201/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((217:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-515201/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((217:ℕ)):ℝ)))).re
      - Real.sin ((-515201/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((217:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((217:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((217:ℕ)):ℝ))
      = (((((217:ℕ)):ℝ)) * (Real.log ((((217:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((217:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_217
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
  have hθwin : |(((-515201/500000 : ℚ) : ℝ) + ((44:ℤ)) * (2*Real.pi)) - theta ((((217:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((217:ℕ)):ℝ)))
    (φ := ((-515201/500000 : ℚ) : ℝ) + ((44:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-515201/500000 : ℚ)) : ℝ) 44).1,
    (cos_sin_shift (((-515201/500000 : ℚ)) : ℝ) 44).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_217_sign
end AxiomAudit
