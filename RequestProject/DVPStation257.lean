import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 257` (rung-262.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT257 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((257 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-17679/25000 : ℚ) : ℝ))

theorem st257_c1 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((76021/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 17679/100000) (δ := 1/1000000000) (ψ := -17679/25000) 257 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t1 : ((4751/6250 : ℚ) : ℝ) ≤ stT257 1 := by
  have hc : ((4751/6250 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4751/6250 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((4751/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c2 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-487419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1822993/2500000) (δ := 13/1000000) (ψ := -17679/25000) 257 28
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t2 : ((-215421854387/312500000000 : ℚ) : ℝ) ≤ stT257 2 := by
  have hc : ((-121861/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215421854387/312500000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-121861/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c3 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((953193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 191981/2500000) (δ := 521/40000000) (ψ := -17679/25000) 257 45
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t3 : ((2751486508393/5000000000000 : ℚ) : ℝ) ≤ stT257 3 := by
  have hc : ((953143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2751486508393/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((953143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c4 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((402313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1445943/5000000) (δ := 13011/1000000000) (ψ := -17679/25000) 257 57
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t4 : ((402263/2000000 : ℚ) : ℝ) ≤ stT257 4 := by
  have hc : ((402263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((402263/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((402263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c5 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((936769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -893793/10000000) (δ := 101/7812500) (ψ := -17679/25000) 257 66
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t5 : ((837826765013/2000000000000 : ℚ) : ℝ) ≤ stT257 5 := by
  have hc : ((936719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((837826765013/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((936719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c6 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-811091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1573007/2500000) (δ := 12877/1000000000) (ψ := -17679/25000) 257 73
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t6 : ((-3311469343103/10000000000000 : ℚ) : ℝ) ≤ stT257 6 := by
  have hc : ((-811141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3311469343103/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-811141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c7 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-137197/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -462189/1000000) (δ := 3219/250000000) (ψ := -17679/25000) 257 80
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t7 : ((-51865044619/500000000000 : ℚ) : ℝ) ≤ stT257 7 := by
  have hc : ((-68611/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51865044619/500000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-68611/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c8 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((99013/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1316109/5000000) (δ := 12891/1000000000) (ψ := -17679/25000) 257 85
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t8 : ((350028373599/2000000000000 : ℚ) : ℝ) ≤ stT257 8 := by
  have hc : ((99003/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((350028373599/2000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((99003/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c9 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((62231/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -232021/10000000) (δ := 2591/200000000) (ψ := -17679/25000) 257 90
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t9 : ((1659409834059/5000000000000 : ℚ) : ℝ) ≤ stT257 9 := by
  have hc : ((497823/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1659409834059/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((497823/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c10 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-277607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4630247/10000000) (δ := 13027/1000000000) (ψ := -17679/25000) 257 94
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t10 : ((-439014311323/5000000000000 : ℚ) : ℝ) ≤ stT257 10 := by
  have hc : ((-277657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-439014311323/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-277657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c11 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((873/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1517599/5000000) (δ := 2581/200000000) (ψ := -17679/25000) 257 98
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t11 : ((21054534079/200000000000 : ℚ) : ℝ) ≤ stT257 11 := by
  have hc : ((6983/20000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21054534079/200000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((6983/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c12 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((14063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3891831/10000000) (δ := 12969/1000000000) (ψ := -17679/25000) 257 102
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t12 : ((40452041763/10000000000000 : ℚ) : ℝ) ≤ stT257 12 := by
  have hc : ((14013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40452041763/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((14013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c13 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((98647/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 205857/5000000) (δ := 3237/250000000) (ψ := -17679/25000) 257 105
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t13 : ((273583587/1000000000 : ℚ) : ℝ) ≤ stT257 13 := by
  have hc : ((49321/50000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((273583587/1000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((49321/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c14 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((29237/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 451107/5000000) (δ := 6513/500000000) (ψ := -17679/25000) 257 108
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t14 : ((312539924351/1250000000000 : ℚ) : ℝ) ≤ stT257 14 := by
  have hc : ((467767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((312539924351/1250000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((467767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c15 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((4541/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1893737/10000000) (δ := 6449/500000000) (ψ := -17679/25000) 257 111
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t15 : ((46896002547/250000000000 : ℚ) : ℝ) ≤ stT257 15 := by
  have hc : ((72651/100000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46896002547/250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((72651/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c16 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-124087/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7551641/10000000) (δ := 12983/1000000000) (ψ := -17679/25000) 257 114
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t16 : ((-1240932996373/5000000000000 : ℚ) : ℝ) ≤ stT257 16 := by
  have hc : ((-496373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1240932996373/5000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-496373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c17 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((999979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8131/5000000) (δ := 12969/1000000000) (ψ := -17679/25000) 257 116
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t17 : ((606295949931/2500000000000 : ℚ) : ℝ) ≤ stT257 17 := by
  have hc : ((999929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((606295949931/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((999929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c18 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-103861/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1323021/2500000) (δ := 12949/1000000000) (ψ := -17679/25000) 257 118
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t18 : ((-244826336033/2000000000000 : ℚ) : ℝ) ≤ stT257 18 := by
  have hc : ((-103871/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244826336033/2000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-103871/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c19 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-190821/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -709363/1000000) (δ := 1287/100000000) (ψ := -17679/25000) 257 121
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t19 : ((-218898232649/1000000000000 : ℚ) : ℝ) ≤ stT257 19 := by
  have hc : ((-190831/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218898232649/1000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-190831/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c20 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-302851/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5553611/10000000) (δ := 2597/200000000) (ψ := -17679/25000) 257 123
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t20 : ((-42328208223/312500000000 : ℚ) : ℝ) ≤ stT257 20 := by
  have hc : ((-75719/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42328208223/312500000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-75719/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c21 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-156797/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2810917/5000000) (δ := 12999/1000000000) (ψ := -17679/25000) 257 125
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t21 : ((-684372795801/5000000000000 : ℚ) : ℝ) ≤ stT257 21 := by
  have hc : ((-313619/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-684372795801/5000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-313619/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c22 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-192093/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7148661/10000000) (δ := 1289/100000000) (ψ := -17679/25000) 257 127
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t22 : ((-51195641603/250000000000 : ℚ) : ℝ) ≤ stT257 22 := by
  have hc : ((-192103/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51195641603/250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-192103/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c23 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-652339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5703657/10000000) (δ := 12983/1000000000) (ψ := -17679/25000) 257 128
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t23 : ((-272065132281/2000000000000 : ℚ) : ℝ) ≤ stT257 23 := by
  have hc : ((-652389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-272065132281/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-652389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c24 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((9929/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 816137/5000000) (δ := 2587/200000000) (ψ := -17679/25000) 257 130
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t24 : ((162129648907/1000000000000 : ℚ) : ℝ) ≤ stT257 24 := by
  have hc : ((79427/100000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162129648907/1000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((79427/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c25 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((148043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1777759/5000000) (δ := 6477/500000000) (ψ := -17679/25000) 257 132
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t25 : ((147993/5000000 : ℚ) : ℝ) ≤ stT257 25 := by
  have hc : ((147993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147993/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((147993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c26 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-179953/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5935819/10000000) (δ := 3239/250000000) (ψ := -17679/25000) 257 133
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t26 : ((-352941499911/2500000000000 : ℚ) : ℝ) ≤ stT257 26 := by
  have hc : ((-359931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-352941499911/2500000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-359931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c27 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((440509/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -246393/2000000) (δ := 12871/1000000000) (ψ := -17679/25000) 257 135
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t27 : ((423855729/2500000000 : ℚ) : ℝ) ≤ stT257 27 := by
  have hc : ((110121/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((423855729/2500000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((110121/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c28 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-420663/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6426319/10000000) (δ := 6439/500000000) (ψ := -17679/25000) 257 136
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t28 : ((-49689116139/312500000000 : ℚ) : ℝ) ≤ stT257 28 := by
  have hc : ((-26293/31250 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49689116139/312500000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-26293/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c29 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((279599/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2443447/10000000) (δ := 203/15625000) (ψ := -17679/25000) 257 138
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t29 : ((259577889011/2500000000000 : ℚ) : ℝ) ≤ stT257 29 := by
  have hc : ((139787/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((259577889011/2500000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((139787/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c30 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((118397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3630303/10000000) (δ := 1613/125000000) (ψ := -17679/25000) 257 139
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t30 : ((216070970127/10000000000000 : ℚ) : ℝ) ≤ stT257 30 := by
  have hc : ((118347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216070970127/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((118347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c31 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-224637/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6718113/10000000) (δ := 12989/1000000000) (ψ := -17679/25000) 257 141
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t31 : ((-403482633073/2500000000000 : ℚ) : ℝ) ≤ stT257 31 := by
  have hc : ((-449299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-403482633073/2500000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-449299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c32 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((688763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -126721/625000) (δ := 12921/1000000000) (ψ := -17679/25000) 257 142
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t32 : ((608741712579/5000000000000 : ℚ) : ℝ) ≤ stT257 32 := by
  have hc : ((688713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((608741712579/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((688713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c33 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((343261/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1017627/5000000) (δ := 3257/250000000) (ψ := -17679/25000) 257 143
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t33 : ((18671780973/156250000000 : ℚ) : ℝ) ≤ stT257 33 := by
  have hc : ((85809/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18671780973/156250000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((85809/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c34 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-118207/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5507843/10000000) (δ := 2587/200000000) (ψ := -17679/25000) 257 144
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t34 : ((-101370249981/1000000000000 : ℚ) : ℝ) ≤ stT257 34 := by
  have hc : ((-118217/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101370249981/1000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-118217/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c35 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-974087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1456723/2000000) (δ := 12853/1000000000) (ψ := -17679/25000) 257 146
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t35 : ((-1646592538333/10000000000000 : ℚ) : ℝ) ≤ stT257 35 := by
  have hc : ((-974137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1646592538333/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-974137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c36 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-188203/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -195671/400000) (δ := 12857/1000000000) (ψ := -17679/25000) 257 147
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t36 : ((-78428349019/1250000000000 : ℚ) : ℝ) ≤ stT257 36 := by
  have hc : ((-47057/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78428349019/1250000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-47057/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c37 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((363893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2995881/10000000) (δ := 12939/1000000000) (ψ := -17679/25000) 257 148
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t37 : ((598153889727/10000000000000 : ℚ) : ℝ) ≤ stT257 37 := by
  have hc : ((363843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((598153889727/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((363843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c38 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((202329/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -784763/5000000) (δ := 1629/125000000) (ψ := -17679/25000) 257 149
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t38 : ((328200658731/2500000000000 : ℚ) : ℝ) ≤ stT257 38 := by
  have hc : ((404633/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((328200658731/2500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((404633/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c39 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((486223/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58823/1000000) (δ := 6439/500000000) (ψ := -17679/25000) 257 150
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t39 : ((389269809819/2500000000000 : ℚ) : ℝ) ≤ stT257 39 := by
  have hc : ((243099/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((389269809819/2500000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((243099/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c40 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((99993/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29507/10000000) (δ := 12917/1000000000) (ψ := -17679/25000) 257 151
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t40 : ((19761853293/125000000000 : ℚ) : ℝ) ≤ stT257 40 := by
  have hc : ((24997/25000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19761853293/125000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((24997/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c41 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((998699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5101/400000) (δ := 1301/100000000) (ψ := -17679/25000) 257 152
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t41 : ((1559627093313/10000000000000 : ℚ) : ℝ) ≤ stT257 41 := by
  have hc : ((998649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1559627093313/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((998649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c42 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((249809/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9773/1000000) (δ := 12903/1000000000) (ψ := -17679/25000) 257 153
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t42 : ((770888485569/5000000000000 : ℚ) : ℝ) ≤ stT257 42 := by
  have hc : ((499593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((770888485569/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((499593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c43 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((481221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -687347/10000000) (δ := 403/31250000) (ψ := -17679/25000) 257 154
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t43 : ((36690834103/250000000000 : ℚ) : ℝ) ≤ stT257 43 := by
  have hc : ((120299/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36690834103/250000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((120299/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c44 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((796191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -406139/2500000) (δ := 6507/500000000) (ψ := -17679/25000) 257 155
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t44 : ((300056785349/2500000000000 : ℚ) : ℝ) ≤ stT257 44 := by
  have hc : ((796141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((300056785349/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((796141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c45 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((12551/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1446873/5000000) (δ := 12981/1000000000) (ψ := -17679/25000) 257 156
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t45 : ((299321352401/5000000000000 : ℚ) : ℝ) ≤ stT257 45 := by
  have hc : ((200791/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((299321352401/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((200791/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c46 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-54877/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2240133/5000000) (δ := 6487/500000000) (ψ := -17679/25000) 257 157
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t46 : ((-8093017659/250000000000 : ℚ) : ℝ) ≤ stT257 46 := by
  have hc : ((-109779/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8093017659/250000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-109779/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c47 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-829033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6370431/10000000) (δ := 1617/125000000) (ψ := -17679/25000) 257 158
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t47 : ((-24186838359/200000000000 : ℚ) : ℝ) ≤ stT257 47 := by
  have hc : ((-829083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24186838359/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-829083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c48 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-24033/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3578189/5000000) (δ := 12967/1000000000) (ψ := -17679/25000) 257 158
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t48 : ((-8672614907/62500000000 : ℚ) : ℝ) ≤ stT257 48 := by
  have hc : ((-96137/100000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8672614907/62500000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-96137/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c49 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-302871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4696251/10000000) (δ := 643/50000000) (ψ := -17679/25000) 257 159
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t49 : ((-108186114703/2500000000000 : ℚ) : ℝ) ≤ stT257 49 := by
  have hc : ((-302921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108186114703/2500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-302921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c50 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((141133/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1968587/10000000) (δ := 259/20000000) (ψ := -17679/25000) 257 160
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t50 : ((199577981199/2000000000000 : ℚ) : ℝ) ≤ stT257 50 := by
  have hc : ((141123/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199577981199/2000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((141123/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c51 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((918517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -508103/5000000) (δ := 12857/1000000000) (ψ := -17679/25000) 257 161
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t51 : ((32152774269/250000000000 : ℚ) : ℝ) ≤ stT257 51 := by
  have hc : ((918467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32152774269/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((918467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c52 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-128067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -106201/250000) (δ := 2573/200000000) (ψ := -17679/25000) 257 162
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t52 : ((-177666377867/10000000000000 : ℚ) : ℝ) ≤ stT257 52 := by
  have hc : ((-128117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177666377867/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-128117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c53 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-998511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1543507/2000000) (δ := 12931/1000000000) (ψ := -17679/25000) 257 163
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t53 : ((-685814690483/5000000000000 : ℚ) : ℝ) ≤ stT257 53 := by
  have hc : ((-998561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-685814690483/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-998561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c54 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-145541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4292139/10000000) (δ := 13031/1000000000) (ψ := -17679/25000) 257 163
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t54 : ((-49531077337/2500000000000 : ℚ) : ℝ) ≤ stT257 54 := by
  have hc : ((-145591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49531077337/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-145591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c55 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((494431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 373473/10000000) (δ := 12879/1000000000) (ψ := -17679/25000) 257 164
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t55 : ((333328277997/2500000000000 : ℚ) : ℝ) ≤ stT257 55 := by
  have hc : ((247203/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((333328277997/2500000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((247203/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c56 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((67703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -939401/2500000) (δ := 6443/500000000) (ψ := -17679/25000) 257 165
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t56 : ((45202554909/5000000000000 : ℚ) : ℝ) ≤ stT257 56 := by
  have hc : ((67653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45202554909/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((67653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c57 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-995411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7614389/10000000) (δ := 6443/500000000) (ψ := -17679/25000) 257 165
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t57 : ((-1318520944713/10000000000000 : ℚ) : ℝ) ≤ stT257 57 := by
  have hc : ((-995461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1318520944713/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-995461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c58 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((41513/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3080657/10000000) (δ := 1291/100000000) (ψ := -17679/25000) 257 166
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t58 : ((27250509591/625000000000 : ℚ) : ℝ) ≤ stT257 58 := by
  have hc : ((166027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27250509591/625000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((166027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c59 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((12366/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -822077/5000000) (δ := 129/10000000) (ψ := -17679/25000) 257 167
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t59 : ((515140552743/5000000000000 : ℚ) : ℝ) ≤ stT257 59 := by
  have hc : ((395687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((515140552743/5000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((395687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c60 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-173547/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1638389/2500000) (δ := 2599/200000000) (ψ := -17679/25000) 257 168
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t60 : ((-44812243843/400000000000 : ℚ) : ℝ) ≤ stT257 60 := by
  have hc : ((-173557/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44812243843/400000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-173557/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c61 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-55783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 101663/250000) (δ := 813/62500000) (ψ := -17679/25000) 257 168
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t61 : ((-71486842377/10000000000000 : ℚ) : ℝ) ≤ stT257 61 := by
  have hc : ((-55833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71486842377/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-55833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c62 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((888087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -149259/1250000) (δ := 2603/200000000) (ψ := -17679/25000) 257 169
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t62 : ((1127807878037/10000000000000 : ℚ) : ℝ) ≤ stT257 62 := by
  have hc : ((888037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1127807878037/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((888037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c63 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-880973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6621779/10000000) (δ := 12981/1000000000) (ψ := -17679/25000) 257 170
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t63 : ((-554992509643/5000000000000 : ℚ) : ℝ) ≤ stT257 63 := by
  have hc : ((-881023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-554992509643/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-881023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c64 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((34269/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 437063/1250000) (δ := 12881/1000000000) (ψ := -17679/25000) 257 170
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t64 : ((34259/1600000 : ℚ) : ℝ) ≤ stT257 64 := by
  have hc : ((34259/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34259/1600000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((34259/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c65 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((621607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2250011/10000000) (δ := 6487/500000000) (ψ := -17679/25000) 257 171
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t65 : ((770946360279/10000000000000 : ℚ) : ℝ) ≤ stT257 65 := by
  have hc : ((621557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((770946360279/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((621557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c66 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-124133/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3779679/5000000) (δ := 6437/500000000) (ψ := -17679/25000) 257 171
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t66 : ((-122243891931/1000000000000 : ℚ) : ℝ) ≤ stT257 66 := by
  have hc : ((-496557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122243891931/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-496557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c67 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((205583/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 756623/5000000) (δ := 3259/250000000) (ψ := -17679/25000) 257 172
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t67 : ((251144246427/2500000000000 : ℚ) : ℝ) ≤ stT257 67 := by
  have hc : ((411141/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((251144246427/2500000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((411141/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c68 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-73787/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -292251/625000) (δ := 12859/1000000000) (ψ := -17679/25000) 257 173
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t68 : ((-178990207721/5000000000000 : ℚ) : ℝ) ≤ stT257 68 := by
  have hc : ((-147599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178990207721/5000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-147599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c69 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-61143/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4703713/10000000) (δ := 12859/1000000000) (ψ := -17679/25000) 257 173
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t69 : ((-73619589427/2000000000000 : ℚ) : ℝ) ≤ stT257 69 := by
  have hc : ((-61153/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73619589427/2000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-61153/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c70 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((381193/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -175951/1000000) (δ := 13051/1000000000) (ψ := -17679/25000) 257 174
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t70 : ((7118479161/78125000000 : ℚ) : ℝ) ≤ stT257 70 := by
  have hc : ((23823/31250 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7118479161/78125000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((23823/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c71 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-245019/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1470819/2000000) (δ := 3213/250000000) (ψ := -17679/25000) 257 174
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t71 : ((-290798973633/2500000000000 : ℚ) : ℝ) ≤ stT257 71 := by
  have hc : ((-490063/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-290798973633/2500000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-490063/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c72 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((968183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 632329/10000000) (δ := 2609/200000000) (ψ := -17679/25000) 257 175
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t72 : ((1140955389963/10000000000000 : ℚ) : ℝ) ≤ stT257 72 := by
  have hc : ((968133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1140955389963/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((968133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c73 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-396153/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6213439/10000000) (δ := 6519/500000000) (ψ := -17679/25000) 257 176
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t73 : ((-57961435667/625000000000 : ℚ) : ℝ) ≤ stT257 73 := by
  have hc : ((-198089/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57961435667/625000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-198089/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c74 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((53079/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2528159/10000000) (δ := 6519/500000000) (ψ := -17679/25000) 257 176
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t74 : ((7712156403/125000000000 : ℚ) : ℝ) ≤ stT257 74 := by
  have hc : ((26537/50000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7712156403/125000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((26537/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c75 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-248749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2277731/5000000) (δ := 1609/125000000) (ψ := -17679/25000) 257 177
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t75 : ((-287288454099/10000000000000 : ℚ) : ℝ) ≤ stT257 75 := by
  have hc : ((-248799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-287288454099/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-248799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c76 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-2207/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3954579/10000000) (δ := 1609/125000000) (ψ := -17679/25000) 257 177
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t76 : ((-2543074143/2000000000000 : ℚ) : ℝ) ≤ stT257 76 := by
  have hc : ((-2217/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2543074143/2000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-2217/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c77 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((226977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10483/31250) (δ := 12879/1000000000) (ψ := -17679/25000) 257 178
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t77 : ((51721428767/2000000000000 : ℚ) : ℝ) ≤ stT257 77 := by
  have hc : ((226927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51721428767/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((226927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c78 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-392689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2467937/5000000) (δ := 407/31250000) (ψ := -17679/25000) 257 178
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t78 : ((-222344864721/5000000000000 : ℚ) : ℝ) ≤ stT257 78 := by
  have hc : ((-392739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222344864721/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-392739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c79 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((510601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2587281/10000000) (δ := 12987/1000000000) (ψ := -17679/25000) 257 179
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t79 : ((574414292937/10000000000000 : ℚ) : ℝ) ≤ stT257 79 := by
  have hc : ((510551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((574414292937/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((510551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c80 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-586753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2747299/5000000) (δ := 12987/1000000000) (ψ := -17679/25000) 257 179
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t80 : ((-328032852651/5000000000000 : ℚ) : ℝ) ≤ stT257 80 := by
  have hc : ((-586803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-328032852651/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-586803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c81 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((313631/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2231909/10000000) (δ := 6497/500000000) (ψ := -17679/25000) 257 180
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t81 : ((174225538133/2500000000000 : ℚ) : ℝ) ≤ stT257 81 := by
  have hc : ((156803/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174225538133/2500000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((156803/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c82 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-318213/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 565163/1000000) (δ := 6447/500000000) (ψ := -17679/25000) 257 180
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t82 : ((-43929414401/625000000000 : ℚ) : ℝ) ≤ stT257 82 := by
  have hc : ((-159119/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43929414401/625000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-159119/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c83 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((615849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1134167/5000000) (δ := 6451/500000000) (ψ := -17679/25000) 257 181
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t83 : ((337963422979/5000000000000 : ℚ) : ℝ) ≤ stT257 83 := by
  have hc : ((615799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((337963422979/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((615799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c84 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-564429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5426343/10000000) (δ := 25901/1000000000) (ψ := -17679/25000) 257 181
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t84 : ((-61589739211/1000000000000 : ℚ) : ℝ) ≤ stT257 84 := by
  have hc : ((-564479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61589739211/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-564479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c85 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((119769/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2677987/10000000) (δ := 2599/200000000) (ψ := -17679/25000) 257 182
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t85 : ((64947063619/1250000000000 : ℚ) : ℝ) ≤ stT257 85 := by
  have hc : ((239513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64947063619/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((239513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c86 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-5561/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4836693/10000000) (δ := 2599/200000000) (ψ := -17679/25000) 257 182
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t86 : ((-23989697807/625000000000 : ℚ) : ℝ) ≤ stT257 86 := by
  have hc : ((-177977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23989697807/625000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-177977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c87 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((38447/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53803/156250) (δ := 3247/250000000) (ψ := -17679/25000) 257 183
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t87 : ((2575548059/125000000000 : ℚ) : ℝ) ≤ stT257 87 := by
  have hc : ((38437/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2575548059/125000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((38437/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c88 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((10977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 974887/2500000) (δ := 1611/125000000) (ψ := -17679/25000) 257 183
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t88 : ((11648214781/10000000000000 : ℚ) : ℝ) ≤ stT257 88 := by
  have hc : ((10927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11648214781/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((10927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c89 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-49209/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2274243/5000000) (δ := 13023/1000000000) (ψ := -17679/25000) 257 184
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t89 : ((-26086020781/1000000000000 : ℚ) : ℝ) ≤ stT257 89 := by
  have hc : ((-49219/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26086020781/1000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-49219/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c90 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((49571/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2630359/10000000) (δ := 12923/1000000000) (ψ := -17679/25000) 257 184
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t90 : ((6530890509/125000000000 : ℚ) : ℝ) ≤ stT257 90 := by
  have hc : ((24783/50000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6530890509/125000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((24783/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c91 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-365721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1494519/2500000) (δ := 25773/1000000000) (ψ := -17679/25000) 257 185
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t91 : ((-38340604561/500000000000 : ℚ) : ℝ) ≤ stT257 91 := by
  have hc : ((-182873/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38340604561/500000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-182873/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c92 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((914091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1043839/10000000) (δ := 1293/100000000) (ψ := -17679/25000) 257 185
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t92 : ((238238388363/2500000000000 : ℚ) : ℝ) ≤ stT257 92 := by
  have hc : ((914041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238238388363/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((914041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c93 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-249631/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7718121/10000000) (δ := 12937/1000000000) (ψ := -17679/25000) 257 186
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t93 : ((-64717081653/625000000000 : ℚ) : ℝ) ≤ stT257 93 := by
  have hc : ((-499287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64717081653/625000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-499287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c94 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((188647/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -846391/10000000) (δ := 6433/500000000) (ψ := -17679/25000) 257 186
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t94 : ((194564163177/2000000000000 : ℚ) : ℝ) ≤ stT257 94 := by
  have hc : ((188637/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194564163177/2000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((188637/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c95 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-724457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 186019/312500) (δ := 6483/500000000) (ψ := -17679/25000) 257 186
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t95 : ((-743328967353/10000000000000 : ℚ) : ℝ) ≤ stT257 95 := by
  have hc : ((-724507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-743328967353/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-724507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c96 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((352067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -605509/2000000) (δ := 12959/1000000000) (ψ := -17679/25000) 257 187
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t96 : ((17963779527/500000000000 : ℚ) : ℝ) ≤ stT257 96 := by
  have hc : ((352017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17963779527/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((352017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c97 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((118297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1815277/5000000) (δ := 12959/1000000000) (ψ := -17679/25000) 257 187
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t97 : ((60030809231/5000000000000 : ℚ) : ℝ) ≤ stT257 97 := by
  have hc : ((118247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60030809231/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((118247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c98 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-292243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -685951/1250000) (δ := 1619/125000000) (ψ := -17679/25000) 257 188
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t98 : ((-73808849251/1250000000000 : ℚ) : ℝ) ≤ stT257 98 := by
  have hc : ((-73067/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73808849251/1250000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-73067/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c99 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((915469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1035309/10000000) (δ := 1619/125000000) (ψ := -17679/25000) 257 188
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t99 : ((920029965503/10000000000000 : ℚ) : ℝ) ≤ stT257 99 := by
  have hc : ((915419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((920029965503/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((915419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c100 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-247393/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7492627/10000000) (δ := 3213/250000000) (ψ := -17679/25000) 257 188
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t100 : ((-494811/5000000 : ℚ) : ℝ) ≤ stT257 100 := by
  have hc : ((-494811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-494811/5000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-494811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c101 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((2331/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -455551/2500000) (δ := 6479/500000000) (ψ := -17679/25000) 257 189
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t101 : ((74216824719/1000000000000 : ℚ) : ℝ) ≤ stT257 101 := by
  have hc : ((74587/100000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74216824719/1000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((74587/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c102 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-115139/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2253949/5000000) (δ := 2609/200000000) (ψ := -17679/25000) 257 189
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t102 : ((-7126837767/312500000000 : ℚ) : ℝ) ≤ stT257 102 := by
  have hc : ((-28791/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7126837767/312500000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-28791/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c103 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-391179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4931771/10000000) (δ := 13037/1000000000) (ψ := -17679/25000) 257 190
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t103 : ((-38548967057/1000000000000 : ℚ) : ℝ) ≤ stT257 103 := by
  have hc : ((-391229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38548967057/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-391229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c104 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((872549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 319/2500) (δ := 12937/1000000000) (ψ := -17679/25000) 257 190
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t104 : ((42777753471/500000000000 : ℚ) : ℝ) ≤ stT257 104 := by
  have hc : ((872499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42777753471/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((872499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c105 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-985273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1856101/2500000) (δ := 6433/500000000) (ψ := -17679/25000) 257 190
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t105 : ((-961577701023/10000000000000 : ℚ) : ℝ) ≤ stT257 105 := by
  have hc : ((-985323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-961577701023/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-985323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c106 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((319577/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -438699/2000000) (δ := 1303/100000000) (ψ := -17679/25000) 257 191
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t106 : ((969925201/15625000000 : ℚ) : ℝ) ≤ stT257 106 := by
  have hc : ((9986/15625 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((969925201/15625000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((9986/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c107 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((547/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 959863/2500000) (δ := 12873/1000000000) (ψ := -17679/25000) 257 191
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t107 : ((1056098659/312500000000 : ℚ) : ℝ) ≤ stT257 107 := by
  have hc : ((17479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1056098659/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((17479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c108 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-141491/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5891719/10000000) (δ := 649/50000000) (ψ := -17679/25000) 257 192
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t108 : ((-136159478751/2000000000000 : ℚ) : ℝ) ≤ stT257 108 := by
  have hc : ((-141501/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136159478751/2000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-141501/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c109 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((124991/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14973/5000000) (δ := 12923/1000000000) (ψ := -17679/25000) 257 192
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t109 : ((239427286307/2500000000000 : ℚ) : ℝ) ≤ stT257 109 := by
  have hc : ((499939/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((239427286307/2500000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((499939/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c110 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-70911/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5897577/10000000) (δ := 13023/1000000000) (ψ := -17679/25000) 257 192
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t110 : ((-16903945527/250000000000 : ℚ) : ℝ) ≤ stT257 110 := by
  have hc : ((-17729/25000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16903945527/250000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-17729/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c111 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-2753/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -159833/400000) (δ := 12887/1000000000) (ψ := -17679/25000) 257 193
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t111 : ((-654444441/250000000000 : ℚ) : ℝ) ≤ stT257 111 := by
  have hc : ((-1379/50000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-654444441/250000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-1379/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c112 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((380287/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3533/20000) (δ := 1627/125000000) (ψ := -17679/25000) 257 193
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t112 : ((179656873341/2500000000000 : ℚ) : ℝ) ≤ stT257 112 := by
  have hc : ((190131/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179656873341/2500000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((190131/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c113 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-988693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7477683/10000000) (δ := 12887/1000000000) (ψ := -17679/25000) 257 193
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t113 : ((-930131303703/10000000000000 : ℚ) : ℝ) ≤ stT257 113 := by
  have hc : ((-988743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-930131303703/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-988743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c114 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((258357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -256947/1000000) (δ := 12909/1000000000) (ψ := -17679/25000) 257 194
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t114 : ((12097493811/250000000000 : ℚ) : ℝ) ≤ stT257 114 := by
  have hc : ((64583/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12097493811/250000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((64583/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c115 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((13867/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 760483/2500000) (δ := 13009/1000000000) (ψ := -17679/25000) 257 194
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t115 : ((323229199/10000000000 : ℚ) : ℝ) ≤ stT257 115 := by
  have hc : ((2773/8000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((323229199/10000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((2773/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c116 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-238813/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3551633/5000000) (δ := 12901/1000000000) (ψ := -17679/25000) 257 195
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t116 : ((-443487967527/5000000000000 : ℚ) : ℝ) ≤ stT257 116 := by
  have hc : ((-477651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-443487967527/5000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-477651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c117 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((50307/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -794087/5000000) (δ := 6501/500000000) (ψ := -17679/25000) 257 195
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t117 : ((744094919/10000000000 : ℚ) : ℝ) ≤ stT257 117 := by
  have hc : ((402431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((744094919/10000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((402431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c118 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((3763/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 77599/200000) (δ := 13001/1000000000) (ψ := -17679/25000) 257 195
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t118 : ((1727457111/1000000000000 : ℚ) : ℝ) ≤ stT257 118 := by
  have hc : ((3753/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1727457111/1000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((3753/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c119 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-836923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1601521/2500000) (δ := 6447/500000000) (ψ := -17679/25000) 257 196
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t119 : ((-767252312127/10000000000000 : ℚ) : ℝ) ≤ stT257 119 := by
  have hc : ((-836973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-767252312127/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-836973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c120 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((91641/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1029451/10000000) (δ := 12909/1000000000) (ψ := -17679/25000) 257 196
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t120 : ((2091293883/25000000000 : ℚ) : ℝ) ≤ stT257 120 := by
  have hc : ((22909/25000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2091293883/25000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((22909/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c121 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-149651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 67227/156250) (δ := 12909/1000000000) (ψ := -17679/25000) 257 196
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t121 : ((-136091831791/10000000000000 : ℚ) : ℝ) ≤ stT257 121 := by
  have hc : ((-149701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136091831791/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-149701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c122 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-768273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6117339/10000000) (δ := 3229/250000000) (ψ := -17679/25000) 257 197
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t122 : ((-347803687317/5000000000000 : ℚ) : ℝ) ≤ stT257 122 := by
  have hc : ((-768323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-347803687317/5000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-768323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c123 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((469863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -872419/10000000) (δ := 12887/1000000000) (ψ := -17679/25000) 257 197
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t123 : ((211819179811/2500000000000 : ℚ) : ℝ) ≤ stT257 123 := by
  have hc : ((234919/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211819179811/2500000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((234919/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c124 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-160519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 270627/625000) (δ := 12887/1000000000) (ψ := -17679/25000) 257 197
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t124 : ((-144195297363/10000000000000 : ℚ) : ℝ) ≤ stT257 124 := by
  have hc : ((-160569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144195297363/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-160569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c125 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-793233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6217243/10000000) (δ := 649/50000000) (ψ := -17679/25000) 257 198
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t125 : ((-177383631781/2500000000000 : ℚ) : ℝ) ≤ stT257 125 := by
  have hc : ((-793283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177383631781/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-793283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c126 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((226287/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -548837/5000000) (δ := 12923/1000000000) (ψ := -17679/25000) 257 198
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t126 : ((40316232763/500000000000 : ℚ) : ℝ) ≤ stT257 126 := by
  have hc : ((452549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40316232763/500000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((452549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c127 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-21743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3981353/10000000) (δ := 13023/1000000000) (ψ := -17679/25000) 257 198
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t127 : ((-19338171101/10000000000000 : ℚ) : ℝ) ≤ stT257 127 := by
  have hc : ((-21793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19338171101/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-21793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c128 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-22327/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1337471/2000000) (δ := 12973/1000000000) (ψ := -17679/25000) 257 199
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t128 : ((-19735582923/250000000000 : ℚ) : ℝ) ≤ stT257 128 := by
  have hc : ((-89313/100000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19735582923/250000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-89313/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c129 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((780759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1687291/10000000) (δ := 1293/100000000) (ψ := -17679/25000) 257 199
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t129 : ((13747504781/200000000000 : ℚ) : ℝ) ≤ stT257 129 := by
  have hc : ((780709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13747504781/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((780709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c130 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((1291/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1637047/5000000) (δ := 1293/100000000) (ψ := -17679/25000) 257 199
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t130 : ((2264125227/100000000000 : ℚ) : ℝ) ≤ stT257 130 := by
  have hc : ((5163/20000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2264125227/100000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((5163/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c131 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-495287/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -938807/1250000) (δ := 12937/1000000000) (ψ := -17679/25000) 257 200
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t131 : ((-5409457137/62500000000 : ℚ) : ℝ) ≤ stT257 131 := by
  have hc : ((-30957/31250 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5409457137/62500000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-30957/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c132 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((31109/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2624501/10000000) (δ := 6483/500000000) (ψ := -17679/25000) 257 200
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t132 : ((54148360659/1250000000000 : ℚ) : ℝ) ≤ stT257 132 := by
  have hc : ((248847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54148360659/1250000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((248847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c133 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((78693/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 88983/400000) (δ := 6483/500000000) (ψ := -17679/25000) 257 200
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t133 : ((272919956423/5000000000000 : ℚ) : ℝ) ≤ stT257 133 := by
  have hc : ((314747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272919956423/5000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((314747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c134 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-473559/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3518659/5000000) (δ := 25737/1000000000) (ψ := -17679/25000) 257 200
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t134 : ((-25569658531/312500000000 : ℚ) : ℝ) ≤ stT257 134 := by
  have hc : ((-29599/31250 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25569658531/312500000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-29599/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c135 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((333/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -389369/1000000) (δ := 6429/500000000) (ψ := -17679/25000) 257 201
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t135 : ((571049237/500000000000 : ℚ) : ℝ) ≤ stT257 135 := by
  have hc : ((1327/100000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((571049237/500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((1327/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c136 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((471509/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 106003/1250000) (δ := 6479/500000000) (ψ := -17679/25000) 257 201
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t136 : ((25268359883/312500000000 : ℚ) : ℝ) ≤ stT257 136 := by
  have hc : ((117871/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25268359883/312500000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((117871/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c137 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-303079/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1388761/2500000) (δ := 2609/200000000) (ψ := -17679/25000) 257 201
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t137 : ((-63222492/1220703125 : ℚ) : ℝ) ≤ stT257 137 := by
  have hc : ((-9472/15625 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63222492/1220703125 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-9472/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c138 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-582083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -548021/1000000) (δ := 3213/250000000) (ψ := -17679/25000) 257 202
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t138 : ((-495544791181/10000000000000 : ℚ) : ℝ) ≤ stT257 138 := by
  have hc : ((-582133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-495544791181/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-582133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c139 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((943927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -841167/10000000) (δ := 1619/125000000) (ψ := -17679/25000) 257 202
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t139 : ((200146286219/2500000000000 : ℚ) : ℝ) ≤ stT257 139 := by
  have hc : ((943877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200146286219/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((943877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c140 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((64913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1882297/5000000) (δ := 3213/250000000) (ψ := -17679/25000) 257 202
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t140 : ((27409611951/5000000000000 : ℚ) : ℝ) ≤ stT257 140 := by
  have hc : ((64863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27409611951/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((64863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c141 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-981353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -184261/250000) (δ := 809/62500000) (ψ := -17679/25000) 257 203
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t141 : ((-103311312407/1250000000000 : ℚ) : ℝ) ≤ stT257 141 := by
  have hc : ((-981403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103311312407/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-981403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c142 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((53117/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -707441/2500000) (δ := 809/62500000) (ψ := -17679/25000) 257 203
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t142 : ((178278129183/5000000000000 : ℚ) : ℝ) ≤ stT257 142 := by
  have hc : ((212443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178278129183/5000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((212443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c143 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((24463/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 419761/2500000) (δ := 809/62500000) (ψ := -17679/25000) 257 203
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t143 : ((163645451343/2500000000000 : ℚ) : ℝ) ≤ stT257 143 := by
  have hc : ((391383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163645451343/2500000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((391383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c144 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-778173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 615637/1000000) (δ := 12959/1000000000) (ψ := -17679/25000) 257 203
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t144 : ((-324259842741/5000000000000 : ℚ) : ℝ) ≤ stT257 144 := by
  have hc : ((-778223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324259842741/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-778223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c145 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-22701/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1276293/2500000) (δ := 6483/500000000) (ψ := -17679/25000) 257 204
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t145 : ((-7541694037/200000000000 : ℚ) : ℝ) ≤ stT257 145 := by
  have hc : ((-45407/100000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7541694037/200000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-45407/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c146 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((481113/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -344667/5000000) (δ := 6433/500000000) (ψ := -17679/25000) 257 204
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t146 : ((1244221357/15625000000 : ℚ) : ℝ) ≤ stT257 146 := by
  have hc : ((15034/15625 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1244221357/15625000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((15034/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c147 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((92143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3696307/10000000) (δ := 6483/500000000) (ψ := -17679/25000) 257 204
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t147 : ((37978508549/5000000000000 : ℚ) : ℝ) ≤ stT257 147 := by
  have hc : ((92093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37978508549/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((92093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c148 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-124607/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7655699/10000000) (δ := 12973/1000000000) (ψ := -17679/25000) 257 205
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t148 : ((-81945174747/1000000000000 : ℚ) : ℝ) ≤ stT257 148 := by
  have hc : ((-498453/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81945174747/1000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-498453/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c149 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((118453/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41613/125000) (δ := 12873/1000000000) (ψ := -17679/25000) 257 205
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t149 : ((24254972217/1250000000000 : ℚ) : ℝ) ≤ stT257 149 := by
  have hc : ((29607/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24254972217/1250000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((29607/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c150 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((925883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 484289/5000000) (δ := 1293/100000000) (ψ := -17679/25000) 257 205
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t150 : ((47246183823/625000000000 : ℚ) : ℝ) ≤ stT257 150 := by
  have hc : ((925833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47246183823/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((925833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c151 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-100121/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2618867/5000000) (δ := 12973/1000000000) (ψ := -17679/25000) 257 205
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t151 : ((-81485506359/2000000000000 : ℚ) : ℝ) ≤ stT257 151 := by
  have hc : ((-100131/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81485506359/2000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-100131/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c152 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-199039/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -38933/62500) (δ := 12923/1000000000) (ψ := -17679/25000) 257 206
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t152 : ((-80726132031/1250000000000 : ℚ) : ℝ) ≤ stT257 152 := by
  have hc : ((-398103/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80726132031/1250000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-398103/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c153 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((346029/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40323/200000) (δ := 649/50000000) (ψ := -17679/25000) 257 206
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t153 : ((17482976613/312500000000 : ℚ) : ℝ) ≤ stT257 153 := by
  have hc : ((86501/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17482976613/312500000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((86501/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c154 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((646493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 271193/1250000) (δ := 13023/1000000000) (ψ := -17679/25000) 257 206
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t154 : ((260458995573/5000000000000 : ℚ) : ℝ) ≤ stT257 154 := by
  have hc : ((646443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260458995573/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((646443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c155 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-204863/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3164063/5000000) (δ := 649/50000000) (ψ := -17679/25000) 257 206
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t155 : ((-16456009911/250000000000 : ℚ) : ℝ) ≤ stT257 155 := by
  have hc : ((-409751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16456009911/250000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-409751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c156 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-10083/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -327999/625000) (δ := 3247/250000000) (ψ := -17679/25000) 257 207
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t156 : ((-2018415961/50000000000 : ℚ) : ℝ) ≤ stT257 156 := by
  have hc : ((-2521/5000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2018415961/50000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-2521/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c157 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((448687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -571269/5000000) (δ := 2583/200000000) (ψ := -17679/25000) 257 207
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t157 : ((89517715233/1250000000000 : ℚ) : ℝ) ≤ stT257 157 := by
  have hc : ((224331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89517715233/1250000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((224331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c158 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((385793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2936823/10000000) (δ := 2583/200000000) (ψ := -17679/25000) 257 207
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t158 : ((306880543851/10000000000000 : ℚ) : ℝ) ≤ stT257 158 := by
  have hc : ((385743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((306880543851/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((385743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c159 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-47047/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1747621/2500000) (δ := 2583/200000000) (ψ := -17679/25000) 257 207
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t159 : ((-18656350037/250000000000 : ℚ) : ℝ) ≤ stT257 159 := by
  have hc : ((-94099/100000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18656350037/250000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-94099/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c160 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-60041/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4689261/10000000) (δ := 2579/200000000) (ψ := -17679/25000) 257 208
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t160 : ((-4747451907/200000000000 : ℚ) : ℝ) ≤ stT257 160 := by
  have hc : ((-60051/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4747451907/200000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-60051/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c161 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((96257/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137233/2000000) (δ := 3227/250000000) (ψ := -17679/25000) 257 208
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t161 : ((1896429093/25000000000 : ℚ) : ℝ) ≤ stT257 161 := by
  have hc : ((24063/25000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1896429093/25000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((24063/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c162 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((251199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 658439/2000000) (δ := 3227/250000000) (ψ := -17679/25000) 257 208
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t162 : ((98660619713/5000000000000 : ℚ) : ℝ) ≤ stT257 162 := by
  have hc : ((251149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98660619713/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((251149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c163 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-970581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1811519/2500000) (δ := 2579/200000000) (ψ := -17679/25000) 257 208
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t163 : ((-760257407691/10000000000000 : ℚ) : ℝ) ≤ stT257 163 := by
  have hc : ((-970631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-760257407691/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-970631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c164 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-239737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4532229/10000000) (δ := 12901/1000000000) (ψ := -17679/25000) 257 209
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t164 : ((-187242234903/10000000000000 : ℚ) : ℝ) ≤ stT257 164 := by
  have hc : ((-239787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187242234903/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-239787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c165 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((968767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -626471/10000000) (δ := 6501/500000000) (ψ := -17679/25000) 257 209
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t165 : ((377072123533/5000000000000 : ℚ) : ℝ) ≤ stT257 165 := by
  have hc : ((968717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((377072123533/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((968717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c166 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((265299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1627853/5000000) (δ := 13001/1000000000) (ψ := -17679/25000) 257 209
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t166 : ((4117460227/200000000000 : ℚ) : ℝ) ≤ stT257 166 := by
  have hc : ((265249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4117460227/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((265249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c167 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-478293/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3557313/5000000) (δ := 6501/500000000) (ψ := -17679/25000) 257 209
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t167 : ((-2891671469/39062500000 : ℚ) : ℝ) ≤ stT257 167 := by
  have hc : ((-239159/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2891671469/39062500000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-239159/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c168 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-65229/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1189387/2500000) (δ := 13009/1000000000) (ψ := -17679/25000) 257 210
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t168 : ((-50332997563/2000000000000 : ℚ) : ℝ) ≤ stT257 168 := by
  have hc : ((-65239/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50332997563/2000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-65239/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c169 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((929487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -944439/10000000) (δ := 13009/1000000000) (ψ := -17679/25000) 257 210
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t169 : ((71495082351/1000000000000 : ℚ) : ℝ) ≤ stT257 169 := by
  have hc : ((929437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71495082351/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((929437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c170 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((83801/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1423059/5000000) (δ := 12909/1000000000) (ψ := -17679/25000) 257 210
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t170 : ((16066170131/500000000000 : ℚ) : ℝ) ≤ stT257 170 := by
  have hc : ((83791/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16066170131/500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((83791/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c171 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-879581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1322889/2000000) (δ := 13009/1000000000) (ψ := -17679/25000) 257 210
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t171 : ((-8408392729/125000000000 : ℚ) : ℝ) ≤ stT257 171 := by
  have hc : ((-879631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8408392729/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-879631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c172 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-269003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1069433/2000000) (δ := 1627/125000000) (ψ := -17679/25000) 257 211
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t172 : ((-51282991701/1250000000000 : ℚ) : ℝ) ≤ stT257 172 := by
  have hc : ((-67257/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51282991701/1250000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-67257/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c173 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((398341/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1622529/10000000) (δ := 12987/1000000000) (ψ := -17679/25000) 257 211
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t173 : ((15141684003/250000000000 : ℚ) : ℝ) ≤ stT257 173 := by
  have hc : ((99579/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15141684003/250000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((99579/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c174 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((673207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2080649/10000000) (δ := 1627/125000000) (ψ := -17679/25000) 257 211
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t174 : ((255159487693/5000000000000 : ℚ) : ℝ) ≤ stT257 174 := by
  have hc : ((673157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((255159487693/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((673157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c175 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-670033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5762623/10000000) (δ := 12987/1000000000) (ψ := -17679/25000) 257 211
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t175 : ((-506535172107/10000000000000 : ℚ) : ℝ) ≤ stT257 175 := by
  have hc : ((-670083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-506535172107/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-670083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c176 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-809297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2011/3200) (δ := 12879/1000000000) (ψ := -17679/25000) 257 212
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t176 : ((-610068772313/10000000000000 : ℚ) : ℝ) ≤ stT257 176 := by
  have hc : ((-809347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-610068772313/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-809347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c177 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((49093/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1322049/5000000) (δ := 407/31250000) (ψ := -17679/25000) 257 212
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t177 : ((288256241/7812500000 : ℚ) : ℝ) ≤ stT257 177 := by
  have hc : ((1534/3125 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((288256241/7812500000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((1534/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c178 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((184963/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 487809/5000000) (δ := 12879/1000000000) (ψ := -17679/25000) 257 212
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t178 : ((138628007043/2000000000000 : ℚ) : ℝ) ≤ stT257 178 := by
  have hc : ((184953/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138628007043/2000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((184953/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c179 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-64087/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 571887/1250000) (δ := 3231/250000000) (ψ := -17679/25000) 257 212
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t179 : ((-23955136941/1250000000000 : ℚ) : ℝ) ≤ stT257 179 := by
  have hc : ((-128199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23955136941/1250000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-128199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c180 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-496393/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15107/20000) (δ := 1609/125000000) (ψ := -17679/25000) 257 213
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t180 : ((-46251016851/625000000000 : ℚ) : ℝ) ≤ stT257 180 := by
  have hc : ((-248209/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46251016851/625000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-248209/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c181 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-26769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3993921/10000000) (δ := 13031/1000000000) (ψ := -17679/25000) 257 213
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t181 : ((-3986885721/2000000000000 : ℚ) : ℝ) ≤ stT257 181 := by
  have hc : ((-26819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3986885721/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-26819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c182 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((245889/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -454003/10000000) (δ := 13031/1000000000) (ψ := -17679/25000) 257 213
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t182 : ((364511419497/5000000000000 : ℚ) : ℝ) ≤ stT257 182 := by
  have hc : ((491753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((364511419497/5000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((491753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c183 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((84353/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 122663/400000) (δ := 3243/250000000) (ψ := -17679/25000) 257 213
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t183 : ((124692537501/5000000000000 : ℚ) : ℝ) ≤ stT257 183 := by
  have hc : ((168681/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124692537501/5000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((168681/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c184 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-43529/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6567943/10000000) (δ := 3243/250000000) (ψ := -17679/25000) 257 213
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t184 : ((-6418371423/100000000000 : ℚ) : ℝ) ≤ stT257 184 := by
  have hc : ((-87063/100000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6418371423/100000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-87063/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c185 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-159567/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2828803/5000000) (δ := 2593/200000000) (ψ := -17679/25000) 257 214
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t185 : ((-46930096837/1000000000000 : ℚ) : ℝ) ≤ stT257 185 := by
  have hc : ((-319159/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46930096837/1000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-319159/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c186 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((319497/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2194017/10000000) (δ := 2593/200000000) (ψ := -17679/25000) 257 214
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t186 : ((2928100649/62500000000 : ℚ) : ℝ) ≤ stT257 186 := by
  have hc : ((19967/31250 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2928100649/62500000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((19967/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c187 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((438689/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 312767/2500000) (δ := 2593/200000000) (ψ := -17679/25000) 257 214
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t187 : ((5012229697/78125000000 : ℚ) : ℝ) ≤ stT257 187 := by
  have hc : ((54833/62500 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5012229697/78125000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((54833/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c188 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-295797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2338857/5000000) (δ := 6519/500000000) (ψ := -17679/25000) 257 214
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t188 : ((-8630744531/400000000000 : ℚ) : ℝ) ≤ stT257 188 := by
  have hc : ((-295847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8630744531/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-295847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c189 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-124461/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7621723/10000000) (δ := 6429/500000000) (ψ := -17679/25000) 257 215
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t189 : ((-362146425517/5000000000000 : ℚ) : ℝ) ≤ stT257 189 := by
  have hc : ((-497869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-362146425517/5000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-497869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c190 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-121403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -677/1600) (δ := 2609/200000000) (ψ := -17679/25000) 257 215
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t190 : ((-88111358081/10000000000000 : ℚ) : ℝ) ≤ stT257 190 := by
  have hc : ((-121453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88111358081/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-121453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c191 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((470807/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -858511/10000000) (δ := 6429/500000000) (ψ := -17679/25000) 257 215
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t191 : ((85161403717/1250000000000 : ℚ) : ℝ) ≤ stT257 191 := by
  have hc : ((235391/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85161403717/1250000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((235391/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c192 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((27073/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31207/125000) (δ := 2589/200000000) (ψ := -17679/25000) 257 215
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t192 : ((39072855867/1000000000000 : ℚ) : ℝ) ≤ stT257 192 := by
  have hc : ((54141/100000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39072855867/1000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((54141/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c193 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-345507/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5834219/10000000) (δ := 2589/200000000) (ψ := -17679/25000) 257 215
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t193 : ((-7772483191/156250000000 : ℚ) : ℝ) ≤ stT257 193 := by
  have hc : ((-86383/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7772483191/156250000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-86383/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c194 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-173537/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1310661/2000000) (δ := 13051/1000000000) (ψ := -17679/25000) 257 216
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t194 : ((-124599630573/2000000000000 : ℚ) : ℝ) ≤ stT257 194 := by
  have hc : ((-173547/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124599630573/2000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-173547/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c195 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((66879/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -649991/2000000) (δ := 3213/250000000) (ψ := -17679/25000) 257 216
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t195 : ((47884036781/2500000000000 : ℚ) : ℝ) ≤ stT257 195 := by
  have hc : ((133733/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47884036781/2500000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((133733/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c196 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((999893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 36497/10000000) (δ := 1619/125000000) (ψ := -17679/25000) 257 216
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t196 : ((142834571451/2000000000000 : ℚ) : ℝ) ≤ stT257 196 := by
  have hc : ((999843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142834571451/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((999843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c197 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((61439/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3306243/10000000) (δ := 13051/1000000000) (ψ := -17679/25000) 257 216
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t197 : ((8752907691/500000000000 : ℚ) : ℝ) ≤ stT257 197 := by
  have hc : ((122853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8752907691/500000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((122853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c198 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-868897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3279707/5000000) (δ := 1619/125000000) (ψ := -17679/25000) 257 216
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t198 : ((-61753456449/1000000000000 : ℚ) : ℝ) ≤ stT257 198 := by
  have hc : ((-868947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61753456449/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-868947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c199 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-713099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5911763/10000000) (δ := 12859/1000000000) (ψ := -17679/25000) 257 217
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t199 : ((-252769244709/5000000000000 : ℚ) : ℝ) ≤ stT257 199 := by
  have hc : ((-713149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252769244709/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-713149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c200 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((474419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -84101/312500) (δ := 809/62500000) (ψ := -17679/25000) 257 217
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t200 : ((167714583057/5000000000000 : ℚ) : ℝ) ≤ stT257 200 := by
  have hc : ((474369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167714583057/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((474369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c201 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((244749/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 513301/10000000) (δ := 809/62500000) (ψ := -17679/25000) 257 217
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t201 : ((69049466637/1000000000000 : ℚ) : ℝ) ≤ stT257 201 := by
  have hc : ((489473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69049466637/1000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((489473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c202 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((4497/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 925459/2500000) (δ := 12859/1000000000) (ψ := -17679/25000) 257 217
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t202 : ((6324633433/1000000000000 : ℚ) : ℝ) ≤ stT257 202 := by
  have hc : ((8989/100000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6324633433/1000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((8989/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c203 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-28883/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3437347/5000000) (δ := 12959/1000000000) (ψ := -17679/25000) 257 217
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t203 : ((-324368091039/5000000000000 : ℚ) : ℝ) ≤ stT257 203 := by
  have hc : ((-462153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324368091039/5000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-462153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c204 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-321961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -227041/400000) (δ := 3259/250000000) (ψ := -17679/25000) 257 218
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t204 : ((-112717800013/2500000000000 : ℚ) : ℝ) ≤ stT257 204 := by
  have hc : ((-160993/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112717800013/2500000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-160993/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c205 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((528741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12671/50000) (δ := 3259/250000000) (ψ := -17679/25000) 257 218
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t205 : ((36925365513/1000000000000 : ℚ) : ℝ) ≤ stT257 205 := by
  have hc : ((528691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36925365513/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((528691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c206 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((486031/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 296167/5000000) (δ := 12867/1000000000) (ψ := -17679/25000) 257 218
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t206 : ((169308209199/2500000000000 : ℚ) : ℝ) ≤ stT257 206 := by
  have hc : ((243003/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169308209199/2500000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((243003/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c207 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((22299/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 462963/1250000) (δ := 3259/250000000) (ψ := -17679/25000) 257 218
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t207 : ((3872546813/625000000000 : ℚ) : ℝ) ≤ stT257 207 := by
  have hc : ((44573/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3872546813/625000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((44573/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c208 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-114057/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1360021/2000000) (δ := 12967/1000000000) (ψ := -17679/25000) 257 218
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t208 : ((-2471522501/39062500000 : ℚ) : ℝ) ≤ stT257 208 := by
  have hc : ((-456253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2471522501/39062500000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-456253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c209 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-688721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58263/100000) (δ := 6437/500000000) (ψ := -17679/25000) 257 219
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t209 : ((-95286646453/2000000000000 : ℚ) : ℝ) ≤ stT257 209 := by
  have hc : ((-688771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95286646453/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-688771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c210 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((225111/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -551891/2000000) (δ := 12929/1000000000) (ψ := -17679/25000) 257 219
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t210 : ((15532397059/500000000000 : ℚ) : ℝ) ≤ stT257 210 := by
  have hc : ((112543/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15532397059/500000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((112543/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c211 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((993149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 146403/5000000) (δ := 6487/500000000) (ψ := -17679/25000) 257 219
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t211 : ((170919289593/2500000000000 : ℚ) : ℝ) ≤ stT257 211 := by
  have hc : ((993099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170919289593/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((993099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c212 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((29537/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 333061/1000000) (δ := 6437/500000000) (ψ := -17679/25000) 257 219
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t212 : ((40563556323/2500000000000 : ℚ) : ℝ) ≤ stT257 212 := by
  have hc : ((118123/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40563556323/2500000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((118123/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c213 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-412687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6354151/10000000) (δ := 6487/500000000) (ψ := -17679/25000) 257 219
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t213 : ((-35348215321/625000000000 : ℚ) : ℝ) ≤ stT257 213 := by
  have hc : ((-51589/62500 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35348215321/625000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-51589/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c214 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-823167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6344407/10000000) (δ := 6461/500000000) (ψ := -17679/25000) 257 220
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t214 : ((-281369808081/5000000000000 : ℚ) : ℝ) ≤ stT257 214 := by
  have hc : ((-823217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-281369808081/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-823217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c215 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((114557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -209317/625000) (δ := 6461/500000000) (ψ := -17679/25000) 257 220
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t215 : ((9763767101/625000000000 : ℚ) : ℝ) ≤ stT257 215 := by
  have hc : ((28633/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9763767101/625000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((28633/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c216 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((123651/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -73523/2000000) (δ := 6461/500000000) (ψ := -17679/25000) 257 220
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t216 : ((336517981127/5000000000000 : ℚ) : ℝ) ≤ stT257 216 := by
  have hc : ((494579/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((336517981127/5000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((494579/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c217 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((506211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 650007/2500000) (δ := 6511/500000000) (ψ := -17679/25000) 257 220
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t217 : ((85901089471/2500000000000 : ℚ) : ℝ) ≤ stT257 217 := by
  have hc : ((506161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85901089471/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((506161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c218 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-302921/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5554051/10000000) (δ := 12981/1000000000) (ψ := -17679/25000) 257 220
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t218 : ((-51295271139/1250000000000 : ℚ) : ℝ) ≤ stT257 218 := by
  have hc : ((-151473/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51295271139/1250000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-151473/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c219 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-19347/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7213383/10000000) (δ := 2583/200000000) (ψ := -17679/25000) 257 221
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t219 : ((-1634272353/25000000000 : ℚ) : ℝ) ≤ stT257 219 := by
  have hc : ((-4837/5000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1634272353/25000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-4837/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c220 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-71611/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4286281/10000000) (δ := 3247/250000000) (ψ := -17679/25000) 257 221
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t220 : ((-60371239/6250000000 : ℚ) : ℝ) ≤ stT257 220 := by
  have hc : ((-17909/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60371239/6250000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-17909/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c221 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((170613/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -274483/2000000) (δ := 3247/250000000) (ψ := -17679/25000) 257 221
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t221 : ((3586245663/62500000000 : ℚ) : ℝ) ≤ stT257 221 := by
  have hc : ((170603/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3586245663/62500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((170603/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c222 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((818911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 305643/2000000) (δ := 2583/200000000) (ψ := -17679/25000) 257 221
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t222 : ((137395868329/2500000000000 : ℚ) : ℝ) ≤ stT257 222 := by
  have hc : ((818861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137395868329/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((818861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c223 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-194307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4415867/10000000) (δ := 2583/200000000) (ψ := -17679/25000) 257 221
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t223 : ((-2603023301/200000000000 : ℚ) : ℝ) ≤ stT257 223 := by
  have hc : ((-194357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2603023301/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-194357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c224 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-243679/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1458121/2000000) (δ := 1611/125000000) (ψ := -17679/25000) 257 221
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t224 : ((-162823450491/2500000000000 : ℚ) : ℝ) ≤ stT257 224 := by
  have hc : ((-487383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162823450491/2500000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-487383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c225 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-606273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2777703/5000000) (δ := 2599/200000000) (ψ := -17679/25000) 257 222
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t225 : ((-404215535441/10000000000000 : ℚ) : ℝ) ≤ stT257 225 := by
  have hc : ((-606323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-404215535441/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-606323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c226 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((469137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -84569/312500) (δ := 6427/250000000) (ψ := -17679/25000) 257 222
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t226 : ((31203198153/1000000000000 : ℚ) : ℝ) ≤ stT257 226 := by
  have hc : ((469087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31203198153/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((469087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c227 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((998639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 65231/5000000) (δ := 2599/200000000) (ψ := -17679/25000) 257 222
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t227 : ((662786486847/10000000000000 : ℚ) : ℝ) ≤ stT257 227 := by
  have hc : ((998589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((662786486847/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((998589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c228 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((37921/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 590927/2000000) (δ := 2599/200000000) (ψ := -17679/25000) 257 222
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t228 : ((3138809707/125000000000 : ℚ) : ℝ) ≤ stT257 228 := by
  have hc : ((9479/25000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3138809707/125000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((9479/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c229 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-26847/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 720809/1250000) (δ := 2599/200000000) (ψ := -17679/25000) 257 222
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t229 : ((-17742329331/400000000000 : ℚ) : ℝ) ≤ stT257 229 := by
  have hc : ((-26849/40000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17742329331/400000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-26849/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c230 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-29991/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3570963/5000000) (δ := 13003/1000000000) (ψ := -17679/25000) 257 223
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t230 : ((-316424413661/5000000000000 : ℚ) : ℝ) ≤ stT257 230 := by
  have hc : ((-479881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-316424413661/5000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-479881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c231 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-170173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -544313/1250000) (δ := 13003/1000000000) (ψ := -17679/25000) 257 223
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t231 : ((-3499955103/312500000000 : ℚ) : ℝ) ≤ stT257 231 := by
  have hc : ((-170223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3499955103/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-170223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c232 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((403523/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1579161/10000000) (δ := 13003/1000000000) (ψ := -17679/25000) 257 223
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t232 : ((33113668617/625000000000 : ℚ) : ℝ) ≤ stT257 232 := by
  have hc : ((201749/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33113668617/625000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((201749/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c233 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((444939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 236859/2000000) (δ := 13/1000000) (ψ := -17679/25000) 257 223
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t233 : ((145736252297/2500000000000 : ℚ) : ℝ) ≤ stT257 233 := by
  have hc : ((222457/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145736252297/2500000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((222457/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c234 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-447/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 393593/1000000) (δ := 129/10000000) (ψ := -17679/25000) 257 223
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t234 : ((-1185196173/5000000000000 : ℚ) : ℝ) ≤ stT257 234 := by
  have hc : ((-1813/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1185196173/5000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-1813/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c235 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-55687/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6675807/10000000) (δ := 129/10000000) (ψ := -17679/25000) 257 223
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t235 : ((-290626268409/5000000000000 : ℚ) : ℝ) ≤ stT257 235 := by
  have hc : ((-445521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-290626268409/5000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-445521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c236 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-813861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1575977/2500000) (δ := 1301/100000000) (ψ := -17679/25000) 257 224
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t236 : ((-105962259179/2000000000000 : ℚ) : ℝ) ≤ stT257 236 := by
  have hc : ((-813911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105962259179/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-813911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c237 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((2117/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1793613/5000000) (δ := 12993/1000000000) (ψ := -17679/25000) 257 224
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t237 : ((43988163111/5000000000000 : ℚ) : ℝ) ≤ stT257 237 := by
  have hc : ((67719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43988163111/5000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((67719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c238 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((234603/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -881979/10000000) (δ := 1301/100000000) (ψ := -17679/25000) 257 224
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t238 : ((304124531743/5000000000000 : ℚ) : ℝ) ≤ stT257 238 := by
  have hc : ((469181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((304124531743/5000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((469181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c239 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((748643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1811959/10000000) (δ := 1291/100000000) (ψ := -17679/25000) 257 224
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t239 : ((242112193839/5000000000000 : ℚ) : ℝ) ≤ stT257 239 := by
  have hc : ((748593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242112193839/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((748593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c240 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-225119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4494653/10000000) (δ := 12993/1000000000) (ψ := -17679/25000) 257 224
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t240 : ((-72673069581/5000000000000 : ℚ) : ℝ) ≤ stT257 240 := by
  have hc : ((-225169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72673069581/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-225169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c241 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-962391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 895771/1250000) (δ := 12993/1000000000) (ψ := -17679/25000) 257 224
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t241 : ((-619963107237/10000000000000 : ℚ) : ℝ) ≤ stT257 241 := by
  have hc : ((-962441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-619963107237/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-962441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c242 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-704513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5881331/10000000) (δ := 6443/500000000) (ψ := -17679/25000) 257 225
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t242 : ((-18116428419/400000000000 : ℚ) : ℝ) ≤ stT257 242 := by
  have hc : ((-704563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18116428419/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-704563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c243 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((137243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1615927/5000000) (δ := 6493/500000000) (ψ := -17679/25000) 257 225
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t243 : ((88025347/5000000000 : ℚ) : ℝ) ≤ stT257 243 := by
  have hc : ((68609/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88025347/5000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((68609/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c244 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((485989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -118647/2000000) (δ := 6493/500000000) (ψ := -17679/25000) 257 225
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t244 : ((9722074293/156250000000 : ℚ) : ℝ) ≤ stT257 244 := by
  have hc : ((121491/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9722074293/156250000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((121491/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c245 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((171681/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1017279/5000000) (δ := 12893/500000000) (ψ := -17679/25000) 257 225
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t245 : ((54837442303/1250000000000 : ℚ) : ℝ) ≤ stT257 245 := by
  have hc : ((343337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54837442303/1250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((343337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c246 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-57167/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2325843/5000000) (δ := 13017/1000000000) (ψ := -17679/25000) 257 225
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t246 : ((-36454740129/2000000000000 : ℚ) : ℝ) ≤ stT257 246 := by
  have hc : ((-57177/200000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36454740129/2000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-57177/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c247 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-121467/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 362909/500000) (δ := 13017/1000000000) (ψ := -17679/25000) 257 225
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t247 : ((-61833285501/1000000000000 : ℚ) : ℝ) ≤ stT257 247 := by
  have hc : ((-485893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61833285501/1000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-485893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c248 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-348331/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5853827/10000000) (δ := 12979/1000000000) (ψ := -17679/25000) 257 226
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t248 : ((-55301602089/1250000000000 : ℚ) : ℝ) ≤ stT257 248 := by
  have hc : ((-87089/125000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55301602089/1250000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-87089/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c249 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((130211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1634171/5000000) (δ := 407/31250000) (ψ := -17679/25000) 257 226
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t249 : ((10312749083/625000000000 : ℚ) : ℝ) ≤ stT257 249 := by
  have hc : ((65093/250000 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10312749083/625000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((65093/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_c250 :
    |Real.cos (((257 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((96181/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -346569/5000000) (δ := 3231/250000000) (ψ := -17679/25000) 257 226
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st257_t250 : ((760337401/12500000000 : ℚ) : ℝ) ≤ stT257 250 := by
  have hc : ((6011/6250 : ℚ) : ℝ)
      ≤ Real.cos (((257 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st257_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((760337401/12500000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((6011/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st257_p1 : ((4751/6250 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT257 (i+1) := by
  rw [Finset.sum_range_one]
  exact st257_t1

theorem st257_p2 : ((22128145613/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT257 (i+1))
      = (∑ i ∈ Finset.range 1, stT257 (i+1)) + stT257 2 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 1
    simpa using h
  have hprev := st257_p1
  have hstep := st257_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p3 : ((3105536838201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT257 (i+1))
      = (∑ i ∈ Finset.range 2, stT257 (i+1)) + stT257 3 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 2
    simpa using h
  have hprev := st257_p2
  have hstep := st257_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p4 : ((4111194338201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT257 (i+1))
      = (∑ i ∈ Finset.range 3, stT257 (i+1)) + stT257 4 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 3
    simpa using h
  have hprev := st257_p3
  have hstep := st257_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p5 : ((12411522501467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT257 (i+1))
      = (∑ i ∈ Finset.range 4, stT257 (i+1)) + stT257 5 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 4
    simpa using h
  have hprev := st257_p4
  have hstep := st257_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p6 : ((2275013289591/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT257 (i+1))
      = (∑ i ∈ Finset.range 5, stT257 (i+1)) + stT257 6 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 5
    simpa using h
  have hprev := st257_p5
  have hstep := st257_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p7 : ((31495126039/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT257 (i+1))
      = (∑ i ∈ Finset.range 6, stT257 (i+1)) + stT257 7 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 6
    simpa using h
  have hprev := st257_p6
  have hstep := st257_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p8 : ((9812894133979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT257 (i+1))
      = (∑ i ∈ Finset.range 7, stT257 (i+1)) + stT257 8 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 7
    simpa using h
  have hprev := st257_p7
  have hstep := st257_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p9 : ((13131713802097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT257 (i+1))
      = (∑ i ∈ Finset.range 8, stT257 (i+1)) + stT257 9 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 8
    simpa using h
  have hprev := st257_p8
  have hstep := st257_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p10 : ((12253685179451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT257 (i+1))
      = (∑ i ∈ Finset.range 9, stT257 (i+1)) + stT257 10 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 9
    simpa using h
  have hprev := st257_p9
  have hstep := st257_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p11 : ((13306411883401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT257 (i+1))
      = (∑ i ∈ Finset.range 10, stT257 (i+1)) + stT257 11 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 10
    simpa using h
  have hprev := st257_p10
  have hstep := st257_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p12 : ((3336715981291/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT257 (i+1))
      = (∑ i ∈ Finset.range 11, stT257 (i+1)) + stT257 12 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 11
    simpa using h
  have hprev := st257_p11
  have hstep := st257_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p13 : ((4020674948791/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT257 (i+1))
      = (∑ i ∈ Finset.range 12, stT257 (i+1)) + stT257 13 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 12
    simpa using h
  have hprev := st257_p12
  have hstep := st257_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p14 : ((4645754797493/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT257 (i+1))
      = (∑ i ∈ Finset.range 13, stT257 (i+1)) + stT257 14 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 13
    simpa using h
  have hprev := st257_p13
  have hstep := st257_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p15 : ((5114714822963/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT257 (i+1))
      = (∑ i ∈ Finset.range 14, stT257 (i+1)) + stT257 15 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 14
    simpa using h
  have hprev := st257_p14
  have hstep := st257_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p16 : ((8988496649553/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT257 (i+1))
      = (∑ i ∈ Finset.range 15, stT257 (i+1)) + stT257 16 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 15
    simpa using h
  have hprev := st257_p15
  have hstep := st257_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p17 : ((2040217709883/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT257 (i+1))
      = (∑ i ∈ Finset.range 16, stT257 (i+1)) + stT257 17 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 16
    simpa using h
  have hprev := st257_p16
  have hstep := st257_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p18 : ((3835609083733/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT257 (i+1))
      = (∑ i ∈ Finset.range 17, stT257 (i+1)) + stT257 18 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 17
    simpa using h
  have hprev := st257_p17
  have hstep := st257_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p19 : ((679562523687/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT257 (i+1))
      = (∑ i ∈ Finset.range 18, stT257 (i+1)) + stT257 19 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 18
    simpa using h
  have hprev := st257_p18
  have hstep := st257_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p20 : ((15634560429039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT257 (i+1))
      = (∑ i ∈ Finset.range 19, stT257 (i+1)) + stT257 20 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 19
    simpa using h
  have hprev := st257_p19
  have hstep := st257_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p21 : ((14265814837437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT257 (i+1))
      = (∑ i ∈ Finset.range 20, stT257 (i+1)) + stT257 21 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 20
    simpa using h
  have hprev := st257_p20
  have hstep := st257_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p22 : ((12217989173317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT257 (i+1))
      = (∑ i ∈ Finset.range 21, stT257 (i+1)) + stT257 22 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 21
    simpa using h
  have hprev := st257_p21
  have hstep := st257_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p23 : ((1357207938989/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT257 (i+1))
      = (∑ i ∈ Finset.range 22, stT257 (i+1)) + stT257 23 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 22
    simpa using h
  have hprev := st257_p22
  have hstep := st257_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p24 : ((6239480000491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT257 (i+1))
      = (∑ i ∈ Finset.range 23, stT257 (i+1)) + stT257 24 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 23
    simpa using h
  have hprev := st257_p23
  have hstep := st257_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p25 : ((6387473000491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT257 (i+1))
      = (∑ i ∈ Finset.range 24, stT257 (i+1)) + stT257 25 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 24
    simpa using h
  have hprev := st257_p24
  have hstep := st257_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p26 : ((5681590000669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT257 (i+1))
      = (∑ i ∈ Finset.range 25, stT257 (i+1)) + stT257 26 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 25
    simpa using h
  have hprev := st257_p25
  have hstep := st257_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p27 : ((6529301458669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT257 (i+1))
      = (∑ i ∈ Finset.range 26, stT257 (i+1)) + stT257 27 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 26
    simpa using h
  have hprev := st257_p26
  have hstep := st257_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p28 : ((1146855120089/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT257 (i+1))
      = (∑ i ∈ Finset.range 27, stT257 (i+1)) + stT257 28 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 27
    simpa using h
  have hprev := st257_p27
  have hstep := st257_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p29 : ((6253431378467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT257 (i+1))
      = (∑ i ∈ Finset.range 28, stT257 (i+1)) + stT257 29 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 28
    simpa using h
  have hprev := st257_p28
  have hstep := st257_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p30 : ((12722933727061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT257 (i+1))
      = (∑ i ∈ Finset.range 29, stT257 (i+1)) + stT257 30 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 29
    simpa using h
  have hprev := st257_p29
  have hstep := st257_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p31 : ((11109003194769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT257 (i+1))
      = (∑ i ∈ Finset.range 30, stT257 (i+1)) + stT257 31 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 30
    simpa using h
  have hprev := st257_p30
  have hstep := st257_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p32 : ((12326486619927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT257 (i+1))
      = (∑ i ∈ Finset.range 31, stT257 (i+1)) + stT257 32 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 31
    simpa using h
  have hprev := st257_p31
  have hstep := st257_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p33 : ((13521480602199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT257 (i+1))
      = (∑ i ∈ Finset.range 32, stT257 (i+1)) + stT257 33 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 32
    simpa using h
  have hprev := st257_p32
  have hstep := st257_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p34 : ((12507778102389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT257 (i+1))
      = (∑ i ∈ Finset.range 33, stT257 (i+1)) + stT257 34 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 33
    simpa using h
  have hprev := st257_p33
  have hstep := st257_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p35 : ((1357648195507/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT257 (i+1))
      = (∑ i ∈ Finset.range 34, stT257 (i+1)) + stT257 35 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 34
    simpa using h
  have hprev := st257_p34
  have hstep := st257_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p36 : ((159902480811/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT257 (i+1))
      = (∑ i ∈ Finset.range 35, stT257 (i+1)) + stT257 36 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 35
    simpa using h
  have hprev := st257_p35
  have hstep := st257_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p37 : ((10831912661631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT257 (i+1))
      = (∑ i ∈ Finset.range 36, stT257 (i+1)) + stT257 37 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 36
    simpa using h
  have hprev := st257_p36
  have hstep := st257_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p38 : ((2428943059311/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT257 (i+1))
      = (∑ i ∈ Finset.range 37, stT257 (i+1)) + stT257 38 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 37
    simpa using h
  have hprev := st257_p37
  have hstep := st257_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p39 : ((13701794535831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT257 (i+1))
      = (∑ i ∈ Finset.range 38, stT257 (i+1)) + stT257 39 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 38
    simpa using h
  have hprev := st257_p38
  have hstep := st257_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p40 : ((15282742799271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT257 (i+1))
      = (∑ i ∈ Finset.range 39, stT257 (i+1)) + stT257 40 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 39
    simpa using h
  have hprev := st257_p39
  have hstep := st257_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p41 : ((2105296236573/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT257 (i+1))
      = (∑ i ∈ Finset.range 40, stT257 (i+1)) + stT257 41 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 40
    simpa using h
  have hprev := st257_p40
  have hstep := st257_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p42 : ((9192073431861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT257 (i+1))
      = (∑ i ∈ Finset.range 41, stT257 (i+1)) + stT257 42 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 41
    simpa using h
  have hprev := st257_p41
  have hstep := st257_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p43 : ((9925890113921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT257 (i+1))
      = (∑ i ∈ Finset.range 42, stT257 (i+1)) + stT257 43 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 42
    simpa using h
  have hprev := st257_p42
  have hstep := st257_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p44 : ((10526003684619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT257 (i+1))
      = (∑ i ∈ Finset.range 43, stT257 (i+1)) + stT257 44 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 43
    simpa using h
  have hprev := st257_p43
  have hstep := st257_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p45 : ((541266251851/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT257 (i+1))
      = (∑ i ∈ Finset.range 44, stT257 (i+1)) + stT257 45 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 44
    simpa using h
  have hprev := st257_p44
  have hstep := st257_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p46 : ((33323327137/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT257 (i+1))
      = (∑ i ∈ Finset.range 45, stT257 (i+1)) + stT257 46 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 45
    simpa using h
  have hprev := st257_p45
  have hstep := st257_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p47 : ((2011758744973/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT257 (i+1))
      = (∑ i ∈ Finset.range 46, stT257 (i+1)) + stT257 47 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 46
    simpa using h
  have hprev := st257_p46
  have hstep := st257_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p48 : ((1872996906461/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT257 (i+1))
      = (∑ i ∈ Finset.range 47, stT257 (i+1)) + stT257 48 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 47
    simpa using h
  have hprev := st257_p47
  have hstep := st257_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p49 : ((9148612302899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT257 (i+1))
      = (∑ i ∈ Finset.range 48, stT257 (i+1)) + stT257 49 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 48
    simpa using h
  have hprev := st257_p48
  have hstep := st257_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p50 : ((19295114511793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT257 (i+1))
      = (∑ i ∈ Finset.range 49, stT257 (i+1)) + stT257 50 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 49
    simpa using h
  have hprev := st257_p49
  have hstep := st257_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p51 : ((20581225482553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT257 (i+1))
      = (∑ i ∈ Finset.range 50, stT257 (i+1)) + stT257 51 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 50
    simpa using h
  have hprev := st257_p50
  have hstep := st257_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p52 : ((10201779552343/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT257 (i+1))
      = (∑ i ∈ Finset.range 51, stT257 (i+1)) + stT257 52 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 51
    simpa using h
  have hprev := st257_p51
  have hstep := st257_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p53 : ((475798243093/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT257 (i+1))
      = (∑ i ∈ Finset.range 52, stT257 (i+1)) + stT257 53 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 52
    simpa using h
  have hprev := st257_p52
  have hstep := st257_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p54 : ((4708451353593/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT257 (i+1))
      = (∑ i ∈ Finset.range 53, stT257 (i+1)) + stT257 54 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 53
    simpa using h
  have hprev := st257_p53
  have hstep := st257_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p55 : ((504177963159/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT257 (i+1))
      = (∑ i ∈ Finset.range 54, stT257 (i+1)) + stT257 55 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 54
    simpa using h
  have hprev := st257_p54
  have hstep := st257_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p56 : ((10128761818089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT257 (i+1))
      = (∑ i ∈ Finset.range 55, stT257 (i+1)) + stT257 56 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 55
    simpa using h
  have hprev := st257_p55
  have hstep := st257_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p57 : ((3787800538293/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT257 (i+1))
      = (∑ i ∈ Finset.range 56, stT257 (i+1)) + stT257 57 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 56
    simpa using h
  have hprev := st257_p56
  have hstep := st257_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p58 : ((19375010844921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT257 (i+1))
      = (∑ i ∈ Finset.range 57, stT257 (i+1)) + stT257 58 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 57
    simpa using h
  have hprev := st257_p57
  have hstep := st257_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p59 : ((20405291950407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT257 (i+1))
      = (∑ i ∈ Finset.range 58, stT257 (i+1)) + stT257 59 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 58
    simpa using h
  have hprev := st257_p58
  have hstep := st257_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p60 : ((4821246463583/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT257 (i+1))
      = (∑ i ∈ Finset.range 59, stT257 (i+1)) + stT257 60 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 59
    simpa using h
  have hprev := st257_p59
  have hstep := st257_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p61 : ((3842699802391/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT257 (i+1))
      = (∑ i ∈ Finset.range 60, stT257 (i+1)) + stT257 61 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 60
    simpa using h
  have hprev := st257_p60
  have hstep := st257_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p62 : ((2542663361249/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT257 (i+1))
      = (∑ i ∈ Finset.range 61, stT257 (i+1)) + stT257 62 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 61
    simpa using h
  have hprev := st257_p61
  have hstep := st257_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p63 : ((9615660935353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT257 (i+1))
      = (∑ i ∈ Finset.range 62, stT257 (i+1)) + stT257 63 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 62
    simpa using h
  have hprev := st257_p62
  have hstep := st257_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p64 : ((9722720310353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT257 (i+1))
      = (∑ i ∈ Finset.range 63, stT257 (i+1)) + stT257 64 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 63
    simpa using h
  have hprev := st257_p63
  have hstep := st257_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p65 : ((4043277396197/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT257 (i+1))
      = (∑ i ∈ Finset.range 64, stT257 (i+1)) + stT257 65 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 64
    simpa using h
  have hprev := st257_p64
  have hstep := st257_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p66 : ((759757922467/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT257 (i+1))
      = (∑ i ∈ Finset.range 65, stT257 (i+1)) + stT257 66 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 65
    simpa using h
  have hprev := st257_p65
  have hstep := st257_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p67 : ((19998525047383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT257 (i+1))
      = (∑ i ∈ Finset.range 66, stT257 (i+1)) + stT257 67 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 66
    simpa using h
  have hprev := st257_p66
  have hstep := st257_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p68 : ((19640544631941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT257 (i+1))
      = (∑ i ∈ Finset.range 67, stT257 (i+1)) + stT257 68 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 67
    simpa using h
  have hprev := st257_p67
  have hstep := st257_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p69 : ((9636223342403/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT257 (i+1))
      = (∑ i ∈ Finset.range 68, stT257 (i+1)) + stT257 69 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 68
    simpa using h
  have hprev := st257_p68
  have hstep := st257_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p70 : ((10091806008707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT257 (i+1))
      = (∑ i ∈ Finset.range 69, stT257 (i+1)) + stT257 70 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 69
    simpa using h
  have hprev := st257_p69
  have hstep := st257_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p71 : ((9510208061441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT257 (i+1))
      = (∑ i ∈ Finset.range 70, stT257 (i+1)) + stT257 71 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 70
    simpa using h
  have hprev := st257_p70
  have hstep := st257_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p72 : ((4032274302569/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT257 (i+1))
      = (∑ i ∈ Finset.range 71, stT257 (i+1)) + stT257 72 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 71
    simpa using h
  have hprev := st257_p71
  have hstep := st257_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p73 : ((19233988542173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT257 (i+1))
      = (∑ i ∈ Finset.range 72, stT257 (i+1)) + stT257 73 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 72
    simpa using h
  have hprev := st257_p72
  have hstep := st257_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p74 : ((19850961054413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT257 (i+1))
      = (∑ i ∈ Finset.range 73, stT257 (i+1)) + stT257 74 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 73
    simpa using h
  have hprev := st257_p73
  have hstep := st257_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p75 : ((9781836300157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT257 (i+1))
      = (∑ i ∈ Finset.range 74, stT257 (i+1)) + stT257 75 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 74
    simpa using h
  have hprev := st257_p74
  have hstep := st257_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p76 : ((19550957229599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT257 (i+1))
      = (∑ i ∈ Finset.range 75, stT257 (i+1)) + stT257 76 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 75
    simpa using h
  have hprev := st257_p75
  have hstep := st257_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p77 : ((9904782186717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT257 (i+1))
      = (∑ i ∈ Finset.range 76, stT257 (i+1)) + stT257 77 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 76
    simpa using h
  have hprev := st257_p76
  have hstep := st257_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p78 : ((2420609330499/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT257 (i+1))
      = (∑ i ∈ Finset.range 77, stT257 (i+1)) + stT257 78 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 77
    simpa using h
  have hprev := st257_p77
  have hstep := st257_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p79 : ((19939288936929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT257 (i+1))
      = (∑ i ∈ Finset.range 78, stT257 (i+1)) + stT257 79 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 78
    simpa using h
  have hprev := st257_p78
  have hstep := st257_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p80 : ((19283223231627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT257 (i+1))
      = (∑ i ∈ Finset.range 79, stT257 (i+1)) + stT257 80 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 79
    simpa using h
  have hprev := st257_p79
  have hstep := st257_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p81 : ((19980125384159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT257 (i+1))
      = (∑ i ∈ Finset.range 80, stT257 (i+1)) + stT257 81 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 80
    simpa using h
  have hprev := st257_p80
  have hstep := st257_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p82 : ((19277254753743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT257 (i+1))
      = (∑ i ∈ Finset.range 81, stT257 (i+1)) + stT257 82 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 81
    simpa using h
  have hprev := st257_p81
  have hstep := st257_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p83 : ((19953181599701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT257 (i+1))
      = (∑ i ∈ Finset.range 82, stT257 (i+1)) + stT257 83 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 82
    simpa using h
  have hprev := st257_p82
  have hstep := st257_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p84 : ((19337284207591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT257 (i+1))
      = (∑ i ∈ Finset.range 83, stT257 (i+1)) + stT257 84 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 83
    simpa using h
  have hprev := st257_p83
  have hstep := st257_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p85 : ((19856860716543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT257 (i+1))
      = (∑ i ∈ Finset.range 84, stT257 (i+1)) + stT257 85 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 84
    simpa using h
  have hprev := st257_p84
  have hstep := st257_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p86 : ((19473025551631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT257 (i+1))
      = (∑ i ∈ Finset.range 85, stT257 (i+1)) + stT257 86 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 85
    simpa using h
  have hprev := st257_p85
  have hstep := st257_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p87 : ((19679069396351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT257 (i+1))
      = (∑ i ∈ Finset.range 86, stT257 (i+1)) + stT257 87 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 86
    simpa using h
  have hprev := st257_p86
  have hstep := st257_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p88 : ((4922679402783/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT257 (i+1))
      = (∑ i ∈ Finset.range 87, stT257 (i+1)) + stT257 88 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 87
    simpa using h
  have hprev := st257_p87
  have hstep := st257_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p89 : ((9714928701661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT257 (i+1))
      = (∑ i ∈ Finset.range 88, stT257 (i+1)) + stT257 89 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 88
    simpa using h
  have hprev := st257_p88
  have hstep := st257_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p90 : ((9976164322021/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT257 (i+1))
      = (∑ i ∈ Finset.range 89, stT257 (i+1)) + stT257 90 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 89
    simpa using h
  have hprev := st257_p89
  have hstep := st257_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p91 : ((9592758276411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT257 (i+1))
      = (∑ i ∈ Finset.range 90, stT257 (i+1)) + stT257 91 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 90
    simpa using h
  have hprev := st257_p90
  have hstep := st257_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p92 : ((10069235053137/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT257 (i+1))
      = (∑ i ∈ Finset.range 91, stT257 (i+1)) + stT257 92 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 91
    simpa using h
  have hprev := st257_p91
  have hstep := st257_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p93 : ((9551498399913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT257 (i+1))
      = (∑ i ∈ Finset.range 92, stT257 (i+1)) + stT257 93 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 92
    simpa using h
  have hprev := st257_p92
  have hstep := st257_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p94 : ((20075817615711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT257 (i+1))
      = (∑ i ∈ Finset.range 93, stT257 (i+1)) + stT257 94 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 93
    simpa using h
  have hprev := st257_p93
  have hstep := st257_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p95 : ((9666244324179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT257 (i+1))
      = (∑ i ∈ Finset.range 94, stT257 (i+1)) + stT257 95 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 94
    simpa using h
  have hprev := st257_p94
  have hstep := st257_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p96 : ((9845882119449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT257 (i+1))
      = (∑ i ∈ Finset.range 95, stT257 (i+1)) + stT257 96 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 95
    simpa using h
  have hprev := st257_p95
  have hstep := st257_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p97 : ((247647823217/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT257 (i+1))
      = (∑ i ∈ Finset.range 96, stT257 (i+1)) + stT257 97 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 96
    simpa using h
  have hprev := st257_p96
  have hstep := st257_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p98 : ((2402669382919/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT257 (i+1))
      = (∑ i ∈ Finset.range 97, stT257 (i+1)) + stT257 98 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 97
    simpa using h
  have hprev := st257_p97
  have hstep := st257_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p99 : ((4028277005771/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT257 (i+1))
      = (∑ i ∈ Finset.range 98, stT257 (i+1)) + stT257 99 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 98
    simpa using h
  have hprev := st257_p98
  have hstep := st257_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p100 : ((3830352605771/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT257 (i+1))
      = (∑ i ∈ Finset.range 99, stT257 (i+1)) + stT257 100 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 99
    simpa using h
  have hprev := st257_p99
  have hstep := st257_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p101 : ((3978786255209/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT257 (i+1))
      = (∑ i ∈ Finset.range 100, stT257 (i+1)) + stT257 101 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 100
    simpa using h
  have hprev := st257_p100
  have hstep := st257_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p102 : ((19665872467501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT257 (i+1))
      = (∑ i ∈ Finset.range 101, stT257 (i+1)) + stT257 102 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 101
    simpa using h
  have hprev := st257_p101
  have hstep := st257_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p103 : ((19280382796931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT257 (i+1))
      = (∑ i ∈ Finset.range 102, stT257 (i+1)) + stT257 103 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 102
    simpa using h
  have hprev := st257_p102
  have hstep := st257_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p104 : ((20135937866351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT257 (i+1))
      = (∑ i ∈ Finset.range 103, stT257 (i+1)) + stT257 104 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 103
    simpa using h
  have hprev := st257_p103
  have hstep := st257_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p105 : ((1198397510333/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT257 (i+1))
      = (∑ i ∈ Finset.range 104, stT257 (i+1)) + stT257 105 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 104
    simpa using h
  have hprev := st257_p104
  have hstep := st257_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p106 : ((1237194518373/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT257 (i+1))
      = (∑ i ∈ Finset.range 105, stT257 (i+1)) + stT257 106 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 105
    simpa using h
  have hprev := st257_p105
  have hstep := st257_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p107 : ((1239306715691/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT257 (i+1))
      = (∑ i ∈ Finset.range 106, stT257 (i+1)) + stT257 107 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 106
    simpa using h
  have hprev := st257_p106
  have hstep := st257_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p108 : ((19148110057301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT257 (i+1))
      = (∑ i ∈ Finset.range 107, stT257 (i+1)) + stT257 108 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 107
    simpa using h
  have hprev := st257_p107
  have hstep := st257_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p109 : ((20105819202529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT257 (i+1))
      = (∑ i ∈ Finset.range 108, stT257 (i+1)) + stT257 109 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 108
    simpa using h
  have hprev := st257_p108
  have hstep := st257_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p110 : ((19429661381449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT257 (i+1))
      = (∑ i ∈ Finset.range 109, stT257 (i+1)) + stT257 110 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 109
    simpa using h
  have hprev := st257_p109
  have hstep := st257_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p111 : ((19403483603809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT257 (i+1))
      = (∑ i ∈ Finset.range 110, stT257 (i+1)) + stT257 111 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 110
    simpa using h
  have hprev := st257_p110
  have hstep := st257_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p112 : ((20122111097173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT257 (i+1))
      = (∑ i ∈ Finset.range 111, stT257 (i+1)) + stT257 112 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 111
    simpa using h
  have hprev := st257_p111
  have hstep := st257_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p113 : ((1919197979347/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT257 (i+1))
      = (∑ i ∈ Finset.range 112, stT257 (i+1)) + stT257 113 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 112
    simpa using h
  have hprev := st257_p112
  have hstep := st257_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p114 : ((1967587954591/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT257 (i+1))
      = (∑ i ∈ Finset.range 113, stT257 (i+1)) + stT257 114 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 113
    simpa using h
  have hprev := st257_p113
  have hstep := st257_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p115 : ((1999910874491/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT257 (i+1))
      = (∑ i ∈ Finset.range 114, stT257 (i+1)) + stT257 115 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 114
    simpa using h
  have hprev := st257_p114
  have hstep := st257_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p116 : ((149313537577/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT257 (i+1))
      = (∑ i ∈ Finset.range 115, stT257 (i+1)) + stT257 116 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 115
    simpa using h
  have hprev := st257_p115
  have hstep := st257_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p117 : ((2482028466107/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT257 (i+1))
      = (∑ i ∈ Finset.range 116, stT257 (i+1)) + stT257 117 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 116
    simpa using h
  have hprev := st257_p116
  have hstep := st257_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p118 : ((9936751149983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT257 (i+1))
      = (∑ i ∈ Finset.range 117, stT257 (i+1)) + stT257 118 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 117
    simpa using h
  have hprev := st257_p117
  have hstep := st257_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p119 : ((19106249987839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT257 (i+1))
      = (∑ i ∈ Finset.range 118, stT257 (i+1)) + stT257 119 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 118
    simpa using h
  have hprev := st257_p118
  have hstep := st257_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p120 : ((19942767541039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT257 (i+1))
      = (∑ i ∈ Finset.range 119, stT257 (i+1)) + stT257 120 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 119
    simpa using h
  have hprev := st257_p119
  have hstep := st257_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p121 : ((309479307957/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT257 (i+1))
      = (∑ i ∈ Finset.range 120, stT257 (i+1)) + stT257 121 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 120
    simpa using h
  have hprev := st257_p120
  have hstep := st257_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p122 : ((9555534167307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT257 (i+1))
      = (∑ i ∈ Finset.range 121, stT257 (i+1)) + stT257 122 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 121
    simpa using h
  have hprev := st257_p121
  have hstep := st257_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p123 : ((9979172526929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT257 (i+1))
      = (∑ i ∈ Finset.range 122, stT257 (i+1)) + stT257 123 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 122
    simpa using h
  have hprev := st257_p122
  have hstep := st257_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p124 : ((3962829951299/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT257 (i+1))
      = (∑ i ∈ Finset.range 123, stT257 (i+1)) + stT257 124 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 123
    simpa using h
  have hprev := st257_p123
  have hstep := st257_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p125 : ((19104615229371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT257 (i+1))
      = (∑ i ∈ Finset.range 124, stT257 (i+1)) + stT257 125 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 124
    simpa using h
  have hprev := st257_p124
  have hstep := st257_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p126 : ((19910939884631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT257 (i+1))
      = (∑ i ∈ Finset.range 125, stT257 (i+1)) + stT257 126 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 125
    simpa using h
  have hprev := st257_p125
  have hstep := st257_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p127 : ((1989160171353/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT257 (i+1))
      = (∑ i ∈ Finset.range 126, stT257 (i+1)) + stT257 127 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 126
    simpa using h
  have hprev := st257_p126
  have hstep := st257_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p128 : ((1910217839661/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT257 (i+1))
      = (∑ i ∈ Finset.range 127, stT257 (i+1)) + stT257 128 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 127
    simpa using h
  have hprev := st257_p127
  have hstep := st257_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p129 : ((989477681783/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT257 (i+1))
      = (∑ i ∈ Finset.range 128, stT257 (i+1)) + stT257 129 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 128
    simpa using h
  have hprev := st257_p128
  have hstep := st257_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p130 : ((500399153959/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT257 (i+1))
      = (∑ i ∈ Finset.range 129, stT257 (i+1)) + stT257 130 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 129
    simpa using h
  have hprev := st257_p129
  have hstep := st257_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p131 : ((478761325411/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT257 (i+1))
      = (∑ i ∈ Finset.range 130, stT257 (i+1)) + stT257 131 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 130
    simpa using h
  have hprev := st257_p130
  have hstep := st257_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p132 : ((1223977493857/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT257 (i+1))
      = (∑ i ∈ Finset.range 131, stT257 (i+1)) + stT257 132 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 131
    simpa using h
  have hprev := st257_p131
  have hstep := st257_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p133 : ((10064739907279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT257 (i+1))
      = (∑ i ∈ Finset.range 132, stT257 (i+1)) + stT257 133 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 132
    simpa using h
  have hprev := st257_p132
  have hstep := st257_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p134 : ((9655625370783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT257 (i+1))
      = (∑ i ∈ Finset.range 133, stT257 (i+1)) + stT257 134 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 133
    simpa using h
  have hprev := st257_p133
  have hstep := st257_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p135 : ((9661335863153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT257 (i+1))
      = (∑ i ∈ Finset.range 134, stT257 (i+1)) + stT257 135 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 134
    simpa using h
  have hprev := st257_p134
  have hstep := st257_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p136 : ((10065629621281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT257 (i+1))
      = (∑ i ∈ Finset.range 135, stT257 (i+1)) + stT257 136 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 135
    simpa using h
  have hprev := st257_p135
  have hstep := st257_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p137 : ((9806670294049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT257 (i+1))
      = (∑ i ∈ Finset.range 136, stT257 (i+1)) + stT257 137 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 136
    simpa using h
  have hprev := st257_p136
  have hstep := st257_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p138 : ((19117795796917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT257 (i+1))
      = (∑ i ∈ Finset.range 137, stT257 (i+1)) + stT257 138 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 137
    simpa using h
  have hprev := st257_p137
  have hstep := st257_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p139 : ((19918380941793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT257 (i+1))
      = (∑ i ∈ Finset.range 138, stT257 (i+1)) + stT257 139 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 138
    simpa using h
  have hprev := st257_p138
  have hstep := st257_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p140 : ((3994640033139/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT257 (i+1))
      = (∑ i ∈ Finset.range 139, stT257 (i+1)) + stT257 140 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 139
    simpa using h
  have hprev := st257_p139
  have hstep := st257_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p141 : ((19146709666439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT257 (i+1))
      = (∑ i ∈ Finset.range 140, stT257 (i+1)) + stT257 141 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 140
    simpa using h
  have hprev := st257_p140
  have hstep := st257_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p142 : ((3900653184961/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT257 (i+1))
      = (∑ i ∈ Finset.range 141, stT257 (i+1)) + stT257 142 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 141
    simpa using h
  have hprev := st257_p141
  have hstep := st257_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p143 : ((20157847730177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT257 (i+1))
      = (∑ i ∈ Finset.range 142, stT257 (i+1)) + stT257 143 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 142
    simpa using h
  have hprev := st257_p142
  have hstep := st257_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p144 : ((3901865608939/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT257 (i+1))
      = (∑ i ∈ Finset.range 143, stT257 (i+1)) + stT257 144 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 143
    simpa using h
  have hprev := st257_p143
  have hstep := st257_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p145 : ((3826448668569/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT257 (i+1))
      = (∑ i ∈ Finset.range 144, stT257 (i+1)) + stT257 145 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 144
    simpa using h
  have hprev := st257_p144
  have hstep := st257_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p146 : ((797141800453/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT257 (i+1))
      = (∑ i ∈ Finset.range 145, stT257 (i+1)) + stT257 146 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 145
    simpa using h
  have hprev := st257_p145
  have hstep := st257_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p147 : ((20004502028423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT257 (i+1))
      = (∑ i ∈ Finset.range 146, stT257 (i+1)) + stT257 147 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 146
    simpa using h
  have hprev := st257_p146
  have hstep := st257_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p148 : ((19185050280953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT257 (i+1))
      = (∑ i ∈ Finset.range 147, stT257 (i+1)) + stT257 148 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 147
    simpa using h
  have hprev := st257_p147
  have hstep := st257_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p149 : ((19379090058689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT257 (i+1))
      = (∑ i ∈ Finset.range 148, stT257 (i+1)) + stT257 149 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 148
    simpa using h
  have hprev := st257_p148
  have hstep := st257_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p150 : ((20135028999857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT257 (i+1))
      = (∑ i ∈ Finset.range 149, stT257 (i+1)) + stT257 150 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 149
    simpa using h
  have hprev := st257_p149
  have hstep := st257_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p151 : ((9863800734031/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT257 (i+1))
      = (∑ i ∈ Finset.range 150, stT257 (i+1)) + stT257 151 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 150
    simpa using h
  have hprev := st257_p150
  have hstep := st257_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p152 : ((9540896205907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT257 (i+1))
      = (∑ i ∈ Finset.range 151, stT257 (i+1)) + stT257 152 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 151
    simpa using h
  have hprev := st257_p151
  have hstep := st257_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p153 : ((1964124766343/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT257 (i+1))
      = (∑ i ∈ Finset.range 152, stT257 (i+1)) + stT257 153 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 152
    simpa using h
  have hprev := st257_p152
  have hstep := st257_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p154 : ((1260135353411/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT257 (i+1))
      = (∑ i ∈ Finset.range 153, stT257 (i+1)) + stT257 154 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 153
    simpa using h
  have hprev := st257_p153
  have hstep := st257_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p155 : ((2437990657267/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT257 (i+1))
      = (∑ i ∈ Finset.range 154, stT257 (i+1)) + stT257 155 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 154
    simpa using h
  have hprev := st257_p154
  have hstep := st257_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p156 : ((1193765129121/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT257 (i+1))
      = (∑ i ∈ Finset.range 155, stT257 (i+1)) + stT257 156 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 155
    simpa using h
  have hprev := st257_p155
  have hstep := st257_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p157 : ((99081918939/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT257 (i+1))
      = (∑ i ∈ Finset.range 156, stT257 (i+1)) + stT257 157 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 156
    simpa using h
  have hprev := st257_p156
  have hstep := st257_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p158 : ((20123264331651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT257 (i+1))
      = (∑ i ∈ Finset.range 157, stT257 (i+1)) + stT257 158 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 157
    simpa using h
  have hprev := st257_p157
  have hstep := st257_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p159 : ((19377010330171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT257 (i+1))
      = (∑ i ∈ Finset.range 158, stT257 (i+1)) + stT257 159 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 158
    simpa using h
  have hprev := st257_p158
  have hstep := st257_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p160 : ((19139637734821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT257 (i+1))
      = (∑ i ∈ Finset.range 159, stT257 (i+1)) + stT257 160 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 159
    simpa using h
  have hprev := st257_p159
  have hstep := st257_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p161 : ((19898209372021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT257 (i+1))
      = (∑ i ∈ Finset.range 160, stT257 (i+1)) + stT257 161 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 160
    simpa using h
  have hprev := st257_p160
  have hstep := st257_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p162 : ((20095530611447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT257 (i+1))
      = (∑ i ∈ Finset.range 161, stT257 (i+1)) + stT257 162 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 161
    simpa using h
  have hprev := st257_p161
  have hstep := st257_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p163 : ((4833818300939/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT257 (i+1))
      = (∑ i ∈ Finset.range 162, stT257 (i+1)) + stT257 163 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 162
    simpa using h
  have hprev := st257_p162
  have hstep := st257_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p164 : ((19148030968853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT257 (i+1))
      = (∑ i ∈ Finset.range 163, stT257 (i+1)) + stT257 164 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 163
    simpa using h
  have hprev := st257_p163
  have hstep := st257_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p165 : ((19902175215919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT257 (i+1))
      = (∑ i ∈ Finset.range 164, stT257 (i+1)) + stT257 165 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 164
    simpa using h
  have hprev := st257_p164
  have hstep := st257_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p166 : ((20108048227269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT257 (i+1))
      = (∑ i ∈ Finset.range 165, stT257 (i+1)) + stT257 166 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 165
    simpa using h
  have hprev := st257_p165
  have hstep := st257_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p167 : ((3873556066241/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT257 (i+1))
      = (∑ i ∈ Finset.range 166, stT257 (i+1)) + stT257 167 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 166
    simpa using h
  have hprev := st257_p166
  have hstep := st257_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p168 : ((1911611534339/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT257 (i+1))
      = (∑ i ∈ Finset.range 167, stT257 (i+1)) + stT257 168 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 167
    simpa using h
  have hprev := st257_p167
  have hstep := st257_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p169 : ((198310661669/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT257 (i+1))
      = (∑ i ∈ Finset.range 168, stT257 (i+1)) + stT257 169 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 168
    simpa using h
  have hprev := st257_p168
  have hstep := st257_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p170 : ((251904869619/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT257 (i+1))
      = (∑ i ∈ Finset.range 169, stT257 (i+1)) + stT257 170 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 169
    simpa using h
  have hprev := st257_p169
  have hstep := st257_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p171 : ((24349647689/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT257 (i+1))
      = (∑ i ∈ Finset.range 170, stT257 (i+1)) + stT257 171 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 170
    simpa using h
  have hprev := st257_p170
  have hstep := st257_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p172 : ((2383681777199/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT257 (i+1))
      = (∑ i ∈ Finset.range 171, stT257 (i+1)) + stT257 172 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 171
    simpa using h
  have hprev := st257_p171
  have hstep := st257_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p173 : ((1229695098607/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT257 (i+1))
      = (∑ i ∈ Finset.range 172, stT257 (i+1)) + stT257 173 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 172
    simpa using h
  have hprev := st257_p172
  have hstep := st257_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p174 : ((10092720276549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT257 (i+1))
      = (∑ i ∈ Finset.range 173, stT257 (i+1)) + stT257 174 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 173
    simpa using h
  have hprev := st257_p173
  have hstep := st257_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p175 : ((19678905380991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT257 (i+1))
      = (∑ i ∈ Finset.range 174, stT257 (i+1)) + stT257 175 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 174
    simpa using h
  have hprev := st257_p174
  have hstep := st257_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p176 : ((9534418304339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT257 (i+1))
      = (∑ i ∈ Finset.range 175, stT257 (i+1)) + stT257 176 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 175
    simpa using h
  have hprev := st257_p175
  have hstep := st257_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p177 : ((9718902298579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT257 (i+1))
      = (∑ i ∈ Finset.range 176, stT257 (i+1)) + stT257 177 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 176
    simpa using h
  have hprev := st257_p176
  have hstep := st257_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p178 : ((20130944632373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT257 (i+1))
      = (∑ i ∈ Finset.range 177, stT257 (i+1)) + stT257 178 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 177
    simpa using h
  have hprev := st257_p177
  have hstep := st257_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p179 : ((3987860707369/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT257 (i+1))
      = (∑ i ∈ Finset.range 178, stT257 (i+1)) + stT257 179 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 178
    simpa using h
  have hprev := st257_p178
  have hstep := st257_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p180 : ((19199287267229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT257 (i+1))
      = (∑ i ∈ Finset.range 179, stT257 (i+1)) + stT257 180 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 179
    simpa using h
  have hprev := st257_p179
  have hstep := st257_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p181 : ((599354776207/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT257 (i+1))
      = (∑ i ∈ Finset.range 180, stT257 (i+1)) + stT257 181 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 180
    simpa using h
  have hprev := st257_p180
  have hstep := st257_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p182 : ((9954187838809/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT257 (i+1))
      = (∑ i ∈ Finset.range 181, stT257 (i+1)) + stT257 182 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 181
    simpa using h
  have hprev := st257_p181
  have hstep := st257_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p183 : ((1007888037631/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT257 (i+1))
      = (∑ i ∈ Finset.range 182, stT257 (i+1)) + stT257 183 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 182
    simpa using h
  have hprev := st257_p182
  have hstep := st257_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p184 : ((243949045129/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT257 (i+1))
      = (∑ i ∈ Finset.range 183, stT257 (i+1)) + stT257 184 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 183
    simpa using h
  have hprev := st257_p183
  have hstep := st257_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p185 : ((380932452839/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT257 (i+1))
      = (∑ i ∈ Finset.range 184, stT257 (i+1)) + stT257 185 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 184
    simpa using h
  have hprev := st257_p184
  have hstep := st257_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p186 : ((1951511874579/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT257 (i+1))
      = (∑ i ∈ Finset.range 185, stT257 (i+1)) + stT257 186 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 185
    simpa using h
  have hprev := st257_p185
  have hstep := st257_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p187 : ((10078342073503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT257 (i+1))
      = (∑ i ∈ Finset.range 186, stT257 (i+1)) + stT257 187 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 186
    simpa using h
  have hprev := st257_p186
  have hstep := st257_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p188 : ((19940915533731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT257 (i+1))
      = (∑ i ∈ Finset.range 187, stT257 (i+1)) + stT257 188 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 187
    simpa using h
  have hprev := st257_p187
  have hstep := st257_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p189 : ((19216622682697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT257 (i+1))
      = (∑ i ∈ Finset.range 188, stT257 (i+1)) + stT257 189 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 188
    simpa using h
  have hprev := st257_p188
  have hstep := st257_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p190 : ((2391063915577/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT257 (i+1))
      = (∑ i ∈ Finset.range 189, stT257 (i+1)) + stT257 190 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 189
    simpa using h
  have hprev := st257_p189
  have hstep := st257_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p191 : ((1238112659647/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT257 (i+1))
      = (∑ i ∈ Finset.range 190, stT257 (i+1)) + stT257 191 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 190
    simpa using h
  have hprev := st257_p190
  have hstep := st257_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p192 : ((10100265556511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT257 (i+1))
      = (∑ i ∈ Finset.range 191, stT257 (i+1)) + stT257 192 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 191
    simpa using h
  have hprev := st257_p191
  have hstep := st257_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p193 : ((9851546094399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT257 (i+1))
      = (∑ i ∈ Finset.range 192, stT257 (i+1)) + stT257 193 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 192
    simpa using h
  have hprev := st257_p192
  have hstep := st257_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p194 : ((19080094035933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT257 (i+1))
      = (∑ i ∈ Finset.range 193, stT257 (i+1)) + stT257 194 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 193
    simpa using h
  have hprev := st257_p193
  have hstep := st257_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p195 : ((19271630183057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT257 (i+1))
      = (∑ i ∈ Finset.range 194, stT257 (i+1)) + stT257 195 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 194
    simpa using h
  have hprev := st257_p194
  have hstep := st257_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p196 : ((2498225380039/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT257 (i+1))
      = (∑ i ∈ Finset.range 195, stT257 (i+1)) + stT257 196 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 195
    simpa using h
  have hprev := st257_p195
  have hstep := st257_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p197 : ((5040215298533/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT257 (i+1))
      = (∑ i ∈ Finset.range 196, stT257 (i+1)) + stT257 197 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 196
    simpa using h
  have hprev := st257_p196
  have hstep := st257_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p198 : ((9771663314821/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT257 (i+1))
      = (∑ i ∈ Finset.range 197, stT257 (i+1)) + stT257 198 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 197
    simpa using h
  have hprev := st257_p197
  have hstep := st257_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p199 : ((297465439691/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT257 (i+1))
      = (∑ i ∈ Finset.range 198, stT257 (i+1)) + stT257 199 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 198
    simpa using h
  have hprev := st257_p198
  have hstep := st257_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p200 : ((9686608653169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT257 (i+1))
      = (∑ i ∈ Finset.range 199, stT257 (i+1)) + stT257 200 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 199
    simpa using h
  have hprev := st257_p199
  have hstep := st257_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p201 : ((5015927993177/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT257 (i+1))
      = (∑ i ∈ Finset.range 200, stT257 (i+1)) + stT257 201 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 200
    simpa using h
  have hprev := st257_p200
  have hstep := st257_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p202 : ((10063479153519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT257 (i+1))
      = (∑ i ∈ Finset.range 201, stT257 (i+1)) + stT257 202 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 201
    simpa using h
  have hprev := st257_p201
  have hstep := st257_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p203 : ((121738888281/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT257 (i+1))
      = (∑ i ∈ Finset.range 202, stT257 (i+1)) + stT257 203 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 202
    simpa using h
  have hprev := st257_p202
  have hstep := st257_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p204 : ((4756837731227/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT257 (i+1))
      = (∑ i ∈ Finset.range 203, stT257 (i+1)) + stT257 204 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 203
    simpa using h
  have hprev := st257_p203
  have hstep := st257_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p205 : ((9698302290019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT257 (i+1))
      = (∑ i ∈ Finset.range 204, stT257 (i+1)) + stT257 205 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 204
    simpa using h
  have hprev := st257_p204
  have hstep := st257_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p206 : ((10036918708417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT257 (i+1))
      = (∑ i ∈ Finset.range 205, stT257 (i+1)) + stT257 206 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 205
    simpa using h
  have hprev := st257_p205
  have hstep := st257_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p207 : ((10067899082921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT257 (i+1))
      = (∑ i ∈ Finset.range 206, stT257 (i+1)) + stT257 207 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 206
    simpa using h
  have hprev := st257_p206
  have hstep := st257_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p208 : ((9751544202793/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT257 (i+1))
      = (∑ i ∈ Finset.range 207, stT257 (i+1)) + stT257 208 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 207
    simpa using h
  have hprev := st257_p207
  have hstep := st257_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p209 : ((19026655173321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT257 (i+1))
      = (∑ i ∈ Finset.range 208, stT257 (i+1)) + stT257 209 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 208
    simpa using h
  have hprev := st257_p208
  have hstep := st257_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p210 : ((19337303114501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT257 (i+1))
      = (∑ i ∈ Finset.range 209, stT257 (i+1)) + stT257 210 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 209
    simpa using h
  have hprev := st257_p209
  have hstep := st257_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p211 : ((20020980272873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT257 (i+1))
      = (∑ i ∈ Finset.range 210, stT257 (i+1)) + stT257 211 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 210
    simpa using h
  have hprev := st257_p210
  have hstep := st257_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p212 : ((4036646899633/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT257 (i+1))
      = (∑ i ∈ Finset.range 211, stT257 (i+1)) + stT257 212 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 211
    simpa using h
  have hprev := st257_p211
  have hstep := st257_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p213 : ((19617663053029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT257 (i+1))
      = (∑ i ∈ Finset.range 212, stT257 (i+1)) + stT257 213 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 212
    simpa using h
  have hprev := st257_p212
  have hstep := st257_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p214 : ((19054923436867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT257 (i+1))
      = (∑ i ∈ Finset.range 213, stT257 (i+1)) + stT257 214 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 213
    simpa using h
  have hprev := st257_p213
  have hstep := st257_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p215 : ((19211143710483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT257 (i+1))
      = (∑ i ∈ Finset.range 214, stT257 (i+1)) + stT257 215 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 214
    simpa using h
  have hprev := st257_p214
  have hstep := st257_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p216 : ((19884179672737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT257 (i+1))
      = (∑ i ∈ Finset.range 215, stT257 (i+1)) + stT257 216 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 215
    simpa using h
  have hprev := st257_p215
  have hstep := st257_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p217 : ((20227784030621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT257 (i+1))
      = (∑ i ∈ Finset.range 216, stT257 (i+1)) + stT257 217 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 216
    simpa using h
  have hprev := st257_p216
  have hstep := st257_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p218 : ((19817421861509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT257 (i+1))
      = (∑ i ∈ Finset.range 217, stT257 (i+1)) + stT257 218 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 217
    simpa using h
  have hprev := st257_p217
  have hstep := st257_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p219 : ((19163712920309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT257 (i+1))
      = (∑ i ∈ Finset.range 218, stT257 (i+1)) + stT257 219 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 218
    simpa using h
  have hprev := st257_p218
  have hstep := st257_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p220 : ((19067118937909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT257 (i+1))
      = (∑ i ∈ Finset.range 219, stT257 (i+1)) + stT257 220 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 219
    simpa using h
  have hprev := st257_p219
  have hstep := st257_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p221 : ((19640918243989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT257 (i+1))
      = (∑ i ∈ Finset.range 220, stT257 (i+1)) + stT257 221 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 220
    simpa using h
  have hprev := st257_p220
  have hstep := st257_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p222 : ((4038100343461/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT257 (i+1))
      = (∑ i ∈ Finset.range 221, stT257 (i+1)) + stT257 222 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 221
    simpa using h
  have hprev := st257_p221
  have hstep := st257_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p223 : ((4012070110451/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT257 (i+1))
      = (∑ i ∈ Finset.range 222, stT257 (i+1)) + stT257 223 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 222
    simpa using h
  have hprev := st257_p222
  have hstep := st257_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p224 : ((19409056750291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT257 (i+1))
      = (∑ i ∈ Finset.range 223, stT257 (i+1)) + stT257 224 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 223
    simpa using h
  have hprev := st257_p223
  have hstep := st257_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p225 : ((380096824297/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT257 (i+1))
      = (∑ i ∈ Finset.range 224, stT257 (i+1)) + stT257 225 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 224
    simpa using h
  have hprev := st257_p224
  have hstep := st257_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p226 : ((965843659819/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT257 (i+1))
      = (∑ i ∈ Finset.range 225, stT257 (i+1)) + stT257 226 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 225
    simpa using h
  have hprev := st257_p225
  have hstep := st257_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p227 : ((19979659683227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT257 (i+1))
      = (∑ i ∈ Finset.range 226, stT257 (i+1)) + stT257 227 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 226
    simpa using h
  have hprev := st257_p226
  have hstep := st257_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p228 : ((20230764459787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT257 (i+1))
      = (∑ i ∈ Finset.range 227, stT257 (i+1)) + stT257 228 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 227
    simpa using h
  have hprev := st257_p227
  have hstep := st257_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p229 : ((1236700389157/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT257 (i+1))
      = (∑ i ∈ Finset.range 228, stT257 (i+1)) + stT257 229 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 228
    simpa using h
  have hprev := st257_p228
  have hstep := st257_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p230 : ((1915435739919/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT257 (i+1))
      = (∑ i ∈ Finset.range 229, stT257 (i+1)) + stT257 230 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 229
    simpa using h
  have hprev := st257_p229
  have hstep := st257_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p231 : ((9521179417947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT257 (i+1))
      = (∑ i ∈ Finset.range 230, stT257 (i+1)) + stT257 231 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 230
    simpa using h
  have hprev := st257_p230
  have hstep := st257_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p232 : ((9786088766883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT257 (i+1))
      = (∑ i ∈ Finset.range 231, stT257 (i+1)) + stT257 232 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 231
    simpa using h
  have hprev := st257_p231
  have hstep := st257_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p233 : ((10077561271477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT257 (i+1))
      = (∑ i ∈ Finset.range 232, stT257 (i+1)) + stT257 233 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 232
    simpa using h
  have hprev := st257_p232
  have hstep := st257_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p234 : ((1259547009413/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT257 (i+1))
      = (∑ i ∈ Finset.range 233, stT257 (i+1)) + stT257 234 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 233
    simpa using h
  have hprev := st257_p233
  have hstep := st257_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p235 : ((1957149961379/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT257 (i+1))
      = (∑ i ∈ Finset.range 234, stT257 (i+1)) + stT257 235 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 234
    simpa using h
  have hprev := st257_p234
  have hstep := st257_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p236 : ((3808337663579/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT257 (i+1))
      = (∑ i ∈ Finset.range 235, stT257 (i+1)) + stT257 236 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 235
    simpa using h
  have hprev := st257_p235
  have hstep := st257_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p237 : ((19129664644117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT257 (i+1))
      = (∑ i ∈ Finset.range 236, stT257 (i+1)) + stT257 237 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 236
    simpa using h
  have hprev := st257_p236
  have hstep := st257_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p238 : ((19737913707603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT257 (i+1))
      = (∑ i ∈ Finset.range 237, stT257 (i+1)) + stT257 238 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 237
    simpa using h
  have hprev := st257_p237
  have hstep := st257_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p239 : ((20222138095281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT257 (i+1))
      = (∑ i ∈ Finset.range 238, stT257 (i+1)) + stT257 239 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 238
    simpa using h
  have hprev := st257_p238
  have hstep := st257_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p240 : ((20076791956119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT257 (i+1))
      = (∑ i ∈ Finset.range 239, stT257 (i+1)) + stT257 240 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 239
    simpa using h
  have hprev := st257_p239
  have hstep := st257_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p241 : ((9728414424441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT257 (i+1))
      = (∑ i ∈ Finset.range 240, stT257 (i+1)) + stT257 241 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 240
    simpa using h
  have hprev := st257_p240
  have hstep := st257_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p242 : ((19003918138407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT257 (i+1))
      = (∑ i ∈ Finset.range 241, stT257 (i+1)) + stT257 242 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 241
    simpa using h
  have hprev := st257_p241
  have hstep := st257_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p243 : ((19179968832407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT257 (i+1))
      = (∑ i ∈ Finset.range 242, stT257 (i+1)) + stT257 243 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 242
    simpa using h
  have hprev := st257_p242
  have hstep := st257_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p244 : ((19802181587159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT257 (i+1))
      = (∑ i ∈ Finset.range 243, stT257 (i+1)) + stT257 244 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 243
    simpa using h
  have hprev := st257_p243
  have hstep := st257_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p245 : ((20240881125583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT257 (i+1))
      = (∑ i ∈ Finset.range 244, stT257 (i+1)) + stT257 245 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 244
    simpa using h
  have hprev := st257_p244
  have hstep := st257_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p246 : ((10029303712469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT257 (i+1))
      = (∑ i ∈ Finset.range 245, stT257 (i+1)) + stT257 246 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 245
    simpa using h
  have hprev := st257_p245
  have hstep := st257_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p247 : ((2430034321241/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT257 (i+1))
      = (∑ i ∈ Finset.range 246, stT257 (i+1)) + stT257 247 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 246
    simpa using h
  have hprev := st257_p246
  have hstep := st257_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p248 : ((148420794947/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT257 (i+1))
      = (∑ i ∈ Finset.range 247, stT257 (i+1)) + stT257 248 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 247
    simpa using h
  have hprev := st257_p247
  have hstep := st257_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p249 : ((1197679108659/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT257 (i+1))
      = (∑ i ∈ Finset.range 248, stT257 (i+1)) + stT257 249 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 248
    simpa using h
  have hprev := st257_p248
  have hstep := st257_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_p250 : ((1235695978709/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT257 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT257 (i+1))
      = (∑ i ∈ Finset.range 249, stT257 (i+1)) + stT257 250 := by
    have h := Finset.sum_range_succ (fun i => stT257 (i+1)) 249
    simpa using h
  have hprev := st257_p249
  have hstep := st257_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st257_s250 :
    |Real.sin (((257 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))
      - ((-273717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -346569/5000000) (δ := 3231/250000000) (ψ := -17679/25000) 257 226
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 257`** (evaluated boundary). -/
theorem station_257_sign : hardyG ((((257:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 257 250 (by norm_num) (by norm_num)
    ((-17679/25000 : ℚ) : ℝ)
  have hchain := st257_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT257 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((257 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-17679/25000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st257_c250
  have hsinb := abs_le.mp st257_s250
  have hbdy_lo : ((8835584695099/528394000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((257 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-17679/25000 : ℚ) : ℝ))) / 2
          - ((((257:ℕ)):ℝ))
            * Real.sin (((257 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-17679/25000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((257:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((257:ℝ) * Real.log (250:ℝ) - ((-17679/25000 : ℚ) : ℝ))) / 2
        - ((257:ℝ)) * Real.sin ((257:ℝ) * Real.log (250:ℝ) - ((-17679/25000 : ℚ) : ℝ))
        ≥ ((69851489/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((257:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((69851489/1000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((69851489/1000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((69851489/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((257:ℕ)):ℝ))+1) * (((((257:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((452752402927/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1235695978709/625000000000 : ℚ) : ℝ) + ((8835584695099/528394000000000 : ℚ) : ℝ)
      - ((452752402927/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-17679/25000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((257:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-17679/25000 : ℚ) : ℝ)
        * (riemannZeta (line ((((257:ℕ)):ℝ)))).re
      - Real.sin ((-17679/25000 : ℚ) : ℝ)
        * (riemannZeta (line ((((257:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((257:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((257:ℕ)):ℝ))
      = (((((257:ℕ)):ℝ)) * (Real.log ((((257:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((257:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_257
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
  have hθwin : |(((-17679/25000 : ℚ) : ℝ) + ((56:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((257:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((257:ℕ)):ℝ)))
    (φ := ((-17679/25000 : ℚ) : ℝ) + ((56:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-17679/25000 : ℚ) : ℝ) + ((56:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-17679/25000 : ℚ)) : ℝ) - Real.pi) + ((56:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-17679/25000 : ℚ)) : ℝ) - Real.pi) 56).1,
    (cos_sin_shift ((((-17679/25000 : ℚ)) : ℝ) - Real.pi) 56).2]
  exact cos_sin_flip ((-17679/25000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_257_sign
end AxiomAudit
