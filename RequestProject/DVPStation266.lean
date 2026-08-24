import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 266` (rung-280.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT266 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((266 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((181581/500000 : ℚ) : ℝ))

theorem st266_c1 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((467389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -181581/2000000) (δ := 1/1000000000) (ψ := 181581/500000) 266 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t1 : ((116841/125000 : ℚ) : ℝ) ≤ stT266 1 := by
  have hc : ((116841/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116841/125000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((116841/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c2 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-114383/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 900803/2000000) (δ := 1331/100000000) (ψ := 181581/500000) 266 29
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t2 : ((-25280835867/156250000000 : ℚ) : ℝ) ≤ stT266 2 := by
  have hc : ((-14301/62500 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25280835867/156250000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-14301/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c3 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-238803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7102931/10000000) (δ := 3333/250000000) (ψ := 181581/500000) 266 46
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t3 : ((-2757604011393/5000000000000 : ℚ) : ℝ) ≤ stT266 3 := by
  have hc : ((-477631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2757604011393/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-477631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c4 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-169677/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1158399/2000000) (δ := 533/40000000) (ψ := 181581/500000) 266 59
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t4 : ((-1696895339379/5000000000000 : ℚ) : ℝ) ≤ stT266 4 := by
  have hc : ((-339379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1696895339379/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-339379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c5 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((220497/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 122683/1000000) (δ := 1349/100000000) (ψ := 181581/500000) 266 68
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t5 : ((394414579763/1000000000000 : ℚ) : ℝ) ≤ stT266 5 := by
  have hc : ((440969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((394414579763/1000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((440969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c6 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((144683/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3193079/10000000) (δ := 13347/1000000000) (ψ := 181581/500000) 266 76
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t6 : ((147640920289/1250000000000 : ℚ) : ℝ) ≤ stT266 6 := by
  have hc : ((72329/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147640920289/1250000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((72329/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c7 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-44121/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5069357/10000000) (δ := 1339/100000000) (ψ := 181581/500000) 266 82
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t7 : ((-16678061527/100000000000 : ℚ) : ℝ) ≤ stT266 7 := by
  have hc : ((-22063/50000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16678061527/100000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-22063/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c8 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((247117/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -190021/5000000) (δ := 1337/100000000) (ψ := 181581/500000) 266 88
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t8 : ((1747292228397/5000000000000 : ℚ) : ℝ) ≤ stT266 8 := by
  have hc : ((494209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1747292228397/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((494209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c9 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((97189/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -594163/10000000) (δ := 13369/1000000000) (ψ := 181581/500000) 266 93
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t9 : ((10123332321/31250000000 : ℚ) : ℝ) ≤ stT266 9 := by
  have hc : ((3037/3125 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10123332321/31250000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((3037/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c10 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-884159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1659679/2500000) (δ := 2681/200000000) (ψ := 181581/500000) 266 97
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t10 : ((-1398057334051/5000000000000 : ℚ) : ℝ) ≤ stT266 10 := by
  have hc : ((-884209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1398057334051/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-884209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c11 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-482371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3594073/5000000) (δ := 209/15625000) (ψ := 181581/500000) 266 101
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t11 : ((-181809866643/625000000000 : ℚ) : ℝ) ≤ stT266 11 := by
  have hc : ((-120599/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181809866643/625000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-120599/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c12 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((315657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1109437/5000000) (δ := 3337/250000000) (ψ := 181581/500000) 266 105
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t12 : ((56946936977/312500000000 : ℚ) : ℝ) ≤ stT266 12 := by
  have hc : ((19727/31250 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56946936977/312500000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((19727/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c13 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-39297/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7384583/10000000) (δ := 3371/250000000) (ψ := 181581/500000) 266 109
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t13 : ((-108995815799/400000000000 : ℚ) : ℝ) ≤ stT266 13 := by
  have hc : ((-39299/40000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108995815799/400000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-39299/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c14 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-496763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5226653/10000000) (δ := 6703/500000000) (ψ := 181581/500000) 266 112
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t14 : ((-1327788882369/10000000000000 : ℚ) : ℝ) ≤ stT266 14 := by
  have hc : ((-496813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1327788882369/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-496813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c15 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-850697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1294053/2000000) (δ := 3369/250000000) (ψ := 181581/500000) 266 115
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t15 : ((-2196619395783/10000000000000 : ℚ) : ℝ) ≤ stT266 15 := by
  have hc : ((-850747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2196619395783/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-850747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c16 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-427719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5031911/10000000) (δ := 13461/1000000000) (ψ := 181581/500000) 266 117
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t16 : ((-1069422927769/10000000000000 : ℚ) : ℝ) ≤ stT266 16 := by
  have hc : ((-427769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1069422927769/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-427769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c17 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((37897/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1776619/10000000) (δ := 13463/1000000000) (ψ := 181581/500000) 266 120
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t17 : ((45953826471/250000000000 : ℚ) : ℝ) ≤ stT266 17 := by
  have hc : ((75789/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45953826471/250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((75789/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c18 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-348827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 481779/1000000) (δ := 6663/500000000) (ψ := 181581/500000) 266 122
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t18 : ((-822311113171/10000000000000 : ℚ) : ℝ) ≤ stT266 18 := by
  have hc : ((-348877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-822311113171/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-348877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c19 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-164951/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1587853/2500000) (δ := 3351/250000000) (ψ := 181581/500000) 266 125
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t19 : ((-189223298919/1000000000000 : ℚ) : ℝ) ≤ stT266 19 := by
  have hc : ((-164961/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-189223298919/1000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-164961/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c20 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((10767/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1828647/5000000) (δ := 1339/100000000) (ψ := 181581/500000) 266 127
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t20 : ((12032276527/500000000000 : ℚ) : ℝ) ≤ stT266 20 := by
  have hc : ((5381/50000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12032276527/500000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((5381/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c21 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((496621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2627737/10000000) (δ := 3357/250000000) (ψ := 181581/500000) 266 129
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t21 : ((541803155819/5000000000000 : ℚ) : ℝ) ≤ stT266 21 := by
  have hc : ((496571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((541803155819/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((496571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c22 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((16091/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -388483/1250000) (δ := 13361/1000000000) (ψ := 181581/500000) 266 131
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t22 : ((68601589239/1000000000000 : ℚ) : ℝ) ≤ stT266 22 := by
  have hc : ((32177/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68601589239/1000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((32177/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c23 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-40277/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4963343/10000000) (δ := 841/62500000) (ψ := 181581/500000) 266 133
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t23 : ((-8399381089/100000000000 : ℚ) : ℝ) ≤ stT266 23 := by
  have hc : ((-20141/50000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8399381089/100000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-20141/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c24 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-996019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7630827/10000000) (δ := 13439/1000000000) (ψ := 181581/500000) 266 134
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t24 : ((-1016608938849/5000000000000 : ℚ) : ℝ) ≤ stT266 24 := by
  have hc : ((-996069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1016608938849/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-996069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c25 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((11213/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3361531/10000000) (δ := 6689/500000000) (ψ := 181581/500000) 266 136
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t25 : ((22421/500000 : ℚ) : ℝ) ≤ stT266 25 := by
  have hc : ((22421/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22421/500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((22421/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c26 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((352259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -197263/1000000) (δ := 837/62500000) (ψ := 181581/500000) 266 138
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t26 : ((345393791837/2500000000000 : ℚ) : ℝ) ≤ stT266 26 := by
  have hc : ((176117/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((345393791837/2500000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((176117/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c27 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-492371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3708353/5000000) (δ := 1663/125000000) (ψ := 181581/500000) 266 139
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t27 : ((-236904148599/1250000000000 : ℚ) : ℝ) ≤ stT266 27 := by
  have hc : ((-123099/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236904148599/1250000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-123099/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c28 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((498627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1853/100000) (δ := 6657/500000000) (ψ := 181581/500000) 266 141
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t28 : ((235567257211/1250000000000 : ℚ) : ℝ) ≤ stT266 28 := by
  have hc : ((249301/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235567257211/1250000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((249301/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c29 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-499933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7813051/10000000) (δ := 6691/500000000) (ψ := 181581/500000) 266 142
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t29 : ((-232099751983/1250000000000 : ℚ) : ℝ) ≤ stT266 29 := by
  have hc : ((-249979/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232099751983/1250000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-249979/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c30 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((911717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -529189/5000000) (δ := 1671/125000000) (ψ := 181581/500000) 266 144
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t30 : ((1664467820247/10000000000000 : ℚ) : ℝ) ≤ stT266 30 := by
  have hc : ((911667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1664467820247/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((911667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c31 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-21513/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2519471/5000000) (δ := 673/50000000) (ψ := 181581/500000) 266 145
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t31 : ((-38642999837/500000000000 : ℚ) : ℝ) ≤ stT266 31 := by
  have hc : ((-43031/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38642999837/500000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-43031/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c32 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-254853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5264099/10000000) (δ := 6723/500000000) (ψ := 181581/500000) 266 147
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t32 : ((-225282458713/2500000000000 : ℚ) : ℝ) ≤ stT266 32 := by
  have hc : ((-127439/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225282458713/2500000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-127439/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c33 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((979349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -127237/2500000) (δ := 13339/1000000000) (ψ := 181581/500000) 266 148
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t33 : ((213092524503/1250000000000 : ℚ) : ℝ) ≤ stT266 33 := by
  have hc : ((979299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213092524503/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((979299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c34 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((58199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1817667/5000000) (δ := 13371/1000000000) (ψ := 181581/500000) 266 149
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t34 : ((9976753739/500000000000 : ℚ) : ℝ) ≤ stT266 34 := by
  have hc : ((29087/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9976753739/500000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((29087/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c35 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-483199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3602029/5000000) (δ := 533/40000000) (ψ := 181581/500000) 266 150
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t35 : ((-102099734527/625000000000 : ℚ) : ℝ) ≤ stT266 35 := by
  have hc : ((-60403/62500 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102099734527/625000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-60403/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c36 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-116287/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -273911/500000) (δ := 1331/100000000) (ψ := 181581/500000) 266 152
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t36 : ((-193828372099/2000000000000 : ℚ) : ℝ) ≤ stT266 36 := by
  have hc : ((-116297/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193828372099/2000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-116297/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c37 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((23441/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -370731/1250000) (δ := 67/5000000) (ψ := 181581/500000) 266 153
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t37 : ((308252869467/5000000000000 : ℚ) : ℝ) ≤ stT266 37 := by
  have hc : ((187503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((308252869467/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((187503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c38 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((46511/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -939459/10000000) (δ := 1687/125000000) (ψ := 181581/500000) 266 154
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t38 : ((75446739819/500000000000 : ℚ) : ℝ) ≤ stT266 38 := by
  have hc : ((93017/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75446739819/500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((93017/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c39 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((193757/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 313143/5000000) (δ := 6707/500000000) (ψ := 181581/500000) 266 155
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t39 : ((310243389907/2000000000000 : ℚ) : ℝ) ≤ stT266 39 := by
  have hc : ((193747/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((310243389907/2000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((193747/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c40 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((19091/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1754659/10000000) (δ := 13481/1000000000) (ψ := 181581/500000) 266 156
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t40 : ((60367058271/500000000000 : ℚ) : ℝ) ≤ stT266 40 := by
  have hc : ((76359/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60367058271/500000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((76359/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c41 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((551271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 98691/400000) (δ := 6687/500000000) (ψ := 181581/500000) 266 157
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t41 : ((860862230877/10000000000000 : ℚ) : ℝ) ≤ stT266 41 := by
  have hc : ((551221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((860862230877/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((551221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c42 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((441357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 348027/1250000) (δ := 1667/125000000) (ψ := 181581/500000) 266 158
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t42 : ((680951264131/10000000000000 : ℚ) : ℝ) ≤ stT266 42 := by
  have hc : ((441307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((680951264131/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((441307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c43 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((115707/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 544807/2000000) (δ := 167/12500000) (ψ := 181581/500000) 266 159
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t43 : ((70572950833/1000000000000 : ℚ) : ℝ) ≤ stT266 43 := by
  have hc : ((231389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70572950833/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((231389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c44 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((302259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2304089/10000000) (δ := 13453/1000000000) (ψ := 181581/500000) 266 160
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t44 : ((56954335013/625000000000 : ℚ) : ℝ) ≤ stT266 44 := by
  have hc : ((151117/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56954335013/625000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((151117/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c45 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((102009/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 770269/5000000) (δ := 6673/500000000) (ψ := 181581/500000) 266 161
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t45 : ((608226485821/5000000000000 : ℚ) : ℝ) ≤ stT266 45 := by
  have hc : ((408011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((608226485821/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((408011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c46 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((245987/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 448543/10000000) (δ := 6719/500000000) (ψ := 181581/500000) 266 162
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t46 : ((725338952631/5000000000000 : ℚ) : ℝ) ≤ stT266 46 := by
  have hc : ((491949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((725338952631/5000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((491949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c47 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((927513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -95773/1000000) (δ := 421/31250000) (ψ := 181581/500000) 266 163
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t47 : ((1352842977487/10000000000000 : ℚ) : ℝ) ≤ stT266 47 := by
  have hc : ((927463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1352842977487/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((927463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c48 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((96713/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2665183/10000000) (δ := 839/62500000) (ψ := 181581/500000) 266 164
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t48 : ((1116629541/16000000000 : ℚ) : ℝ) ≤ stT266 48 := by
  have hc : ((96703/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1116629541/16000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((96703/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c49 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-72387/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2330689/5000000) (δ := 13317/1000000000) (ψ := 181581/500000) 266 165
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t49 : ((-51713949257/1250000000000 : ℚ) : ℝ) ≤ stT266 49 := by
  have hc : ((-144799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51713949257/1250000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-144799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c50 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-2916/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6934479/10000000) (δ := 13393/1000000000) (ψ := 181581/500000) 266 166
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t50 : ((-65985103919/500000000000 : ℚ) : ℝ) ≤ stT266 50 := by
  have hc : ((-93317/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65985103919/500000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-93317/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c51 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-797357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24937/40000) (δ := 13393/1000000000) (ψ := 181581/500000) 266 166
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t51 : ((-1116593871367/10000000000000 : ℚ) : ℝ) ≤ stT266 51 := by
  have hc : ((-797407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1116593871367/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-797407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c52 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((24229/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3439323/10000000) (δ := 13303/1000000000) (ψ := 181581/500000) 266 167
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t52 : ((537454377/20000000000 : ℚ) : ℝ) ≤ stT266 52 := by
  have hc : ((96891/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((537454377/20000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((96891/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c53 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((15427/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 398413/10000000) (δ := 419/31250000) (ψ := 181581/500000) 266 168
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t53 : ((135612999719/1000000000000 : ℚ) : ℝ) ≤ stT266 53 := by
  have hc : ((493639/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135612999719/1000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((493639/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c54 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((81383/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -359913/1250000) (δ := 2663/200000000) (ψ := 181581/500000) 266 169
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t54 : ((110734575471/2000000000000 : ℚ) : ℝ) ≤ stT266 54 := by
  have hc : ((81373/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110734575471/2000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((81373/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c55 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-832303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1596279/2500000) (δ := 13381/1000000000) (ψ := 181581/500000) 266 170
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t55 : ((-2805861963/25000000000 : ℚ) : ℝ) ≤ stT266 55 := by
  have hc : ((-832353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2805861963/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-832353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c56 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-619479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5597187/10000000) (δ := 6711/500000000) (ψ := 181581/500000) 266 170
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t56 : ((-827880939403/10000000000000 : ℚ) : ℝ) ≤ stT266 56 := by
  have hc : ((-619529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-827880939403/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-619529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c57 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((787667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1659457/10000000) (δ := 6737/500000000) (ψ := 181581/500000) 266 171
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t57 : ((260805980061/2500000000000 : ℚ) : ℝ) ≤ stT266 57 := by
  have hc : ((787617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260805980061/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((787617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c58 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((273013/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2482959/10000000) (δ := 13367/1000000000) (ψ := 181581/500000) 266 172
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t58 : ((11201584851/156250000000 : ℚ) : ℝ) ≤ stT266 58 := by
  have hc : ((68247/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11201584851/156250000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((68247/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c59 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-229047/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3411573/5000000) (δ := 417/31250000) (ψ := 181581/500000) 266 173
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t59 : ((-59642054491/500000000000 : ℚ) : ℝ) ≤ stT266 59 := by
  have hc : ((-458119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59642054491/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-458119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c60 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-169807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 174143/400000) (δ := 13459/1000000000) (ψ := 181581/500000) 266 173
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t60 : ((-43856907543/2000000000000 : ℚ) : ℝ) ≤ stT266 60 := by
  have hc : ((-169857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43856907543/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-169857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c61 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((123689/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -362403/10000000) (δ := 13451/1000000000) (ψ := 181581/500000) 266 174
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t61 : ((39589858813/312500000000 : ℚ) : ℝ) ≤ stT266 61 := by
  have hc : ((494731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39589858813/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((494731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c62 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-507307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2628567/5000000) (δ := 6679/500000000) (ψ := 181581/500000) 266 175
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t62 : ((-322172202357/5000000000000 : ℚ) : ℝ) ≤ stT266 62 := by
  have hc : ((-507357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-322172202357/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-507357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c63 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-550077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1345783/2500000) (δ := 6679/500000000) (ψ := 181581/500000) 266 175
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t63 : ((-346547552507/5000000000000 : ℚ) : ℝ) ≤ stT266 63 := by
  have hc : ((-550127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-346547552507/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-550127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c64 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((998253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 36947/2500000) (δ := 6669/500000000) (ψ := 181581/500000) 266 176
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t64 : ((998203/8000000 : ℚ) : ℝ) ≤ stT266 64 := by
  have hc : ((998203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((998203/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((998203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c65 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-100961/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2624941/5000000) (δ := 3343/250000000) (ψ := 181581/500000) 266 177
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t65 : ((-31309794477/500000000000 : ℚ) : ℝ) ≤ stT266 65 := by
  have hc : ((-100971/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31309794477/500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-100971/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c66 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-95141/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 980601/2000000) (δ := 13431/1000000000) (ψ := 181581/500000) 266 177
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t66 : ((-46850348181/1000000000000 : ℚ) : ℝ) ≤ stT266 66 := by
  have hc : ((-190307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46850348181/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-190307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c67 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((237159/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -402377/5000000) (δ := 13479/1000000000) (ψ := 181581/500000) 266 178
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t67 : ((289720456171/2500000000000 : ℚ) : ℝ) ≤ stT266 67 := by
  have hc : ((474293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((289720456171/2500000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((474293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c68 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-222057/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1665169/2500000) (δ := 13387/1000000000) (ψ := 181581/500000) 266 179
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t68 : ((-538598038381/5000000000000 : ℚ) : ℝ) ≤ stT266 68 := by
  have hc : ((-444139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-538598038381/5000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-444139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c69 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((13783/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1523763/5000000) (δ := 13387/1000000000) (ψ := 181581/500000) 266 179
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t69 : ((8295183549/200000000000 : ℚ) : ℝ) ≤ stT266 69 := by
  have hc : ((13781/40000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8295183549/200000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((13781/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c70 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((327839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -193247/625000) (δ := 13309/1000000000) (ψ := 181581/500000) 266 180
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t70 : ((97945647723/2500000000000 : ℚ) : ℝ) ≤ stT266 70 := by
  have hc : ((327789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97945647723/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((327789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c71 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-822349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6340807/10000000) (δ := 13309/1000000000) (ψ := 181581/500000) 266 180
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t71 : ((-488004165009/5000000000000 : ℚ) : ℝ) ≤ stT266 71 := by
  have hc : ((-822399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-488004165009/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-822399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c72 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((999649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -66267/10000000) (δ := 6701/500000000) (ψ := 181581/500000) 266 181
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t72 : ((1178038417089/10000000000000 : ℚ) : ℝ) ≤ stT266 72 := by
  have hc : ((999599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1178038417089/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((999599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c73 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-438571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3300843/5000000) (δ := 2699/200000000) (ψ := 181581/500000) 266 182
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t73 : ((-32083626347/312500000000 : ℚ) : ℝ) ≤ stT266 73 := by
  have hc : ((-109649/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32083626347/312500000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-109649/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c74 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((279169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1223019/5000000) (δ := 2699/200000000) (ψ := 181581/500000) 266 182
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t74 : ((10140568767/156250000000 : ℚ) : ℝ) ≤ stT266 74 := by
  have hc : ((34893/62500 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10140568767/156250000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((34893/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c75 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-81351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4335563/10000000) (δ := 2683/200000000) (ψ := 181581/500000) 266 183
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t75 : ((-2936404643/156250000000 : ℚ) : ℝ) ≤ stT266 75 := by
  have hc : ((-2543/15625 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2936404643/156250000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-2543/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c76 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-108237/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 894499/2000000) (δ := 2683/200000000) (ψ := 181581/500000) 266 183
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t76 : ((-62092533349/2500000000000 : ℚ) : ℝ) ≤ stT266 76 := by
  have hc : ((-54131/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62092533349/2500000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-54131/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c77 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((65739/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1271261/5000000) (δ := 13323/1000000000) (ψ := 181581/500000) 266 184
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t77 : ((59927496451/1000000000000 : ℚ) : ℝ) ≤ stT266 77 := by
  have hc : ((262931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59927496451/1000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((262931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c78 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-747639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6038239/10000000) (δ := 13323/1000000000) (ψ := 181581/500000) 266 184
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t78 : ((-423295902771/5000000000000 : ℚ) : ℝ) ≤ stT266 78 := by
  have hc : ((-747689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-423295902771/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-747689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c79 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((887311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1198289/10000000) (δ := 1343/100000000) (ψ := 181581/500000) 266 185
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t79 : ((998245816707/10000000000000 : ℚ) : ℝ) ≤ stT266 79 := by
  have hc : ((887261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((998245816707/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((887261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c80 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-962439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7166613/10000000) (δ := 1343/100000000) (ψ := 181581/500000) 266 185
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t80 : ((-538047713313/5000000000000 : ℚ) : ℝ) ≤ stT266 80 := by
  have hc : ((-962489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-538047713313/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-962489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c81 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((993717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -70097/2500000) (δ := 13337/1000000000) (ψ := 181581/500000) 266 186
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t81 : ((1104074334037/10000000000000 : ℚ) : ℝ) ≤ stT266 81 := by
  have hc : ((993667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1104074334037/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((993667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c82 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-999949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1565747/2000000) (δ := 13359/1000000000) (ψ := 181581/500000) 266 187
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t82 : ((-276078723921/2500000000000 : ℚ) : ℝ) ≤ stT266 82 := by
  have hc : ((-999999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-276078723921/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-999999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c83 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((995697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57999/2500000) (δ := 13359/1000000000) (ψ := 181581/500000) 266 187
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t83 : ((546431982187/5000000000000 : ℚ) : ℝ) ≤ stT266 83 := by
  have hc : ((995647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((546431982187/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((995647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c84 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-990649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7511827/10000000) (δ := 26751/1000000000) (ψ := 181581/500000) 266 188
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t84 : ((-108094177191/1000000000000 : ℚ) : ℝ) ≤ stT266 84 := by
  have hc : ((-990699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108094177191/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-990699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c85 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((3093/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 179041/5000000) (δ := 13351/1000000000) (ψ := 181581/500000) 266 188
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t85 : ((26837273273/250000000000 : ℚ) : ℝ) ≤ stT266 85 := by
  have hc : ((98971/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26837273273/250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((98971/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c86 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-993647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7572041/10000000) (δ := 6729/500000000) (ψ := 181581/500000) 266 189
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t86 : ((-133941412327/1250000000000 : ℚ) : ℝ) ≤ stT266 86 := by
  have hc : ((-993697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133941412327/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-993697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c87 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((39957/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 115957/10000000) (δ := 2669/200000000) (ψ := 181581/500000) 266 189
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t87 : ((535452937/5000000000 : ℚ) : ℝ) ≤ stT266 87 := by
  have hc : ((7991/8000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((535452937/5000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((7991/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c88 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-499239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7716043/10000000) (δ := 6729/500000000) (ψ := 181581/500000) 266 189
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t88 : ((-2078974301/19531250000 : ℚ) : ℝ) ≤ stT266 88 := by
  have hc : ((-15602/15625 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2078974301/19531250000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-15602/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c89 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((245449/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -477753/10000000) (δ := 6683/500000000) (ψ := 181581/500000) 266 190
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t89 : ((520323907381/5000000000000 : ℚ) : ℝ) ≤ stT266 89 := by
  have hc : ((490873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((520323907381/5000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((490873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c90 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-935687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6952491/10000000) (δ := 13437/1000000000) (ψ := 181581/500000) 266 190
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t90 : ((-986353821541/10000000000000 : ℚ) : ℝ) ≤ stT266 90 := by
  have hc : ((-935737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-986353821541/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-935737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c91 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((13214/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -703661/5000000) (δ := 2673/100000000) (ψ := 181581/500000) 266 191
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t91 : ((110809646433/1250000000000 : ℚ) : ℝ) ≤ stT266 91 := by
  have hc : ((422823/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110809646433/1250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((422823/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c92 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-349287/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5860497/10000000) (δ := 13473/1000000000) (ψ := 181581/500000) 266 191
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t92 : ((-2845181717/39062500000 : ℚ) : ℝ) ≤ stT266 92 := by
  have hc : ((-10916/15625 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2845181717/39062500000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-10916/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c93 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((243001/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1329109/5000000) (δ := 669/50000000) (ψ := 181581/500000) 266 192
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t93 : ((7873568943/156250000000 : ℚ) : ℝ) ≤ stT266 93 := by
  have hc : ((7593/15625 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7873568943/156250000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((7593/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c94 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-209307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1113539/2500000) (δ := 13423/1000000000) (ψ := 181581/500000) 266 192
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t94 : ((-107967707827/5000000000000 : ℚ) : ℝ) ≤ stT266 94 := by
  have hc : ((-209357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107967707827/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-209357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c95 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-28907/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -421671/1000000) (δ := 13487/1000000000) (ψ := 181581/500000) 266 193
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t95 : ((-59341599381/5000000000000 : ℚ) : ℝ) ≤ stT266 95 := by
  have hc : ((-57839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59341599381/5000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-57839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c96 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((454771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 171669/625000) (δ := 3329/250000000) (ψ := 181581/500000) 266 193
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t96 : ((23204867351/500000000000 : ℚ) : ℝ) ≤ stT266 96 := by
  have hc : ((454721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23204867351/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((454721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c97 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-378007/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6069997/10000000) (δ := 6697/500000000) (ψ := 181581/500000) 266 194
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t97 : ((-23989603569/312500000000 : ℚ) : ℝ) ≤ stT266 97 := by
  have hc : ((-23627/31250 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23989603569/312500000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-23627/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c98 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((238817/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30023/400000) (δ := 13409/1000000000) (ψ := 181581/500000) 266 194
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t98 : ((60307210821/625000000000 : ℚ) : ℝ) ≤ stT266 98 := by
  have hc : ((477609/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60307210821/625000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((477609/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c99 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-990101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7501921/10000000) (δ := 13409/1000000000) (ψ := 181581/500000) 266 194
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t99 : ((-497569690369/5000000000000 : ℚ) : ℝ) ≤ stT266 99 := by
  have hc : ((-990151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-497569690369/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-990151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c100 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((820199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1522593/10000000) (δ := 13501/1000000000) (ψ := 181581/500000) 266 195
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t100 : ((820148179851/10000000000000 : ℚ) : ℝ) ≤ stT266 100 := by
  have hc : ((820149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((820148179851/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((820149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c101 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-90037/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5094423/10000000) (δ := 13501/1000000000) (ψ := 181581/500000) 266 195
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t101 : ((-44800093393/1000000000000 : ℚ) : ℝ) ≤ stT266 101 := by
  have hc : ((-90047/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44800093393/1000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-90047/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c102 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-26941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12693/31250) (δ := 13409/1000000000) (ψ := 181581/500000) 266 196
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t102 : ((-3337541371/625000000000 : ℚ) : ℝ) ≤ stT266 102 := by
  have hc : ((-13483/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3337541371/625000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-13483/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c103 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((282477/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1213023/5000000) (δ := 6697/500000000) (ψ := 181581/500000) 266 196
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t103 : ((69577036677/1250000000000 : ℚ) : ℝ) ≤ stT266 103 := by
  have hc : ((70613/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69577036677/1250000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((70613/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c104 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-230373/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3428377/5000000) (δ := 13487/1000000000) (ψ := 181581/500000) 266 197
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t104 : ((-451823287951/5000000000000 : ℚ) : ℝ) ≤ stT266 104 := by
  have hc : ((-460771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-451823287951/5000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-460771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c105 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((122577/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -123259/2500000) (δ := 3329/250000000) (ψ := 181581/500000) 266 197
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t105 : ((4784671797/50000000000 : ℚ) : ℝ) ≤ stT266 105 := by
  have hc : ((490283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4784671797/50000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((490283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c106 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-684067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5810299/10000000) (δ := 13487/1000000000) (ψ := 181581/500000) 266 197
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t106 : ((-332236632231/5000000000000 : ℚ) : ℝ) ≤ stT266 106 := by
  have hc : ((-684117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-332236632231/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-684117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c107 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((109199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3653447/10000000) (δ := 669/50000000) (ψ := 181581/500000) 266 198
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t107 : ((6594891729/625000000000 : ℚ) : ℝ) ≤ stT266 107 := by
  have hc : ((109149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6594891729/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((109149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c108 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((529267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2532649/10000000) (δ := 669/50000000) (ψ := 181581/500000) 266 198
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t108 : ((2036956233/40000000000 : ℚ) : ℝ) ≤ stT266 108 := by
  have hc : ((529217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2036956233/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((529217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c109 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-948261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -281851/400000) (δ := 1333/100000000) (ψ := 181581/500000) 266 199
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t109 : ((-908317880197/10000000000000 : ℚ) : ℝ) ≤ stT266 109 := by
  have hc : ((-948311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-908317880197/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-948311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c110 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((231297/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -973163/10000000) (δ := 13473/1000000000) (ψ := 181581/500000) 266 199
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t110 : ((220520981939/2500000000000 : ℚ) : ℝ) ≤ stT266 110 := by
  have hc : ((462569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220520981939/2500000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((462569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c111 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-432453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5045021/10000000) (δ := 1333/100000000) (ψ := 181581/500000) 266 199
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t111 : ((-205256841237/5000000000000 : ℚ) : ℝ) ≤ stT266 111 := by
  have hc : ((-432503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205256841237/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-432503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c112 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-75963/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4698823/10000000) (δ := 13437/1000000000) (ψ := 181581/500000) 266 200
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t112 : ((-8973770207/312500000000 : ℚ) : ℝ) ≤ stT266 112 := by
  have hc : ((-151951/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8973770207/312500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-151951/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c113 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((884701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 606181/5000000) (δ := 13437/1000000000) (ψ := 181581/500000) 266 200
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t113 : ((10402611109/125000000000 : ℚ) : ℝ) ≤ stT266 113 := by
  have hc : ((884651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10402611109/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((884651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c114 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-190281/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7071411/10000000) (δ := 13437/1000000000) (ψ := 181581/500000) 266 200
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t114 : ((-89111943263/1000000000000 : ℚ) : ℝ) ≤ stT266 114 := by
  have hc : ((-190291/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89111943263/1000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-190291/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c115 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((212671/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1414321/5000000) (δ := 2669/200000000) (ψ := 181581/500000) 266 201
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t115 : ((12393327849/312500000000 : ℚ) : ℝ) ≤ stT266 115 := by
  have hc : ((106323/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12393327849/312500000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((106323/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c116 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((77741/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 91529/312500) (δ := 2669/200000000) (ψ := 181581/500000) 266 201
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t116 : ((18042841989/500000000000 : ℚ) : ℝ) ≤ stT266 116 := by
  have hc : ((77731/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18042841989/500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((77731/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c117 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-951331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -883851/1250000) (δ := 3363/250000000) (ψ := 181581/500000) 266 202
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t117 : ((-879552685881/10000000000000 : ℚ) : ℝ) ≤ stT266 117 := by
  have hc : ((-951381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-879552685881/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-951381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c118 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((211217/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1411193/10000000) (δ := 13351/1000000000) (ψ := 181581/500000) 266 202
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t118 : ((194429371383/2500000000000 : ℚ) : ℝ) ≤ stT266 118 := by
  have hc : ((422409/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194429371383/2500000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((422409/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c119 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-109229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4200609/10000000) (δ := 13351/1000000000) (ψ := 181581/500000) 266 202
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t119 : ((-100175950021/10000000000000 : ℚ) : ℝ) ≤ stT266 119 := by
  have hc : ((-109279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100175950021/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-109279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c120 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-360823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1188487/2000000) (δ := 3361/250000000) (ψ := 181581/500000) 266 203
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t120 : ((-20587979663/312500000000 : ℚ) : ℝ) ≤ stT266 120 := by
  have hc : ((-22553/31250 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20587979663/312500000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-22553/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c121 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((98567/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -423733/10000000) (δ := 3361/250000000) (ψ := 181581/500000) 266 203
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t121 : ((4480086429/50000000000 : ℚ) : ℝ) ≤ stT266 121 := by
  have hc : ((49281/50000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4480086429/50000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((49281/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c122 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-217043/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 100991/200000) (δ := 13359/1000000000) (ψ := 181581/500000) 266 203
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t122 : ((-24565531293/625000000000 : ℚ) : ℝ) ≤ stT266 122 := by
  have hc : ((-54267/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24565531293/625000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-54267/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c123 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-248931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5229819/10000000) (δ := 13337/1000000000) (ψ := 181581/500000) 266 204
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t123 : ((-5611903913/125000000000 : ℚ) : ℝ) ≤ stT266 123 := by
  have hc : ((-62239/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5611903913/125000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-62239/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c124 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((998083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 154819/10000000) (δ := 13337/1000000000) (ψ := 181581/500000) 266 204
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t124 : ((448129791429/5000000000000 : ℚ) : ℝ) ≤ stT266 124 := by
  have hc : ((998033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((448129791429/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((998033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c125 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-293641/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 687029/1250000) (δ := 13337/1000000000) (ψ := 181581/500000) 266 204
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t125 : ((-32832886631/625000000000 : ℚ) : ℝ) ≤ stT266 125 := by
  have hc : ((-146833/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32832886631/625000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-146833/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c126 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-384213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2456439/5000000) (δ := 13373/1000000000) (ψ := 181581/500000) 266 205
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t126 : ((-342328763073/10000000000000 : ℚ) : ℝ) ≤ stT266 126 := by
  have hc : ((-384263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-342328763073/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-384263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c127 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((990547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 344013/10000000) (δ := 1343/100000000) (ψ := 181581/500000) 266 205
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t127 : ((219730863983/2500000000000 : ℚ) : ℝ) ≤ stT266 127 := by
  have hc : ((990497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219730863983/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((990497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c128 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-607651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5559741/10000000) (δ := 1343/100000000) (ψ := 181581/500000) 266 205
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t128 : ((-134284297671/2500000000000 : ℚ) : ℝ) ≤ stT266 128 := by
  have hc : ((-607701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134284297671/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-607701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c129 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-101581/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4973059/10000000) (δ := 13323/1000000000) (ψ := 181581/500000) 266 206
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t129 : ((-178896197337/5000000000000 : ℚ) : ℝ) ≤ stT266 129 := by
  have hc : ((-203187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178896197337/5000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-203187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c130 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((997899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 162071/10000000) (δ := 13323/1000000000) (ψ := 181581/500000) 266 206
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t130 : ((437585724121/5000000000000 : ℚ) : ℝ) ≤ stT266 130 := by
  have hc : ((997849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((437585724121/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((997849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c131 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-507571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 52579/100000) (δ := 337/25000000) (ψ := 181581/500000) 266 206
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t131 : ((-88702201161/2000000000000 : ℚ) : ℝ) ≤ stT266 131 := by
  have hc : ((-507621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88702201161/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-507621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c132 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-553371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1078601/2000000) (δ := 2683/200000000) (ψ := 181581/500000) 266 207
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t132 : ((-481691550769/10000000000000 : ℚ) : ℝ) ≤ stT266 132 := by
  have hc : ((-553421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-481691550769/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-553421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c133 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((123603/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -374117/10000000) (δ := 2683/200000000) (ψ := 181581/500000) 266 207
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t133 : ((428687417183/5000000000000 : ℚ) : ℝ) ≤ stT266 133 := by
  have hc : ((494387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((428687417183/5000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((494387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c134 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-134363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2303583/5000000) (δ := 6697/250000000) (ψ := 181581/500000) 266 207
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t134 : ((-29023406793/1250000000000 : ℚ) : ℝ) ≤ stT266 134 := by
  have hc : ((-33597/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29023406793/1250000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-33597/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c135 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-38911/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1539139/2500000) (δ := 3327/250000000) (ψ := 181581/500000) 266 208
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t135 : ((-66982819301/1000000000000 : ℚ) : ℝ) ≤ stT266 135 := by
  have hc : ((-77827/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66982819301/1000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-77827/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c136 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((175563/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1248789/10000000) (δ := 2699/200000000) (ψ := 181581/500000) 266 208
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t136 : ((37633823269/500000000000 : ℚ) : ℝ) ≤ stT266 136 := by
  have hc : ((175553/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37633823269/500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((175553/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c137 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((12127/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3623067/10000000) (δ := 3327/250000000) (ψ := 181581/500000) 266 208
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t137 : ((5178257777/500000000000 : ℚ) : ℝ) ≤ stT266 137 := by
  have hc : ((6061/50000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5178257777/500000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((6061/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c138 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-970819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7248551/10000000) (δ := 13401/1000000000) (ψ := 181581/500000) 266 209
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t138 : ((-826459032333/10000000000000 : ℚ) : ℝ) ≤ stT266 138 := by
  have hc : ((-970869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-826459032333/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-970869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c139 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((279001/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2447051/10000000) (δ := 6701/500000000) (ψ := 181581/500000) 266 209
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t139 : ((924312873/19531250000 : ℚ) : ℝ) ≤ stT266 139 := by
  have hc : ((8718/15625 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((924312873/19531250000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((8718/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c140 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((149859/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2320001/10000000) (δ := 13401/1000000000) (ψ := 181581/500000) 266 209
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t140 : ((126643368861/2500000000000 : ℚ) : ℝ) ≤ stT266 140 := by
  have hc : ((299693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126643368861/2500000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((299693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c141 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-949121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 440817/625000) (δ := 13401/1000000000) (ψ := 181581/500000) 266 209
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t141 : ((-99918281999/1250000000000 : ℚ) : ℝ) ≤ stT266 141 := by
  have hc : ((-949171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99918281999/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-949171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c142 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-2257/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3955203/10000000) (δ := 13309/1000000000) (ψ := 181581/500000) 266 210
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t142 : ((-951212797/1000000000000 : ℚ) : ℝ) ≤ stT266 142 := by
  have hc : ((-2267/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-951212797/1000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-2267/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c143 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((479887/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 711501/10000000) (δ := 13309/1000000000) (ψ := 181581/500000) 266 210
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t143 : ((100320189651/1250000000000 : ℚ) : ℝ) ≤ stT266 143 := by
  have hc : ((239931/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100320189651/1250000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((239931/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c144 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-107497/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 267281/500000) (δ := 13309/1000000000) (ψ := 181581/500000) 266 210
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t144 : ((-44794619169/1000000000000 : ℚ) : ℝ) ≤ stT266 144 := by
  have hc : ((-107507/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44794619169/1000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-107507/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c145 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-167329/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5760211/10000000) (δ := 13387/1000000000) (ψ := 181581/500000) 266 211
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t145 : ((-55587834153/1000000000000 : ℚ) : ℝ) ≤ stT266 145 := by
  have hc : ((-334683/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55587834153/1000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-334683/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c146 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((222221/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -297433/2500000) (δ := 1677/125000000) (ψ := 181581/500000) 266 211
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t146 : ((73560346257/1000000000000 : ℚ) : ℝ) ≤ stT266 146 := by
  have hc : ((444417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73560346257/1000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((444417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c147 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((228951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3349491/10000000) (δ := 13387/1000000000) (ψ := 181581/500000) 266 211
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t147 : ((94397170093/5000000000000 : ℚ) : ℝ) ≤ stT266 147 := by
  have hc : ((228901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94397170093/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((228901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c148 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-999999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1962493/2500000) (δ := 13479/1000000000) (ψ := 181581/500000) 266 212
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t148 : ((-164407055551/2000000000000 : ℚ) : ℝ) ≤ stT266 148 := by
  have hc : ((-1000049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164407055551/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-1000049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c149 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((220257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -674359/2000000) (δ := 3331/250000000) (ψ := 181581/500000) 266 212
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t149 : ((180400400817/10000000000000 : ℚ) : ℝ) ≤ stT266 149 := by
  have hc : ((220207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180400400817/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((220207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c150 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((181749/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1076323/10000000) (δ := 13479/1000000000) (ψ := 181581/500000) 266 212
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t150 : ((9274322909/125000000000 : ℚ) : ℝ) ≤ stT266 150 := by
  have hc : ((181739/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9274322909/125000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((181739/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c151 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-586877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2747491/5000000) (δ := 13479/1000000000) (ψ := 181581/500000) 266 212
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t151 : ((-477634736403/10000000000000 : ℚ) : ℝ) ≤ stT266 151 := by
  have hc : ((-586927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-477634736403/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-586927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c152 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-687913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1164703/2000000) (δ := 13431/1000000000) (ψ := 181581/500000) 266 213
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t152 : ((-139503073251/2500000000000 : ℚ) : ℝ) ≤ stT266 152 := by
  have hc : ((-687963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139503073251/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-687963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c153 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((208409/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -365711/2500000) (δ := 13431/1000000000) (ψ := 181581/500000) 266 213
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t153 : ((84239283609/1250000000000 : ℚ) : ℝ) ≤ stT266 153 := by
  have hc : ((416793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84239283609/1250000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((416793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c154 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((10263/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2869431/10000000) (δ := 3343/250000000) (ψ := 181581/500000) 266 213
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t154 : ((16538287817/500000000000 : ℚ) : ℝ) ≤ stT266 154 := by
  have hc : ((41047/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16538287817/500000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((41047/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c155 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-963199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1793411/2500000) (δ := 13431/1000000000) (ψ := 181581/500000) 266 213
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t155 : ((-38685043089/500000000000 : ℚ) : ℝ) ≤ stT266 155 := by
  have hc : ((-963249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38685043089/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-963249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c156 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-65963/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4257771/10000000) (δ := 6669/500000000) (ψ := 181581/500000) 266 214
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t156 : ((-13208174577/1250000000000 : ℚ) : ℝ) ≤ stT266 156 := by
  have hc : ((-16497/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13208174577/1250000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-16497/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c157 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((499997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4277/5000000) (δ := 6669/500000000) (ψ := 181581/500000) 266 214
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t157 : ((49877581699/625000000000 : ℚ) : ℝ) ≤ stT266 157 := by
  have hc : ((124993/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49877581699/625000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((124993/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c158 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-57209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 131677/312500) (δ := 6669/500000000) (ψ := 181581/500000) 266 214
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t158 : ((-11383241643/1250000000000 : ℚ) : ℝ) ≤ stT266 158 := by
  have hc : ((-28617/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11383241643/1250000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-28617/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c159 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-975433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7298681/10000000) (δ := 2689/200000000) (ψ := 181581/500000) 266 215
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t159 : ((-193402186029/2500000000000 : ℚ) : ℝ) ≤ stT266 159 := by
  have hc : ((-975483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193402186029/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-975483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c160 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((313653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3129397/10000000) (δ := 2689/200000000) (ψ := 181581/500000) 266 215
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t160 : ((247924810107/10000000000000 : ℚ) : ℝ) ≤ stT266 160 := by
  have hc : ((313603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((247924810107/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((313603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c161 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((229721/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 202777/2000000) (δ := 6679/500000000) (ψ := 181581/500000) 266 215
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t161 : ((36207113187/500000000000 : ℚ) : ℝ) ≤ stT266 161 := by
  have hc : ((459417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36207113187/500000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((459417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c162 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-463401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1026313/2000000) (δ := 6679/500000000) (ψ := 181581/500000) 266 215
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t162 : ((-14564874577/400000000000 : ℚ) : ℝ) ≤ stT266 162 := by
  have hc : ((-463451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14564874577/400000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-463451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c163 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-853583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1296811/2000000) (δ := 13451/1000000000) (ψ := 181581/500000) 266 216
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t163 : ((-668617437213/10000000000000 : ℚ) : ℝ) ≤ stT266 163 := by
  have hc : ((-853633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-668617437213/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-853633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c164 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((71001/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1208391/5000000) (δ := 13451/1000000000) (ψ := 181581/500000) 266 216
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t164 : ((55437528443/1250000000000 : ℚ) : ℝ) ≤ stT266 164 := by
  have hc : ((283979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55437528443/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((283979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c165 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((795901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1625753/10000000) (δ := 13451/1000000000) (ψ := 181581/500000) 266 216
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t165 : ((309784205899/5000000000000 : ℚ) : ℝ) ≤ stT266 165 := by
  have hc : ((795851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((309784205899/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((795851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c166 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-634033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5643883/10000000) (δ := 1669/125000000) (ψ := 181581/500000) 266 216
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t166 : ((-492144154533/10000000000000 : ℚ) : ℝ) ≤ stT266 166 := by
  have hc : ((-634083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-492144154533/10000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-634083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c167 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-756021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -758753/1250000) (δ := 417/31250000) (ψ := 181581/500000) 266 217
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t167 : ((-9141654461/156250000000 : ℚ) : ℝ) ≤ stT266 167 := by
  have hc : ((-756071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9141654461/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-756071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c168 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((667491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2099907/10000000) (δ := 13459/1000000000) (ψ := 181581/500000) 266 217
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t168 : ((128735352639/2500000000000 : ℚ) : ℝ) ≤ stT266 168 := by
  have hc : ((667441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128735352639/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((667441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c169 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((739349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 369347/2000000) (δ := 13459/1000000000) (ψ := 181581/500000) 266 217
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t169 : ((56869096977/1000000000000 : ℚ) : ℝ) ≤ stT266 169 := by
  have hc : ((739299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56869096977/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((739299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c170 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-672231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1154007/2000000) (δ := 417/31250000) (ψ := 181581/500000) 266 217
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t170 : ((-103123199433/2000000000000 : ℚ) : ℝ) ≤ stT266 170 := by
  have hc : ((-672281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103123199433/2000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-672281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c171 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-747479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6037637/10000000) (δ := 3359/250000000) (ψ := 181581/500000) 266 218
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t171 : ((-7145629711/125000000000 : ℚ) : ℝ) ≤ stT266 171 := by
  have hc : ((-747529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7145629711/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-747529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c172 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((324687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -270011/1250000) (δ := 13367/1000000000) (ψ := 181581/500000) 266 218
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t172 : ((30944022213/625000000000 : ℚ) : ℝ) ≤ stT266 172 := by
  have hc : ((162331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30944022213/625000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((162331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c173 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((778833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1694983/10000000) (δ := 3359/250000000) (ψ := 181581/500000) 266 218
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t173 : ((118419406631/2000000000000 : ℚ) : ℝ) ≤ stT266 173 := by
  have hc : ((778783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118419406631/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((778783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c174 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-597469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1381961/2500000) (δ := 13367/1000000000) (ψ := 181581/500000) 266 218
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t174 : ((-452978556381/10000000000000 : ℚ) : ℝ) ≤ stT266 174 := by
  have hc : ((-597519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-452978556381/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-597519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c175 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-414379/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1592301/2500000) (δ := 13329/1000000000) (ψ := 181581/500000) 266 219
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t175 : ((-78315000329/1250000000000 : ℚ) : ℝ) ≤ stT266 175 := by
  have hc : ((-103601/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78315000329/1250000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-103601/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c176 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((128273/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1290017/5000000) (δ := 13329/1000000000) (ψ := 181581/500000) 266 219
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t176 : ((96679943169/2500000000000 : ℚ) : ℝ) ≤ stT266 176 := by
  have hc : ((256521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96679943169/2500000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((256521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c177 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((222313/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1187723/10000000) (δ := 13329/1000000000) (ψ := 181581/500000) 266 219
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t177 : ((167091281623/2500000000000 : ℚ) : ℝ) ≤ stT266 177 := by
  have hc : ((444601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167091281623/2500000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((444601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c178 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-392073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24671/50000) (δ := 13329/1000000000) (ψ := 181581/500000) 266 219
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t178 : ((-73477184109/2500000000000 : ℚ) : ℝ) ≤ stT266 178 := by
  have hc : ((-392123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73477184109/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-392123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c179 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-94851/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3524117/5000000) (δ := 6711/500000000) (ψ := 181581/500000) 266 220
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t179 : ((-2215587163/31250000000 : ℚ) : ℝ) ≤ stT266 179 := by
  have hc : ((-11857/12500 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2215587163/31250000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-11857/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c180 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((57819/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3343519/10000000) (δ := 6711/500000000) (ψ := 181581/500000) 266 220
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t180 : ((17234545523/1000000000000 : ℚ) : ℝ) ≤ stT266 180 := by
  have hc : ((115613/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17234545523/1000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((115613/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c181 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((990727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 170357/5000000) (δ := 6711/500000000) (ψ := 181581/500000) 266 220
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t181 : ((368182135019/5000000000000 : ℚ) : ℝ) ≤ stT266 181 := by
  have hc : ((990677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((368182135019/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((990677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c182 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-15519/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2002299/5000000) (δ := 6711/500000000) (ψ := 181581/500000) 266 220
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t182 : ((-1152199/500000000 : ℚ) : ℝ) ≤ stT266 182 := by
  have hc : ((-1943/62500 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1152199/500000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-1943/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c183 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-996623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3824233/5000000) (δ := 13381/1000000000) (ψ := 181581/500000) 266 220
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t183 : ((-368381304203/5000000000000 : ℚ) : ℝ) ≤ stT266 183 := by
  have hc : ((-996673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-368381304203/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-996673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c184 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-202009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4435513/10000000) (δ := 843/62500000) (ψ := 181581/500000) 266 221
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t184 : ((-14895991539/1000000000000 : ℚ) : ℝ) ≤ stT266 184 := by
  have hc : ((-202059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14895991539/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-202059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c185 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((945243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -831147/10000000) (δ := 2663/200000000) (ψ := 181581/500000) 266 221
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t185 : ((347459563151/5000000000000 : ℚ) : ℝ) ≤ stT266 185 := by
  have hc : ((945193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((347459563151/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((945193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c186 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((56533/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 550747/2000000) (δ := 2663/200000000) (ψ := 181581/500000) 266 221
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t186 : ((33157913229/1000000000000 : ℚ) : ℝ) ≤ stT266 186 := by
  have hc : ((226107/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33157913229/1000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((226107/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c187 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-817461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1263893/2000000) (δ := 2663/200000000) (ψ := 181581/500000) 266 221
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t187 : ((-597823721503/10000000000000 : ℚ) : ℝ) ≤ stT266 187 := by
  have hc : ((-817511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-597823721503/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-817511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c188 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-693219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2920927/5000000) (δ := 419/31250000) (ψ := 181581/500000) 266 222
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t188 : ((-20224736537/400000000000 : ℚ) : ℝ) ≤ stT266 188 := by
  have hc : ((-693269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20224736537/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-693269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c189 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((601367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1156981/5000000) (δ := 2679/200000000) (ψ := 181581/500000) 266 222
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t189 : ((13668536727/312500000000 : ℚ) : ℝ) ≤ stT266 189 := by
  have hc : ((601317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13668536727/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((601317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c190 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((13873/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1195243/10000000) (δ := 2679/200000000) (ψ := 181581/500000) 266 222
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t190 : ((80511694159/1250000000000 : ℚ) : ℝ) ≤ stT266 190 := by
  have hc : ((443911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80511694159/1250000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((443911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c191 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-298997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2343047/5000000) (δ := 2679/200000000) (ψ := 181581/500000) 266 222
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t191 : ((-8655317321/400000000000 : ℚ) : ℝ) ≤ stT266 191 := by
  have hc : ((-299047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8655317321/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-299047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c192 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-992583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3774653/5000000) (δ := 13303/1000000000) (ψ := 181581/500000) 266 223
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t192 : ((-89546415563/1250000000000 : ℚ) : ℝ) ≤ stT266 192 := by
  have hc : ((-992633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89546415563/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-992633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c193 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-67059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1023691/2500000) (δ := 13303/1000000000) (ψ := 181581/500000) 266 223
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t193 : ((-6038266493/1250000000000 : ℚ) : ℝ) ≤ stT266 193 := by
  have hc : ((-67109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6038266493/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-67109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c194 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((482779/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -164511/2500000) (δ := 13303/1000000000) (ψ := 181581/500000) 266 223
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t194 : ((86649274083/1250000000000 : ℚ) : ℝ) ≤ stT266 194 := by
  have hc : ((241377/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86649274083/1250000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((241377/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c195 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((17987/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2760987/10000000) (δ := 13303/1000000000) (ψ := 181581/500000) 266 223
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t195 : ((1287931029/40000000000 : ℚ) : ℝ) ≤ stT266 195 := by
  have hc : ((3597/8000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1287931029/40000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((3597/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c196 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-389859/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 192579/312500) (δ := 27/2000000) (ψ := 181581/500000) 266 223
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t196 : ((-34811085353/625000000000 : ℚ) : ℝ) ≤ stT266 196 := by
  have hc : ((-97471/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34811085353/625000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-97471/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c197 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-779381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6161183/10000000) (δ := 1341/100000000) (ψ := 181581/500000) 266 224
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t197 : ((-555321984001/10000000000000 : ℚ) : ℝ) ≤ stT266 197 := by
  have hc : ((-779431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-555321984001/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-779431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c198 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((437809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2794089/10000000) (δ := 13393/1000000000) (ψ := 181581/500000) 266 224
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t198 : ((311101750771/10000000000000 : ℚ) : ℝ) ≤ stT266 198 := by
  have hc : ((437759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((311101750771/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((437759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c199 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((975367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 34753/625000) (δ := 13393/1000000000) (ψ := 181581/500000) 266 224
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t199 : ((691383690277/10000000000000 : ℚ) : ℝ) ≤ stT266 199 := by
  have hc : ((975317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((691383690277/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((975317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c200 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((15051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3889361/10000000) (δ := 1341/100000000) (ψ := 181581/500000) 266 224
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t200 : ((5303648553/5000000000000 : ℚ) : ℝ) ≤ stT266 200 := by
  have hc : ((15001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5303648553/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((15001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c201 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-966609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1441223/2000000) (δ := 1341/100000000) (ψ := 181581/500000) 266 224
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t201 : ((-340914529507/5000000000000 : ℚ) : ℝ) ≤ stT266 201 := by
  have hc : ((-966659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-340914529507/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-966659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c202 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-488059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5201653/10000000) (δ := 13317/1000000000) (ψ := 181581/500000) 266 225
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t202 : ((-171716258091/5000000000000 : ℚ) : ℝ) ≤ stT266 202 := by
  have hc : ((-488109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171716258091/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-488109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c203 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((143989/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -479421/2500000) (δ := 6743/500000000) (ψ := 181581/500000) 266 225
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t203 : ((50526694449/1000000000000 : ℚ) : ℝ) ≤ stT266 203 := by
  have hc : ((143979/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50526694449/1000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((143979/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c204 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((857683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 675063/5000000) (δ := 6743/500000000) (ψ := 181581/500000) 266 225
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t204 : ((30023158431/500000000000 : ℚ) : ℝ) ≤ stT266 204 := by
  have hc : ((857633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30023158431/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((857633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c205 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-133363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 575247/1250000) (δ := 6743/500000000) (ψ := 181581/500000) 266 225
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t205 : ((-23290578557/1250000000000 : ℚ) : ℝ) ≤ stT266 205 := by
  have hc : ((-33347/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23290578557/1250000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-33347/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c206 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-49999/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7837999/10000000) (δ := 6743/500000000) (ψ := 181581/500000) 266 225
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t206 : ((-34837745101/500000000000 : ℚ) : ℝ) ≤ stT266 206 := by
  have hc : ((-100003/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34837745101/500000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-100003/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c207 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-285049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -929927/2000000) (δ := 13379/1000000000) (ψ := 181581/500000) 266 226
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t207 : ((-198157774851/10000000000000 : ℚ) : ℝ) ≤ stT266 207 := by
  have hc : ((-285099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198157774851/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-285099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c208 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((837601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -903/6250) (δ := 839/62500000) (ψ := 181581/500000) 266 226
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t208 : ((4645895397/80000000000 : ℚ) : ℝ) ≤ stT266 208 := by
  have hc : ((837551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4645895397/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((837551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c209 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((766213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1744673/10000000) (δ := 839/62500000) (ψ := 181581/500000) 266 226
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t209 : ((264982836691/5000000000000 : ℚ) : ℝ) ≤ stT266 209 := by
  have hc : ((766163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((264982836691/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((766163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c210 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-193221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4918917/10000000) (δ := 13379/1000000000) (ψ := 181581/500000) 266 226
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t210 : ((-33338123559/1250000000000 : ℚ) : ℝ) ≤ stT266 210 := by
  have hc : ((-96623/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33338123559/1250000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-96623/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c211 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-497993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7629897/10000000) (δ := 13331/1000000000) (ψ := 181581/500000) 266 227
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t211 : ((-171425016861/2500000000000 : ℚ) : ℝ) ≤ stT266 211 := by
  have hc : ((-249009/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171425016861/2500000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-249009/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c212 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-3463/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4485711/10000000) (δ := 421/31250000) (ψ := 181581/500000) 266 227
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t212 : ((-76125931323/5000000000000 : ℚ) : ℝ) ≤ stT266 212 := by
  have hc : ((-110841/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76125931323/5000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-110841/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c213 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((856413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1356287/10000000) (δ := 13331/1000000000) (ψ := 181581/500000) 266 227
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t213 : ((146692412811/2500000000000 : ℚ) : ℝ) ≤ stT266 213 := by
  have hc : ((856363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146692412811/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((856363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c214 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((381323/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 879253/5000000) (δ := 421/31250000) (ψ := 181581/500000) 266 227
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t214 : ((26064959333/500000000000 : ℚ) : ℝ) ≤ stT266 214 := by
  have hc : ((190649/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26064959333/500000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((190649/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c215 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-36413/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 303671/625000) (δ := 421/31250000) (ψ := 181581/500000) 266 227
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t215 : ((-2483689391/100000000000 : ℚ) : ℝ) ≤ stT266 215 := by
  have hc : ((-18209/50000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2483689391/100000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-18209/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c216 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-999343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7763361/10000000) (δ := 2673/200000000) (ψ := 181581/500000) 266 228
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t216 : ((-340000494351/5000000000000 : ℚ) : ℝ) ≤ stT266 216 := by
  have hc : ((-999393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-340000494351/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-999393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c217 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-301171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -293237/625000) (δ := 6719/500000000) (ψ := 181581/500000) 266 228
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t217 : ((-40896473949/2000000000000 : ℚ) : ℝ) ≤ stT266 217 := by
  have hc : ((-301221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40896473949/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-301221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c218 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((396911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -817161/5000000) (δ := 2673/200000000) (ψ := 181581/500000) 266 228
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t218 : ((26880493451/500000000000 : ℚ) : ℝ) ≤ stT266 218 := by
  have hc : ((198443/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26880493451/500000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((198443/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c219 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((422649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44037/312500) (δ := 6719/500000000) (ψ := 181581/500000) 266 228
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t219 : ((8924458559/156250000000 : ℚ) : ℝ) ≤ stT266 219 := by
  have hc : ((13207/15625 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8924458559/156250000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((13207/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c220 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-203293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4438791/10000000) (δ := 6719/500000000) (ψ := 181581/500000) 266 228
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t220 : ((-685469253/50000000000 : ℚ) : ℝ) ≤ stT266 220 := by
  have hc : ((-203343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-685469253/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-203343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c221 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-987273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7454699/10000000) (δ := 6719/500000000) (ψ := 181581/500000) 266 228
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t221 : ((-664145524379/10000000000000 : ℚ) : ℝ) ≤ stT266 221 := by
  have hc : ((-987323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-664145524379/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-987323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c222 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-505211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -328191/625000) (δ := 13457/1000000000) (ψ := 181581/500000) 266 229
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t222 : ((-339109456977/10000000000000 : ℚ) : ℝ) ≤ stT266 222 := by
  have hc : ((-505261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-339109456977/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-505261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c223 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((123551/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56557/250000) (δ := 13457/1000000000) (ψ := 181581/500000) 266 229
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t223 : ((82729107109/2000000000000 : ℚ) : ℝ) ≤ stT266 223 := by
  have hc : ((123541/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82729107109/2000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((123541/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c224 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((959591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71313/1000000) (δ := 6673/500000000) (ψ := 181581/500000) 266 229
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t224 : ((641120197773/10000000000000 : ℚ) : ℝ) ≤ stT266 224 := by
  have hc : ((959541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((641120197773/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((959541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c225 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((12563/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1837653/5000000) (δ := 6673/500000000) (ψ := 181581/500000) 266 229
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t225 : ((16742316591/2500000000000 : ℚ) : ℝ) ≤ stT266 225 := by
  have hc : ((50227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16742316591/2500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((50227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c226 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-881447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3312141/5000000) (δ := 13373/500000000) (ψ := 181581/500000) 266 229
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t226 : ((-586363870927/10000000000000 : ℚ) : ℝ) ≤ stT266 226 := by
  have hc : ((-881497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-586363870927/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-881497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c227 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-48499/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6147673/10000000) (δ := 13453/1000000000) (ψ := 181581/500000) 266 230
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t227 : ((-64384048827/1250000000000 : ℚ) : ℝ) ≤ stT266 227 := by
  have hc : ((-388017/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64384048827/1250000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-388017/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c228 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((11091/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3224599/10000000) (δ := 13453/1000000000) (ψ := 181581/500000) 266 230
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t228 : ((3671933837/200000000000 : ℚ) : ℝ) ≤ stT266 228 := by
  have hc : ((11089/40000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3671933837/200000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((11089/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c229 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((248027/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -314293/10000000) (δ := 13453/1000000000) (ψ := 181581/500000) 266 230
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t229 : ((163892445861/2500000000000 : ℚ) : ℝ) ≤ stT266 229 := by
  have hc : ((496029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163892445861/2500000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((496029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c230 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((255983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2583311/10000000) (δ := 267/20000000) (ψ := 181581/500000) 266 230
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t230 : ((4219339651/125000000000 : ℚ) : ℝ) ≤ stT266 230 := by
  have hc : ((127979/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4219339651/125000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((127979/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c231 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-289109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5468347/10000000) (δ := 267/20000000) (ψ := 181581/500000) 266 230
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t231 : ((-2972442087/78125000000 : ℚ) : ℝ) ≤ stT266 231 := by
  have hc : ((-144567/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2972442087/78125000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-144567/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c232 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-490547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3683541/5000000) (δ := 167/12500000) (ψ := 181581/500000) 266 231
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t232 : ((-80519176719/1250000000000 : ℚ) : ℝ) ≤ stT266 232 := by
  have hc : ((-122643/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80519176719/1250000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-122643/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c233 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-22987/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4506851/10000000) (δ := 13443/1000000000) (ψ := 181581/500000) 266 231
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t233 : ((-470705157/31250000000 : ℚ) : ℝ) ≤ stT266 233 := by
  have hc : ((-1437/6250 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-470705157/31250000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-1437/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c234 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((98477/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -331771/2000000) (δ := 167/12500000) (ψ := 181581/500000) 266 231
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t234 : ((6437229869/125000000000 : ℚ) : ℝ) ≤ stT266 234 := by
  have hc : ((393883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6437229869/125000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((393883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c235 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((891211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1176971/10000000) (δ := 167/12500000) (ψ := 181581/500000) 266 231
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t235 : ((72666159101/1250000000000 : ℚ) : ℝ) ≤ stT266 235 := by
  have hc : ((891161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72666159101/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((891161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c236 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-29503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 100019/250000) (δ := 13443/1000000000) (ψ := 181581/500000) 266 231
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t236 : ((-3847475517/2000000000000 : ℚ) : ℝ) ≤ stT266 236 := by
  have hc : ((-29553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3847475517/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-29553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c237 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-457243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 340629/500000) (δ := 167/12500000) (ψ := 181581/500000) 266 231
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t237 : ((-7425689369/125000000000 : ℚ) : ℝ) ≤ stT266 237 := by
  have hc : ((-114317/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7425689369/125000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-114317/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c238 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-762627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6095401/10000000) (δ := 1667/125000000) (ψ := 181581/500000) 266 232
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t238 : ((-123592570527/2500000000000 : ℚ) : ℝ) ≤ stT266 238 := by
  have hc : ((-762677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123592570527/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-762677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c239 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((49083/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1653561/5000000) (δ := 13467/1000000000) (ψ := 181581/500000) 266 232
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t239 : ((15871336879/1000000000000 : ℚ) : ℝ) ≤ stT266 239 := by
  have hc : ((49073/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15871336879/1000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((49073/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c240 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((244393/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -530481/10000000) (δ := 13467/1000000000) (ψ := 181581/500000) 266 232
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t240 : ((315493759217/5000000000000 : ℚ) : ℝ) ≤ stT266 240 := by
  have hc : ((488761/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((315493759217/5000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((488761/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c241 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((626427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2234589/10000000) (δ := 13467/1000000000) (ψ := 181581/500000) 266 232
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t241 : ((100871125703/2500000000000 : ℚ) : ℝ) ≤ stT266 241 := by
  have hc : ((626377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100871125703/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((626377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c242 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-205929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4988221/10000000) (δ := 13467/1000000000) (ψ := 181581/500000) 266 232
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t242 : ((-2647847601/100000000000 : ℚ) : ℝ) ≤ stT266 242 := by
  have hc : ((-102977/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2647847601/100000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-102977/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c243 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-49939/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7730481/10000000) (δ := 1667/125000000) (ψ := 181581/500000) 266 232
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t243 : ((-64075044383/1000000000000 : ℚ) : ℝ) ≤ stT266 243 := by
  have hc : ((-99883/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64075044383/1000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-99883/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c244 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-503623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -262323/500000) (δ := 6687/500000000) (ψ := 181581/500000) 266 233
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t244 : ((-64488779901/2000000000000 : ℚ) : ℝ) ≤ stT266 244 := by
  have hc : ((-503673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64488779901/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-503673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c245 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((66413/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2526643/10000000) (δ := 13387/500000000) (ψ := 181581/500000) 266 233
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t245 : ((42425678813/1250000000000 : ℚ) : ℝ) ≤ stT266 245 := by
  have hc : ((265627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42425678813/1250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((265627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c246 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((997347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 91067/5000000) (δ := 13429/1000000000) (ψ := 181581/500000) 266 233
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t246 : ((79481579009/1250000000000 : ℚ) : ℝ) ≤ stT266 246 := by
  have hc : ((997297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79481579009/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((997297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c247 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((81339/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1439953/5000000) (δ := 13429/1000000000) (ψ := 181581/500000) 266 233
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t247 : ((12937085359/500000000000 : ℚ) : ℝ) ≤ stT266 247 := by
  have hc : ((81329/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12937085359/500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((81329/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c248 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-609883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1391693/2500000) (δ := 13429/1000000000) (ψ := 181581/500000) 266 233
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t248 : ((-387308064933/10000000000000 : ℚ) : ℝ) ≤ stT266 248 := by
  have hc : ((-609933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-387308064933/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-609933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c249 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-98793/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1866291/2500000) (δ := 6741/500000000) (ψ := 181581/500000) 266 234
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t249 : ((-1252215251/20000000000 : ℚ) : ℝ) ≤ stT266 249 := by
  have hc : ((-49399/50000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1252215251/20000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-49399/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c250 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-171033/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2399889/5000000) (δ := 13321/1000000000) (ψ := 181581/500000) 266 234
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t250 : ((-6761666153/312500000000 : ℚ) : ℝ) ≤ stT266 250 := by
  have hc : ((-85529/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6761666153/312500000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-85529/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c251 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((326961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1072549/5000000) (δ := 13321/1000000000) (ψ := 181581/500000) 266 234
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t251 : ((12897502599/312500000000 : ℚ) : ℝ) ≤ stT266 251 := by
  have hc : ((40867/62500 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12897502599/312500000000 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((40867/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c252 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((196029/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 499009/10000000) (δ := 6741/500000000) (ψ := 181581/500000) 266 234
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t252 : ((6174010443/100000000000 : ℚ) : ℝ) ≤ stT266 252 := by
  have hc : ((196019/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).1
  have hw2 : ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31497/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6174010443/100000000000 : ℚ) : ℝ)
      = ((31497/500000 : ℚ) : ℝ) * ((196019/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c253 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((312407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 125307/400000) (δ := 6741/500000000) (ψ := 181581/500000) 266 234
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t253 : ((98188485879/5000000000000 : ℚ) : ℝ) ≤ stT266 253 := by
  have hc : ((312357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).1
  have hw2 : ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((314347/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98188485879/5000000000000 : ℚ) : ℝ)
      = ((314347/5000000 : ℚ) : ℝ) * ((312357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c254 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-334027/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5755967/10000000) (δ := 6741/500000000) (ψ := 181581/500000) 266 234
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t254 : ((-204690363/4882812500 : ℚ) : ℝ) ≤ stT266 254 := by
  have hc : ((-83513/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204690363/4882812500 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-83513/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c255 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-978859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1834753/2500000) (δ := 13389/1000000000) (ψ := 181581/500000) 266 235
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t255 : ((-24520691541/400000000000 : ℚ) : ℝ) ≤ stT266 255 := by
  have hc : ((-978909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24520691541/400000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-978909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c256 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-318087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4736269/10000000) (δ := 6707/500000000) (ψ := 181581/500000) 266 235
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t256 : ((-198835943137/10000000000000 : ℚ) : ℝ) ≤ stT266 256 := by
  have hc : ((-318137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).2
  have h0 : (0:ℝ) ≤ ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198835943137/10000000000000 : ℚ) : ℝ)
      = ((625001/10000000 : ℚ) : ℝ) * ((-318137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c257 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((130869/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21437/100000) (δ := 6707/500000000) (ψ := 181581/500000) 266 235
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t257 : ((40813744369/1000000000000 : ℚ) : ℝ) ≤ stT266 257 := by
  have hc : ((130859/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40813744369/1000000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((130859/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c258 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((492317/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109707/2500000) (δ := 13389/1000000000) (ψ := 181581/500000) 266 235
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t258 : ((19155450939/312500000000 : ℚ) : ℝ) ≤ stT266 258 := by
  have hc : ((123073/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19155450939/312500000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((123073/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c259 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((358111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 150569/500000) (δ := 6707/500000000) (ψ := 181581/500000) 266 235
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t259 : ((222488005509/10000000000000 : ℚ) : ℝ) ≤ stT266 259 := by
  have hc : ((358061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).1
  have hw2 : ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((621369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222488005509/10000000000000 : ℚ) : ℝ)
      = ((621369/10000000 : ℚ) : ℝ) * ((358061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c260 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-612179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 696753/1250000) (δ := 6707/500000000) (ψ := 181581/500000) 266 235
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t260 : ((-189844253923/5000000000000 : ℚ) : ℝ) ≤ stT266 260 := by
  have hc : ((-612229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-189844253923/5000000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-612229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c261 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-19881/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7581137/10000000) (δ := 13307/1000000000) (ψ := 181581/500000) 266 236
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t261 : ((-1230665977/20000000000 : ℚ) : ℝ) ≤ stT266 261 := by
  have hc : ((-9941/10000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1230665977/20000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-9941/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c262 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-429959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -503811/1000000) (δ := 1253/31250000) (ψ := 181581/500000) 266 236
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t262 : ((-265660850227/10000000000000 : ℚ) : ℝ) ≤ stT266 262 := by
  have hc : ((-430009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-265660850227/10000000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-430009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c263 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((8417/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2504793/10000000) (δ := 13307/1000000000) (ψ := 181581/500000) 266 236
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t263 : ((83034548847/2500000000000 : ℚ) : ℝ) ≤ stT266 263 := by
  have hc : ((269319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83034548847/2500000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((269319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c264 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((999971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18949/10000000) (δ := 1253/31250000) (ψ := 181581/500000) 266 236
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t264 : ((615408378897/10000000000000 : ℚ) : ℝ) ≤ stT266 264 := by
  have hc : ((999921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((615408378897/10000000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((999921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c265 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((529109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1266557/5000000) (δ := 13307/1000000000) (ψ := 181581/500000) 266 236
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t265 : ((64999659681/2000000000000 : ℚ) : ℝ) ≤ stT266 265 := by
  have hc : ((529059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64999659681/2000000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((529059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c266 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-429861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5037837/10000000) (δ := 1687/125000000) (ψ := 181581/500000) 266 236
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t266 : ((-13179781527/500000000000 : ℚ) : ℝ) ≤ stT266 266 := by
  have hc : ((-429911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13179781527/500000000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-429911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c267 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-39671/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1883279/2500000) (δ := 13307/1000000000) (ψ := 181581/500000) 266 236
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t267 : ((-24279518943/400000000000 : ℚ) : ℝ) ≤ stT266 267 := by
  have hc : ((-39673/40000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24279518943/400000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-39673/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c268 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-647847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2844439/5000000) (δ := 67/5000000) (ψ := 181581/500000) 266 237
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t268 : ((-12367705833/312500000000 : ℚ) : ℝ) ≤ stT266 268 := by
  have hc : ((-647897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12367705833/312500000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-647897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c269 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((56411/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -401519/1250000) (δ := 67/5000000) (ψ := 181581/500000) 266 237
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t269 : ((3438825371/200000000000 : ℚ) : ℝ) ≤ stT266 269 := by
  have hc : ((56401/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3438825371/200000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((56401/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c270 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((238993/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -744603/10000000) (δ := 67/5000000) (ψ := 181581/500000) 266 237
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t270 : ((14543875269/250000000000 : ℚ) : ℝ) ≤ stT266 270 := by
  have hc : ((477961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14543875269/250000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((477961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c271 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((774081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 428459/2500000) (δ := 13403/1000000000) (ψ := 181581/500000) 266 237
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t271 : ((14693430473/312500000000 : ℚ) : ℝ) ≤ stT266 271 := by
  have hc : ((774031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14693430473/312500000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((774031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c272 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-94329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1040791/2500000) (δ := 13403/1000000000) (ψ := 181581/500000) 266 237
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t272 : ((-2861288143/500000000000 : ℚ) : ℝ) ≤ stT266 272 := by
  have hc : ((-94379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).2
  have h0 : (0:ℝ) ≤ ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2861288143/500000000000 : ℚ) : ℝ)
      = ((30317/500000 : ℚ) : ℝ) * ((-94379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c273 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-877493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3301757/5000000) (δ := 67/5000000) (ψ := 181581/500000) 266 237
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t273 : ((-132778398701/2500000000000 : ℚ) : ℝ) ≤ stT266 273 := by
  have hc : ((-877543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132778398701/2500000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-877543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c274 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-111309/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6672943/10000000) (δ := 1331/100000000) (ψ := 181581/500000) 266 238
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t274 : ((-268992411103/5000000000000 : ℚ) : ℝ) ≤ stT266 274 := by
  have hc : ((-445261/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-268992411103/5000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-445261/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c275 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-129009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -850083/2000000) (δ := 13493/1000000000) (ψ := 181581/500000) 266 238
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t275 : ((-77825545357/10000000000000 : ℚ) : ℝ) ≤ stT266 275 := by
  have hc : ((-129059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77825545357/10000000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-129059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c276 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((742073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -918299/5000000) (δ := 13493/1000000000) (ψ := 181581/500000) 266 238
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t276 : ((446645162367/10000000000000 : ℚ) : ℝ) ≤ stT266 276 := by
  have hc : ((742023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((446645162367/10000000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((742023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c277 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((194851/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 142127/2500000) (δ := 1331/100000000) (ψ := 181581/500000) 266 238
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t277 : ((117068461281/2000000000000 : ℚ) : ℝ) ≤ stT266 277 := by
  have hc : ((194841/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117068461281/2000000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((194841/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c278 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((375407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1482451/5000000) (δ := 1331/100000000) (ψ := 181581/500000) 266 238
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t278 : ((2814051429/125000000000 : ℚ) : ℝ) ≤ stT266 278 := by
  have hc : ((375357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2814051429/125000000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((375357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c279 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-269927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5352651/10000000) (δ := 1331/100000000) (ψ := 181581/500000) 266 238
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t279 : ((-252525333/7812500000 : ℚ) : ℝ) ≤ stT266 279 := by
  have hc : ((-8436/15625 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).2
  have h0 : (0:ℝ) ≤ ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252525333/7812500000 : ℚ) : ℝ)
      = ((119737/2000000 : ℚ) : ℝ) * ((-8436/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c280 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-998809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3865977/5000000) (δ := 13493/1000000000) (ψ := 181581/500000) 266 238
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t280 : ((-119386624257/2000000000000 : ℚ) : ℝ) ≤ stT266 280 := by
  have hc : ((-998859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119386624257/2000000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-998859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c281 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-311009/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1401321/2500000) (δ := 6693/500000000) (ψ := 181581/500000) 266 239
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t281 : ((-1855473327/50000000000 : ℚ) : ℝ) ≤ stT266 281 := by
  have hc : ((-155517/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1855473327/50000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-155517/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c282 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((13511/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1621469/5000000) (δ := 6693/500000000) (ψ := 181581/500000) 266 239
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t282 : ((16088380347/1000000000000 : ℚ) : ℝ) ≤ stT266 282 := by
  have hc : ((27017/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16088380347/1000000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((27017/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c283 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((468721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -888971/10000000) (δ := 6693/500000000) (ψ := 181581/500000) 266 239
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t283 : ((17413169553/312500000000 : ℚ) : ℝ) ≤ stT266 283 := by
  have hc : ((58587/62500 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17413169553/312500000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((58587/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c284 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((41749/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5827/40000) (δ := 6693/500000000) (ψ := 181581/500000) 266 239
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t284 : ((4954391127/100000000000 : ℚ) : ℝ) ≤ stT266 284 := by
  have hc : ((83493/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4954391127/100000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((83493/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c285 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((13277/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3794159/10000000) (δ := 13417/1000000000) (ψ := 181581/500000) 266 239
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t285 : ((3928600023/1250000000000 : ℚ) : ℝ) ≤ stT266 285 := by
  have hc : ((26529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).1
  have hw2 : ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((148087/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3928600023/1250000000000 : ℚ) : ℝ)
      = ((148087/2500000 : ℚ) : ℝ) * ((26529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c286 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-769837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3061727/5000000) (δ := 6693/500000000) (ψ := 181581/500000) 266 239
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t286 : ((-455244191631/10000000000000 : ℚ) : ℝ) ≤ stT266 286 := by
  have hc : ((-769887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-455244191631/10000000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-769887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c287 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-486113/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7263393/10000000) (δ := 533/40000000) (ψ := 181581/500000) 266 240
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t287 : ((-71739627729/1250000000000 : ℚ) : ℝ) ≤ stT266 287 := by
  have hc : ((-243069/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71739627729/1250000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-243069/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c288 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-199011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -495039/1000000) (δ := 533/40000000) (ψ := 181581/500000) 266 240
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t288 : ((-3665098663/156250000000 : ℚ) : ℝ) ≤ stT266 288 := by
  have hc : ((-49759/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).2
  have h0 : (0:ℝ) ≤ ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3665098663/156250000000 : ℚ) : ℝ)
      = ((73657/1250000 : ℚ) : ℝ) * ((-49759/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c289 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((61311/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2645367/10000000) (δ := 533/40000000) (ψ := 181581/500000) 266 240
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t289 : ((28849279693/1000000000000 : ℚ) : ℝ) ≤ stT266 289 := by
  have hc : ((245219/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28849279693/1000000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((245219/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c290 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((990313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -174129/5000000) (δ := 6739/500000000) (ψ := 181581/500000) 266 240
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t290 : ((29075111943/500000000000 : ℚ) : ℝ) ≤ stT266 290 := by
  have hc : ((990263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29075111943/500000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((990263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c291 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((713477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 242609/1250000) (δ := 533/40000000) (ψ := 181581/500000) 266 240
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t291 : ((41821804167/1000000000000 : ℚ) : ℝ) ≤ stT266 291 := by
  have hc : ((713427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41821804167/1000000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((713427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c292 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-58909/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4222221/10000000) (δ := 533/40000000) (ψ := 181581/500000) 266 240
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t292 : ((-8622132601/1250000000000 : ℚ) : ℝ) ≤ stT266 292 := by
  have hc : ((-29467/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).2
  have h0 : (0:ℝ) ≤ ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8622132601/1250000000000 : ℚ) : ℝ)
      = ((292603/5000000 : ℚ) : ℝ) * ((-29467/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c293 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-428003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6495723/10000000) (δ := 533/40000000) (ψ := 181581/500000) 266 240
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t293 : ((-62514238449/1250000000000 : ℚ) : ℝ) ≤ stT266 293 := by
  have hc : ((-107007/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).2
  have h0 : (0:ℝ) ≤ ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62514238449/1250000000000 : ℚ) : ℝ)
      = ((584207/10000000 : ℚ) : ℝ) * ((-107007/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c294 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-934841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6946519/10000000) (δ := 13371/1000000000) (ψ := 181581/500000) 266 241
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t294 : ((-136309912473/2500000000000 : ℚ) : ℝ) ≤ stT266 294 := by
  have hc : ((-934891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136309912473/2500000000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-934891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c295 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-149947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -937689/2000000) (δ := 13371/1000000000) (ψ := 181581/500000) 266 241
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t295 : ((-21829286939/1250000000000 : ℚ) : ℝ) ≤ stT266 295 := by
  have hc : ((-37493/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).2
  have h0 : (0:ℝ) ≤ ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21829286939/1250000000000 : ℚ) : ℝ)
      = ((582223/10000000 : ℚ) : ℝ) * ((-37493/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c296 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((560997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1219009/5000000) (δ := 1679/125000000) (ψ := 181581/500000) 266 241
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t296 : ((163021856193/5000000000000 : ℚ) : ℝ) ≤ stT266 296 := by
  have hc : ((560947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).1
  have hw2 : ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163021856193/5000000000000 : ℚ) : ℝ)
      = ((290619/5000000 : ℚ) : ℝ) * ((560947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c297 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((498477/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -195173/10000000) (δ := 13371/1000000000) (ψ := 181581/500000) 266 241
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t297 : ((36153845077/625000000000 : ℚ) : ℝ) ≤ stT266 297 := by
  have hc : ((124613/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).1
  have hw2 : ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290129/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36153845077/625000000000 : ℚ) : ℝ)
      = ((290129/5000000 : ℚ) : ℝ) * ((124613/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c298 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((342557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 510023/2500000) (δ := 1679/125000000) (ψ := 181581/500000) 266 241
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t298 : ((12401456693/312500000000 : ℚ) : ℝ) ≤ stT266 298 := by
  have hc : ((85633/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12401456693/312500000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((85633/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c299 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-27189/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1066977/2500000) (δ := 13371/1000000000) (ψ := 181581/500000) 266 241
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t299 : ((-3145917937/400000000000 : ℚ) : ℝ) ≤ stT266 299 := by
  have hc : ((-27199/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).2
  have h0 : (0:ℝ) ≤ ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3145917937/400000000000 : ℚ) : ℝ)
      = ((115663/2000000 : ℚ) : ℝ) * ((-27199/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c300 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-427231/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6488277/10000000) (δ := 1679/125000000) (ψ := 181581/500000) 266 241
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t300 : ((-30834584857/625000000000 : ℚ) : ℝ) ≤ stT266 300 := by
  have hc : ((-53407/62500 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).2
  have h0 : (0:ℝ) ≤ ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30834584857/625000000000 : ℚ) : ℝ)
      = ((577351/10000000 : ℚ) : ℝ) * ((-53407/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c301 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-943117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -70067/100000) (δ := 1683/125000000) (ψ := 181581/500000) 266 242
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t301 : ((-543632970297/10000000000000 : ℚ) : ℝ) ≤ stT266 301 := by
  have hc : ((-943167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).2
  have h0 : (0:ℝ) ≤ ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-543632970297/10000000000000 : ℚ) : ℝ)
      = ((576391/10000000 : ℚ) : ℝ) * ((-943167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c302 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-42817/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1200257/2500000) (δ := 1683/125000000) (ψ := 181581/500000) 266 242
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t302 : ((-24642039687/1250000000000 : ℚ) : ℝ) ≤ stT266 302 := by
  have hc : ((-171293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24642039687/1250000000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-171293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c303 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((505299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2602671/10000000) (δ := 1683/125000000) (ψ := 181581/500000) 266 242
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t303 : ((72564366629/2500000000000 : ℚ) : ℝ) ≤ stT266 303 := by
  have hc : ((505249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).1
  have hw2 : ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143621/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72564366629/2500000000000 : ℚ) : ℝ)
      = ((143621/2500000 : ℚ) : ℝ) * ((505249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c304 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((12331/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -205781/5000000) (δ := 13339/1000000000) (ψ := 181581/500000) 266 242
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t304 : ((56575607577/1000000000000 : ℚ) : ℝ) ≤ stT266 304 := by
  have hc : ((98643/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).1
  have hw2 : ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56575607577/1000000000000 : ℚ) : ℝ)
      = ((573539/10000000 : ℚ) : ℝ) * ((98643/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c305 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((379533/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 886149/5000000) (δ := 13339/1000000000) (ψ := 181581/500000) 266 242
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t305 : ((27163190223/625000000000 : ℚ) : ℝ) ≤ stT266 305 := by
  have hc : ((94877/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).1
  have hw2 : ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((286299/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27163190223/625000000000 : ℚ) : ℝ)
      = ((286299/5000000 : ℚ) : ℝ) * ((94877/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c306 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-8847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3949109/10000000) (δ := 13339/1000000000) (ψ := 181581/500000) 266 242
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t306 : ((-2543038407/5000000000000 : ℚ) : ℝ) ≤ stT266 306 := by
  have hc : ((-8897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).2
  have h0 : (0:ℝ) ≤ ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2543038407/5000000000000 : ℚ) : ℝ)
      = ((285831/5000000 : ℚ) : ℝ) * ((-8897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c307 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-768631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3059369/5000000) (δ := 13339/1000000000) (ψ := 181581/500000) 266 242
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t307 : ((-438710075811/10000000000000 : ℚ) : ℝ) ≤ stT266 307 := by
  have hc : ((-768681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).2
  have h0 : (0:ℝ) ≤ ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-438710075811/10000000000000 : ℚ) : ℝ)
      = ((570731/10000000 : ℚ) : ℝ) * ((-768681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c308 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-492713/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1485329/2000000) (δ := 6723/500000000) (ψ := 181581/500000) 266 243
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t308 : ((-140381795307/2500000000000 : ℚ) : ℝ) ≤ stT266 308 := by
  have hc : ((-246369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).2
  have h0 : (0:ℝ) ≤ ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140381795307/2500000000000 : ℚ) : ℝ)
      = ((569803/10000000 : ℚ) : ℝ) * ((-246369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c309 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-16003/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -658881/1250000) (δ := 13357/1000000000) (ψ := 181581/500000) 266 243
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t309 : ((-145675064313/5000000000000 : ℚ) : ℝ) ≤ stT266 309 := by
  have hc : ((-256073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).2
  have h0 : (0:ℝ) ≤ ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145675064313/5000000000000 : ℚ) : ℝ)
      = ((568881/10000000 : ℚ) : ℝ) * ((-256073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c310 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((316297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3122433/10000000) (δ := 13357/1000000000) (ψ := 181581/500000) 266 243
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t310 : ((179615962367/10000000000000 : ℚ) : ℝ) ≤ stT266 310 := by
  have hc : ((316247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).1
  have hw2 : ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567961/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179615962367/10000000000000 : ℚ) : ℝ)
      = ((567961/10000000 : ℚ) : ℝ) * ((316247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c311 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((184809/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -980667/10000000) (δ := 6723/500000000) (ψ := 181581/500000) 266 243
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t311 : ((104789718553/2000000000000 : ℚ) : ℝ) ≤ stT266 311 := by
  have hc : ((184799/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).1
  have hw2 : ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104789718553/2000000000000 : ℚ) : ℝ)
      = ((567047/10000000 : ℚ) : ℝ) * ((184799/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c312 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((22383/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 288529/2500000) (δ := 6723/500000000) (ψ := 181581/500000) 266 243
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t312 : ((25342318363/500000000000 : ℚ) : ℝ) ≤ stT266 312 := by
  have hc : ((89527/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).1
  have hw2 : ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((283069/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25342318363/500000000000 : ℚ) : ℝ)
      = ((283069/5000000 : ℚ) : ℝ) * ((89527/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c313 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((255099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 820529/2500000) (δ := 6723/500000000) (ψ := 181581/500000) 266 243
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t313 : ((144162111417/10000000000000 : ℚ) : ℝ) ≤ stT266 313 := by
  have hc : ((255049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).1
  have hw2 : ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((565233/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144162111417/10000000000000 : ℚ) : ℝ)
      = ((565233/10000000 : ℚ) : ℝ) * ((255049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c314 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-556807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5403333/10000000) (δ := 6723/500000000) (ψ := 181581/500000) 266 243
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t314 : ((-314252781381/10000000000000 : ℚ) : ℝ) ≤ stT266 314 := by
  have hc : ((-556857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).2
  have h0 : (0:ℝ) ≤ ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-314252781381/10000000000000 : ℚ) : ℝ)
      = ((564333/10000000 : ℚ) : ℝ) * ((-556857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c315 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-495487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7517833/10000000) (δ := 13357/1000000000) (ψ := 181581/500000) 266 243
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t315 : ((-34898724343/625000000000 : ℚ) : ℝ) ≤ stT266 315 := by
  have hc : ((-61939/62500 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).2
  have h0 : (0:ℝ) ≤ ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34898724343/625000000000 : ℚ) : ℝ)
      = ((563437/10000000 : ℚ) : ℝ) * ((-61939/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c316 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-379619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3041173/5000000) (δ := 13353/1000000000) (ψ := 181581/500000) 266 244
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t316 : ((-3336975849/78125000000 : ℚ) : ℝ) ≤ stT266 316 := by
  have hc : ((-94911/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).2
  have h0 : (0:ℝ) ≤ ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3336975849/78125000000 : ℚ) : ℝ)
      = ((35159/625000 : ℚ) : ℝ) * ((-94911/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c317 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-10857/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3981279/10000000) (δ := 269/20000000) (ψ := 181581/500000) 266 244
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t317 : ((-381996287/312500000000 : ℚ) : ℝ) ≤ stT266 317 := by
  have hc : ((-5441/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).2
  have h0 : (0:ℝ) ≤ ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-381996287/312500000000 : ℚ) : ℝ)
      = ((70207/1250000 : ℚ) : ℝ) * ((-5441/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c318 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((145693/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -377359/2000000) (δ := 269/20000000) (ψ := 181581/500000) 266 244
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t318 : ((20423736819/500000000000 : ℚ) : ℝ) ≤ stT266 318 := by
  have hc : ((145683/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).1
  have hw2 : ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140193/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20423736819/500000000000 : ℚ) : ℝ)
      = ((140193/2500000 : ℚ) : ℝ) * ((145683/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c319 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((249191/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50293/2500000) (δ := 269/20000000) (ψ := 181581/500000) 266 244
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t319 : ((69756524361/1250000000000 : ℚ) : ℝ) ≤ stT266 319 := by
  have hc : ((498357/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).1
  have hw2 : ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((139973/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69756524361/1250000000000 : ℚ) : ℝ)
      = ((139973/2500000 : ℚ) : ℝ) * ((498357/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c320 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((305689/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2282489/10000000) (δ := 269/20000000) (ψ := 181581/500000) 266 244
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t320 : ((41716569/1220703125 : ℚ) : ℝ) ≤ stT266 320 := by
  have hc : ((9552/15625 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).1
  have hw2 : ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69877/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41716569/1220703125 : ℚ) : ℝ)
      = ((69877/1250000 : ℚ) : ℝ) * ((9552/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c321 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-171323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2178711/5000000) (δ := 269/20000000) (ψ := 181581/500000) 266 244
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t321 : ((-47825577229/5000000000000 : ℚ) : ℝ) ≤ stT266 321 := by
  have hc : ((-171373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47825577229/5000000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-171373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c322 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-420611/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3212919/5000000) (δ := 269/20000000) (ψ := 181581/500000) 266 244
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t322 : ((-58602902361/1250000000000 : ℚ) : ℝ) ≤ stT266 322 := by
  have hc : ((-105159/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).2
  have h0 : (0:ℝ) ≤ ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58602902361/1250000000000 : ℚ) : ℝ)
      = ((557279/10000000 : ℚ) : ℝ) * ((-105159/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c323 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-968027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7220093/10000000) (δ := 13343/1000000000) (ψ := 181581/500000) 266 245
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t323 : ((-107730512791/2000000000000 : ℚ) : ℝ) ≤ stT266 323 := by
  have hc : ((-968077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).2
  have h0 : (0:ℝ) ≤ ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107730512791/2000000000000 : ℚ) : ℝ)
      = ((111283/2000000 : ℚ) : ℝ) * ((-968077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c324 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-59377/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1032889/2000000) (δ := 13343/1000000000) (ψ := 181581/500000) 266 245
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t324 : ((-32990720837/1250000000000 : ℚ) : ℝ) ≤ stT266 324 := by
  have hc : ((-237533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).2
  have h0 : (0:ℝ) ≤ ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32990720837/1250000000000 : ℚ) : ℝ)
      = ((138889/2500000 : ℚ) : ℝ) * ((-237533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c325 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((319047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3115181/10000000) (δ := 13343/1000000000) (ψ := 181581/500000) 266 245
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t325 : ((1769476359/100000000000 : ℚ) : ℝ) ≤ stT266 325 := by
  have hc : ((318997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1769476359/100000000000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((318997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c326 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((909437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -134021/1250000) (δ := 13343/1000000000) (ψ := 181581/500000) 266 245
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t326 : ((62957771397/1250000000000 : ℚ) : ℝ) ≤ stT266 326 := by
  have hc : ((909387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).1
  have hw2 : ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69231/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62957771397/1250000000000 : ℚ) : ℝ)
      = ((69231/1250000 : ℚ) : ℝ) * ((909387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c327 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((231621/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 482297/5000000) (δ := 13343/1000000000) (ψ := 181581/500000) 266 245
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t327 : ((256159464217/5000000000000 : ℚ) : ℝ) ≤ stT266 327 := by
  have hc : ((463217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).1
  have hw2 : ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((553001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((256159464217/5000000000000 : ℚ) : ℝ)
      = ((553001/10000000 : ℚ) : ℝ) * ((463217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c328 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((364157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 748793/2500000) (δ := 673/50000000) (ψ := 181581/500000) 266 245
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t328 : ((201044228799/10000000000000 : ℚ) : ℝ) ≤ stT266 328 := by
  have hc : ((364107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).1
  have hw2 : ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((552157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201044228799/10000000000000 : ℚ) : ℝ)
      = ((552157/10000000 : ℚ) : ℝ) * ((364107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c329 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-211613/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2509749/5000000) (δ := 13343/1000000000) (ψ := 181581/500000) 266 245
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t329 : ((-29169959721/1250000000000 : ℚ) : ℝ) ≤ stT266 329 := by
  have hc : ((-105819/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).2
  have h0 : (0:ℝ) ≤ ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29169959721/1250000000000 : ℚ) : ℝ)
      = ((275659/5000000 : ℚ) : ℝ) * ((-105819/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c330 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-29599/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7037707/10000000) (δ := 673/50000000) (ψ := 181581/500000) 266 245
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t330 : ((-130356614769/2500000000000 : ℚ) : ℝ) ≤ stT266 330 := by
  have hc : ((-473609/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).2
  have h0 : (0:ℝ) ≤ ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130356614769/2500000000000 : ℚ) : ℝ)
      = ((275241/5000000 : ℚ) : ℝ) * ((-473609/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c331 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-887767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3329083/5000000) (δ := 1671/125000000) (ψ := 181581/500000) 266 246
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t331 : ((-9759772281/200000000000 : ℚ) : ℝ) ≤ stT266 331 := by
  have hc : ((-887817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9759772281/200000000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-887817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c332 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-71501/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4652127/10000000) (δ := 1671/125000000) (ψ := 181581/500000) 266 246
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t332 : ((-39248182097/2500000000000 : ℚ) : ℝ) ≤ stT266 332 := by
  have hc : ((-143027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).2
  have h0 : (0:ℝ) ≤ ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39248182097/2500000000000 : ℚ) : ℝ)
      = ((274411/5000000 : ℚ) : ℝ) * ((-143027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c333 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((781/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -132607/500000) (δ := 2687/200000000) (ψ := 181581/500000) 266 246
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t333 : ((2674631477/100000000000 : ℚ) : ℝ) ≤ stT266 333 := by
  have hc : ((19523/40000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2674631477/100000000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((19523/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c334 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((241387/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -658137/10000000) (δ := 1671/125000000) (ψ := 181581/500000) 266 246
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t334 : ((10565927363/200000000000 : ℚ) : ℝ) ≤ stT266 334 := by
  have hc : ((482749/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10565927363/200000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((482749/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c335 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((172361/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1329947/10000000) (δ := 1671/125000000) (ψ := 181581/500000) 266 246
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t335 : ((47082673829/1000000000000 : ℚ) : ℝ) ≤ stT266 335 := by
  have hc : ((172351/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47082673829/1000000000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((172351/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c336 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((48701/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1656023/5000000) (δ := 1671/125000000) (ψ := 181581/500000) 266 246
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t336 : ((3320385363/250000000000 : ℚ) : ℝ) ≤ stT266 336 := by
  have hc : ((48691/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3320385363/250000000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((48691/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c337 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-64751/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5288293/10000000) (δ := 1671/125000000) (ψ := 181581/500000) 266 246
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t337 : ((-28220432463/1000000000000 : ℚ) : ℝ) ≤ stT266 337 := by
  have hc : ((-259029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).2
  have h0 : (0:ℝ) ≤ ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28220432463/1000000000000 : ℚ) : ℝ)
      = ((108947/2000000 : ℚ) : ℝ) * ((-259029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c338 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-971777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7258621/10000000) (δ := 2687/200000000) (ψ := 181581/500000) 266 246
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t338 : ((-528604888283/10000000000000 : ℚ) : ℝ) ≤ stT266 338 := by
  have hc : ((-971827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).2
  have h0 : (0:ℝ) ≤ ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-528604888283/10000000000000 : ℚ) : ℝ)
      = ((543929/10000000 : ℚ) : ℝ) * ((-971827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c339 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-34149/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1621183/2500000) (δ := 539/40000000) (ψ := 181581/500000) 266 247
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t339 : ((-9274148013/200000000000 : ℚ) : ℝ) ≤ stT266 339 := by
  have hc : ((-34151/40000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9274148013/200000000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-34151/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c340 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-59327/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -181039/400000) (δ := 833/62500000) (ψ := 181581/500000) 266 247
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t340 : ((-64362826033/5000000000000 : ℚ) : ℝ) ≤ stT266 340 := by
  have hc : ((-118679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).2
  have h0 : (0:ℝ) ≤ ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64362826033/5000000000000 : ℚ) : ℝ)
      = ((542327/10000000 : ℚ) : ℝ) * ((-118679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c341 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((515503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2573003/10000000) (δ := 833/62500000) (ψ := 181581/500000) 266 247
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t341 : ((27913326309/1000000000000 : ℚ) : ℝ) ≤ stT266 341 := by
  have hc : ((515453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).1
  have hw2 : ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((54153/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27913326309/1000000000000 : ℚ) : ℝ)
      = ((54153/1000000 : ℚ) : ℝ) * ((515453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c342 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((193769/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -625683/10000000) (δ := 539/40000000) (ψ := 181581/500000) 266 247
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t342 : ((52386427071/1000000000000 : ℚ) : ℝ) ≤ stT266 342 := by
  have hc : ((193759/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).1
  have hw2 : ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((270369/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52386427071/1000000000000 : ℚ) : ℝ)
      = ((270369/5000000 : ℚ) : ℝ) * ((193759/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c343 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((432319/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1315917/10000000) (δ := 833/62500000) (ψ := 181581/500000) 266 247
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t343 : ((116708356503/2500000000000 : ℚ) : ℝ) ≤ stT266 343 := by
  have hc : ((216147/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116708356503/2500000000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((216147/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c344 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((13339/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 650373/2000000) (δ := 833/62500000) (ψ := 181581/500000) 266 247
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t344 : ((14381094699/1000000000000 : ℚ) : ℝ) ≤ stT266 344 := by
  have hc : ((26673/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).1
  have hw2 : ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539163/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14381094699/1000000000000 : ℚ) : ℝ)
      = ((539163/10000000 : ℚ) : ℝ) * ((26673/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c345 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-481263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5182227/10000000) (δ := 833/62500000) (ψ := 181581/500000) 266 247
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t345 : ((-129565127783/5000000000000 : ℚ) : ℝ) ≤ stT266 345 := by
  have hc : ((-481313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).2
  have h0 : (0:ℝ) ≤ ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129565127783/5000000000000 : ℚ) : ℝ)
      = ((269191/5000000 : ℚ) : ℝ) * ((-481313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c346 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-191137/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7106937/10000000) (δ := 539/40000000) (ψ := 181581/500000) 266 247
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t346 : ((-25690347947/500000000000 : ℚ) : ℝ) ≤ stT266 346 := by
  have hc : ((-191147/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).2
  have h0 : (0:ℝ) ≤ ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25690347947/500000000000 : ℚ) : ℝ)
      = ((134401/2500000 : ℚ) : ℝ) * ((-191147/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c347 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-178417/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6681837/10000000) (δ := 13421/1000000000) (ψ := 181581/500000) 266 248
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t347 : ((-95784787983/2000000000000 : ℚ) : ℝ) ≤ stT266 347 := by
  have hc : ((-178427/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).2
  have h0 : (0:ℝ) ≤ ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95784787983/2000000000000 : ℚ) : ℝ)
      = ((536829/10000000 : ℚ) : ℝ) * ((-178427/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c348 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-330157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2384083/5000000) (δ := 6691/500000000) (ψ := 181581/500000) 266 248
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t348 : ((-177009773799/10000000000000 : ℚ) : ℝ) ≤ stT266 348 := by
  have hc : ((-330207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).2
  have h0 : (0:ℝ) ≤ ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177009773799/10000000000000 : ℚ) : ℝ)
      = ((536057/10000000 : ℚ) : ℝ) * ((-330207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c349 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((16559/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2859949/10000000) (δ := 13421/1000000000) (ψ := 181581/500000) 266 248
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t349 : ((8862746859/400000000000 : ℚ) : ℝ) ≤ stT266 349 := by
  have hc : ((16557/40000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).1
  have hw2 : ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((535287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8862746859/400000000000 : ℚ) : ℝ)
      = ((535287/10000000 : ℚ) : ℝ) * ((16557/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c350 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((185517/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -957251/10000000) (δ := 13421/1000000000) (ψ := 181581/500000) 266 248
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t350 : ((49578786327/1000000000000 : ℚ) : ℝ) ≤ stT266 350 := by
  have hc : ((185507/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).1
  have hw2 : ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((267261/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49578786327/1000000000000 : ℚ) : ℝ)
      = ((267261/5000000 : ℚ) : ℝ) * ((185507/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c351 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((232533/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 940061/10000000) (δ := 6691/500000000) (ψ := 181581/500000) 266 248
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t351 : ((193922097/3906250000 : ℚ) : ℝ) ≤ stT266 351 := by
  have hc : ((465041/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).1
  have hw2 : ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((834/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193922097/3906250000 : ℚ) : ℝ)
      = ((834/15625 : ℚ) : ℝ) * ((465041/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c352 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((84831/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2831919/10000000) (δ := 13421/1000000000) (ψ := 181581/500000) 266 248
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t352 : ((45209677821/2000000000000 : ℚ) : ℝ) ≤ stT266 352 := by
  have hc : ((84821/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).1
  have hw2 : ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((533001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45209677821/2000000000000 : ℚ) : ℝ)
      = ((533001/10000000 : ℚ) : ℝ) * ((84821/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c353 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-12453/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2359229/5000000) (δ := 6691/500000000) (ψ := 181581/500000) 266 248
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t353 : ((-1325827277/80000000000 : ℚ) : ℝ) ≤ stT266 353 := by
  have hc : ((-2491/8000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).2
  have h0 : (0:ℝ) ≤ ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1325827277/80000000000 : ℚ) : ℝ)
      = ((532247/10000000 : ℚ) : ℝ) * ((-2491/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c354 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-219189/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1649919/2500000) (δ := 13421/1000000000) (ψ := 181581/500000) 266 248
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t354 : ((-46601800497/1000000000000 : ℚ) : ℝ) ≤ stT266 354 := by
  have hc : ((-438403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).2
  have h0 : (0:ℝ) ≤ ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46601800497/1000000000000 : ℚ) : ℝ)
      = ((106299/2000000 : ℚ) : ℝ) * ((-438403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c355 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-193851/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1446491/2000000) (δ := 6657/500000000) (ψ := 181581/500000) 266 249
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t355 : ((-20578151289/400000000000 : ℚ) : ℝ) ≤ stT266 355 := by
  have hc : ((-193861/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20578151289/400000000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-193861/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c356 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-108587/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -536181/1000000) (δ := 6657/500000000) (ψ := 181581/500000) 266 249
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t356 : ((-57556301403/2000000000000 : ℚ) : ℝ) ≤ stT266 356 := by
  have hc : ((-108597/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).2
  have h0 : (0:ℝ) ≤ ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57556301403/2000000000000 : ℚ) : ℝ)
      = ((529999/10000000 : ℚ) : ℝ) * ((-108597/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c357 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((171353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -699297/2000000) (δ := 6657/500000000) (ψ := 181581/500000) 266 249
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t357 : ((11332892571/1250000000000 : ℚ) : ℝ) ≤ stT266 357 := by
  have hc : ((171303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).1
  have hw2 : ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66157/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11332892571/1250000000000 : ℚ) : ℝ)
      = ((66157/1250000 : ℚ) : ℝ) * ((171303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c358 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((793329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1636347/10000000) (δ := 6657/500000000) (ψ := 181581/500000) 266 249
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t358 : ((104815160991/2500000000000 : ℚ) : ℝ) ≤ stT266 358 := by
  have hc : ((793279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).1
  have hw2 : ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((132129/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104815160991/2500000000000 : ℚ) : ℝ)
      = ((132129/2500000 : ℚ) : ℝ) * ((793279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c359 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((996179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 54651/2500000) (δ := 6657/500000000) (ψ := 181581/500000) 266 249
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t359 : ((525735967491/10000000000000 : ℚ) : ℝ) ≤ stT266 359 := by
  have hc : ((996129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((525735967491/10000000000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((996129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c360 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((676811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 413687/2000000) (δ := 13489/1000000000) (ψ := 181581/500000) 266 249
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t360 : ((178342089003/5000000000000 : ℚ) : ℝ) ≤ stT266 360 := by
  have hc : ((676761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).1
  have hw2 : ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178342089003/5000000000000 : ℚ) : ℝ)
      = ((263523/5000000 : ℚ) : ℝ) * ((676761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c361 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((1113/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1956539/5000000) (δ := 6657/500000000) (ψ := 181581/500000) 266 249
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t361 : ((116105089/400000000000 : ℚ) : ℝ) ≤ stT266 361 := by
  have hc : ((1103/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116105089/400000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((1103/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c362 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-667071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1438167/2500000) (δ := 13489/1000000000) (ψ := 181581/500000) 266 249
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t362 : ((-350631459269/10000000000000 : ℚ) : ℝ) ≤ stT266 362 := by
  have hc : ((-667121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).2
  have h0 : (0:ℝ) ≤ ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-350631459269/10000000000000 : ℚ) : ℝ)
      = ((525589/10000000 : ℚ) : ℝ) * ((-667121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c363 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-994309/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7587137/10000000) (δ := 13489/1000000000) (ψ := 181581/500000) 266 249
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t363 : ((-8154738159/156250000000 : ℚ) : ℝ) ≤ stT266 363 := by
  have hc : ((-994359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8154738159/156250000000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-994359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c364 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-810947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1572853/2500000) (δ := 13407/1000000000) (ψ := 181581/500000) 266 250
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t364 : ((-425078400571/10000000000000 : ℚ) : ℝ) ≤ stT266 364 := by
  have hc : ((-810997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-425078400571/10000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-810997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c365 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-107161/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -558373/1250000) (δ := 3349/250000000) (ψ := 181581/500000) 266 250
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t365 : ((-876620701/78125000000 : ℚ) : ℝ) ≤ stT266 365 := by
  have hc : ((-53593/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-876620701/78125000000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-53593/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c366 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((489729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -330943/1250000) (δ := 3349/250000000) (ψ := 181581/500000) 266 250
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t366 : ((63989782683/2500000000000 : ℚ) : ℝ) ≤ stT266 366 := by
  have hc : ((489679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).1
  have hw2 : ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((130677/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63989782683/2500000000000 : ℚ) : ℝ)
      = ((130677/2500000 : ℚ) : ℝ) * ((489679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c367 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((944989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -208273/2500000) (δ := 13407/1000000000) (ψ := 181581/500000) 266 250
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t367 : ((98650686661/2000000000000 : ℚ) : ℝ) ≤ stT266 367 := by
  have hc : ((944939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).1
  have hw2 : ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((104399/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98650686661/2000000000000 : ℚ) : ℝ)
      = ((104399/2000000 : ℚ) : ℝ) * ((944939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c368 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((92469/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24411/250000) (δ := 3349/250000000) (ψ := 181581/500000) 266 250
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t368 : ((1506255897/31250000000 : ℚ) : ℝ) ≤ stT266 368 := by
  have hc : ((5779/6250 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1506255897/31250000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((5779/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c369 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((442493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55621/200000) (δ := 13407/1000000000) (ψ := 181581/500000) 266 250
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t369 : ((230326534497/10000000000000 : ℚ) : ℝ) ≤ stT266 369 := by
  have hc : ((442443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230326534497/10000000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((442443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c370 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-51711/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2290403/5000000) (δ := 13407/1000000000) (ψ := 181581/500000) 266 250
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t370 : ((-6722126649/500000000000 : ℚ) : ℝ) ≤ stT266 370 := by
  have hc : ((-51721/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).2
  have h0 : (0:ℝ) ≤ ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6722126649/500000000000 : ℚ) : ℝ)
      = ((129969/2500000 : ℚ) : ℝ) * ((-51721/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c371 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-207549/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6375641/10000000) (δ := 13407/1000000000) (ψ := 181581/500000) 266 250
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t371 : ((-8620859341/200000000000 : ℚ) : ℝ) ≤ stT266 371 := by
  have hc : ((-415123/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8620859341/200000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-415123/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c372 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-992237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -301691/400000) (δ := 1663/125000000) (ψ := 181581/500000) 266 251
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t372 : ((-128619248653/2500000000000 : ℚ) : ℝ) ≤ stT266 372 := by
  have hc : ((-992287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128619248653/2500000000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-992287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c373 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-334183/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -719627/1250000) (δ := 1663/125000000) (ψ := 181581/500000) 266 251
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t373 : ((-1351926191/39062500000 : ℚ) : ℝ) ≤ stT266 373 := by
  have hc : ((-10444/15625 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).2
  have h0 : (0:ℝ) ≤ ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1351926191/39062500000 : ℚ) : ℝ)
      = ((517781/10000000 : ℚ) : ℝ) * ((-10444/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c374 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-19847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -994153/2500000) (δ := 13499/1000000000) (ψ := 181581/500000) 266 251
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t374 : ((-321515623/312500000000 : ℚ) : ℝ) ≤ stT266 374 := by
  have hc : ((-19897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-321515623/312500000000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-19897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c375 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((127377/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1100431/5000000) (δ := 1663/125000000) (ψ := 181581/500000) 266 251
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t375 : ((65771936699/2000000000000 : ℚ) : ℝ) ≤ stT266 375 := by
  have hc : ((127367/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65771936699/2000000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((127367/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c376 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((985251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -429901/10000000) (δ := 13499/1000000000) (ψ := 181581/500000) 266 251
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t376 : ((50807800771/1000000000000 : ℚ) : ℝ) ≤ stT266 376 := by
  have hc : ((985201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50807800771/1000000000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((985201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c377 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((172101/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1336339/10000000) (δ := 13499/1000000000) (ψ := 181581/500000) 266 251
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t377 : ((44315669683/1000000000000 : ℚ) : ℝ) ≤ stT266 377 := by
  have hc : ((172091/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44315669683/1000000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((172091/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c378 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((162791/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 774481/2500000) (δ := 13499/1000000000) (ψ := 181581/500000) 266 251
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t378 : ((5232357219/312500000000 : ℚ) : ℝ) ≤ stT266 378 := by
  have hc : ((81383/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5232357219/312500000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((81383/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c379 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-90677/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4854921/10000000) (δ := 1663/125000000) (ψ := 181581/500000) 266 251
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t379 : ((-46584112707/2500000000000 : ℚ) : ℝ) ≤ stT266 379 := by
  have hc : ((-181379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46584112707/2500000000000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-181379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c380 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-439099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1651799/2500000) (δ := 1663/125000000) (ψ := 181581/500000) 266 251
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t380 : ((-5631655519/125000000000 : ℚ) : ℝ) ≤ stT266 380 := by
  have hc : ((-109781/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5631655519/125000000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-109781/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c381 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-195999/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7353081/10000000) (δ := 837/62500000) (ψ := 181581/500000) 266 252
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t381 : ((-25104636711/500000000000 : ℚ) : ℝ) ≤ stT266 381 := by
  have hc : ((-196009/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25104636711/500000000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-196009/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c382 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-155867/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1402479/2500000) (δ := 13411/1000000000) (ψ := 181581/500000) 266 252
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t382 : ((-31901986711/1000000000000 : ℚ) : ℝ) ≤ stT266 382 := by
  have hc : ((-311759/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).2
  have h0 : (0:ℝ) ≤ ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31901986711/1000000000000 : ℚ) : ℝ)
      = ((102329/2000000 : ℚ) : ℝ) * ((-311759/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c383 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((2779/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3871407/10000000) (δ := 837/62500000) (ψ := 181581/500000) 266 252
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t383 : ((5534409/4882812500 : ℚ) : ℝ) ≤ stT266 383 := by
  have hc : ((11091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5534409/4882812500 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((11091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c384 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((656263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2137353/10000000) (δ := 837/62500000) (ψ := 181581/500000) 266 252
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t384 : ((33487205603/1000000000000 : ℚ) : ℝ) ≤ stT266 384 := by
  have hc : ((656213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).1
  have hw2 : ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33487205603/1000000000000 : ℚ) : ℝ)
      = ((51031/1000000 : ℚ) : ℝ) * ((656213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c385 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((246681/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -407821/10000000) (δ := 837/62500000) (ψ := 181581/500000) 266 252
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t385 : ((251427722039/5000000000000 : ℚ) : ℝ) ≤ stT266 385 := by
  have hc : ((493337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((251427722039/5000000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((493337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c386 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((432191/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1317189/10000000) (δ := 837/62500000) (ψ := 181581/500000) 266 252
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t386 : ((54991610919/1250000000000 : ℚ) : ℝ) ≤ stT266 386 := by
  have hc : ((216083/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).1
  have hw2 : ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((254493/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54991610919/1250000000000 : ℚ) : ℝ)
      = ((254493/5000000 : ℚ) : ℝ) * ((216083/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c387 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((69649/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 189859/625000) (δ := 13411/1000000000) (ψ := 181581/500000) 266 252
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t387 : ((4424931699/250000000000 : ℚ) : ℝ) ≤ stT266 387 := by
  have hc : ((69639/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).1
  have hw2 : ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((63541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4424931699/250000000000 : ℚ) : ℝ)
      = ((63541/1250000 : ℚ) : ℝ) * ((69639/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c388 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-324769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4753909/10000000) (δ := 837/62500000) (ψ := 181581/500000) 266 252
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t388 : ((-82451080503/5000000000000 : ℚ) : ℝ) ≤ stT266 388 := by
  have hc : ((-324819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).2
  have h0 : (0:ℝ) ≤ ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82451080503/5000000000000 : ℚ) : ℝ)
      = ((253837/5000000 : ℚ) : ℝ) * ((-324819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c389 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-849719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6465619/10000000) (δ := 837/62500000) (ψ := 181581/500000) 266 252
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t389 : ((-430850728149/10000000000000 : ℚ) : ℝ) ≤ stT266 389 := by
  have hc : ((-849769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-430850728149/10000000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-849769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c390 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-15498/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7535023/10000000) (δ := 6659/500000000) (ψ := 181581/500000) 266 253
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t390 : ((-25113977157/500000000000 : ℚ) : ℝ) ≤ stT266 390 := by
  have hc : ((-495961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).2
  have h0 : (0:ℝ) ≤ ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25113977157/500000000000 : ℚ) : ℝ)
      = ((50637/1000000 : ℚ) : ℝ) * ((-495961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c391 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-690399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5832091/10000000) (δ := 6659/500000000) (ψ := 181581/500000) 266 253
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t391 : ((-174587624589/5000000000000 : ℚ) : ℝ) ≤ stT266 391 := by
  have hc : ((-690449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).2
  have h0 : (0:ℝ) ≤ ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174587624589/5000000000000 : ℚ) : ℝ)
      = ((252861/5000000 : ℚ) : ℝ) * ((-690449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c392 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-82503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2066741/5000000) (δ := 2697/200000000) (ψ := 181581/500000) 266 253
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t392 : ((-41695621581/10000000000000 : ℚ) : ℝ) ≤ stT266 392 := by
  have hc : ((-82553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).2
  have h0 : (0:ℝ) ≤ ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41695621581/10000000000000 : ℚ) : ℝ)
      = ((505077/10000000 : ℚ) : ℝ) * ((-82553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c393 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((560607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -487839/2000000) (δ := 2697/200000000) (ψ := 181581/500000) 266 253
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t393 : ((282763449181/10000000000000 : ℚ) : ℝ) ≤ stT266 393 := by
  have hc : ((560557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((282763449181/10000000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((560557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c394 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((955427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74923/1000000) (δ := 6659/500000000) (ψ := 181581/500000) 266 253
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t394 : ((30081955599/625000000000 : ℚ) : ℝ) ≤ stT266 394 := by
  have hc : ((955377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).1
  have hw2 : ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31487/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30081955599/625000000000 : ℚ) : ℝ)
      = ((31487/625000 : ℚ) : ℝ) * ((955377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c395 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((930667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 234103/2500000) (δ := 6659/500000000) (ψ := 181581/500000) 266 253
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t395 : ((234121833009/5000000000000 : ℚ) : ℝ) ≤ stT266 395 := by
  have hc : ((930617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).1
  have hw2 : ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234121833009/5000000000000 : ℚ) : ℝ)
      = ((251577/5000000 : ℚ) : ℝ) * ((930617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c396 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((100009/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 327233/1250000) (δ := 2697/200000000) (ψ := 181581/500000) 266 253
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t396 : ((25125648741/1000000000000 : ℚ) : ℝ) ≤ stT266 396 := by
  have hc : ((99999/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).1
  have hw2 : ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251259/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25125648741/1000000000000 : ℚ) : ℝ)
      = ((251259/5000000 : ℚ) : ℝ) * ((99999/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c397 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-14667/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2147497/5000000) (δ := 2697/200000000) (ψ := 181581/500000) 266 253
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t397 : ((-230114731/31250000000 : ℚ) : ℝ) ≤ stT266 397 := by
  have hc : ((-917/6250 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230114731/31250000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-917/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c398 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-45543/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5968001/10000000) (δ := 2697/200000000) (ψ := 181581/500000) 266 253
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t398 : ((-36528356619/1000000000000 : ℚ) : ℝ) ≤ stT266 398 := by
  have hc : ((-364369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).2
  have h0 : (0:ℝ) ≤ ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36528356619/1000000000000 : ℚ) : ℝ)
      = ((100251/2000000 : ℚ) : ℝ) * ((-364369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c399 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-996227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 477297/625000) (δ := 2697/200000000) (ψ := 181581/500000) 266 253
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t399 : ((-498763165679/10000000000000 : ℚ) : ℝ) ≤ stT266 399 := by
  have hc : ((-996277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).2
  have h0 : (0:ℝ) ≤ ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-498763165679/10000000000000 : ℚ) : ℝ)
      = ((500627/10000000 : ℚ) : ℝ) * ((-996277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c400 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-837047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6406649/10000000) (δ := 537/40000000) (ψ := 181581/500000) 266 254
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t400 : ((-418549337097/10000000000000 : ℚ) : ℝ) ≤ stT266 400 := by
  have hc : ((-837097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-418549337097/10000000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-837097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c401 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-64371/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4746211/10000000) (δ := 6689/500000000) (ψ := 181581/500000) 266 254
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t401 : ((-32150390637/2000000000000 : ℚ) : ℝ) ≤ stT266 401 := by
  have hc : ((-64381/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).2
  have h0 : (0:ℝ) ≤ ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32150390637/2000000000000 : ℚ) : ℝ)
      = ((499377/10000000 : ℚ) : ℝ) * ((-64381/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c402 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((328591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1544981/5000000) (δ := 6689/500000000) (ψ := 181581/500000) 266 254
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t402 : ((81930568957/5000000000000 : ℚ) : ℝ) ≤ stT266 402 := by
  have hc : ((328541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).1
  have hw2 : ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((249377/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81930568957/5000000000000 : ℚ) : ℝ)
      = ((249377/5000000 : ℚ) : ℝ) * ((328541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c403 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((419567/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1437769/10000000) (δ := 537/40000000) (ψ := 181581/500000) 266 254
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t403 : ((20898855417/500000000000 : ℚ) : ℝ) ≤ stT266 403 := by
  have hc : ((209771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).1
  have hw2 : ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((99627/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20898855417/500000000000 : ℚ) : ℝ)
      = ((99627/2000000 : ℚ) : ℝ) * ((209771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c404 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((62279/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2103/100000) (δ := 6689/500000000) (ψ := 181581/500000) 266 254
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t404 : ((123933475113/2500000000000 : ℚ) : ℝ) ≤ stT266 404 := by
  have hc : ((498207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).1
  have hw2 : ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((248759/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123933475113/2500000000000 : ℚ) : ℝ)
      = ((248759/5000000 : ℚ) : ℝ) * ((498207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c405 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((92163/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1854313/10000000) (δ := 6689/500000000) (ψ := 181581/500000) 266 254
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t405 : ((183171862181/5000000000000 : ℚ) : ℝ) ≤ stT266 405 := by
  have hc : ((368627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183171862181/5000000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((368627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c406 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((6889/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 349427/1000000) (δ := 537/40000000) (ψ := 181581/500000) 266 254
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t406 : ((3417956117/400000000000 : ℚ) : ℝ) ≤ stT266 406 := by
  have hc : ((6887/40000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3417956117/400000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((6887/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c407 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-462907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 513017/1000000) (δ := 537/40000000) (ψ := 181581/500000) 266 254
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t407 : ((-114739725837/5000000000000 : ℚ) : ℝ) ≤ stT266 407 := by
  have hc : ((-462957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).2
  have h0 : (0:ℝ) ≤ ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114739725837/5000000000000 : ℚ) : ℝ)
      = ((247841/5000000 : ℚ) : ℝ) * ((-462957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c408 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-906127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42263/62500) (δ := 537/40000000) (ψ := 181581/500000) 266 254
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t408 : ((-224312336049/5000000000000 : ℚ) : ℝ) ≤ stT266 408 := by
  have hc : ((-906177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).2
  have h0 : (0:ℝ) ≤ ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224312336049/5000000000000 : ℚ) : ℝ)
      = ((247537/5000000 : ℚ) : ℝ) * ((-906177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c409 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-977103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1829491/2500000) (δ := 13471/1000000000) (ψ := 181581/500000) 266 255
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t409 : ((-483171866757/10000000000000 : ℚ) : ℝ) ≤ stT266 409 := by
  have hc : ((-977153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).2
  have h0 : (0:ℝ) ≤ ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-483171866757/10000000000000 : ℚ) : ℝ)
      = ((494469/10000000 : ℚ) : ℝ) * ((-977153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c410 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-649417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2847017/5000000) (δ := 13471/1000000000) (ψ := 181581/500000) 266 255
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t410 : ((-64149803991/2000000000000 : ℚ) : ℝ) ≤ stT266 410 := by
  have hc : ((-649467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).2
  have h0 : (0:ℝ) ≤ ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64149803991/2000000000000 : ℚ) : ℝ)
      = ((98773/2000000 : ℚ) : ℝ) * ((-649467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c411 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-58781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4074027/10000000) (δ := 3333/250000000) (ψ := 181581/500000) 266 255
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t411 : ((-1813700899/625000000000 : ℚ) : ℝ) ≤ stT266 411 := by
  have hc : ((-58831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1813700899/625000000000 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-58831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c412 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((277179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2458011/10000000) (δ := 13471/1000000000) (ψ := 181581/500000) 266 255
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t412 : ((8533987391/312500000000 : ℚ) : ℝ) ≤ stT266 412 := by
  have hc : ((138577/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).1
  have hw2 : ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61583/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8533987391/312500000000 : ℚ) : ℝ)
      = ((61583/1250000 : ℚ) : ℝ) * ((138577/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c413 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((471649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -422959/5000000) (δ := 13471/1000000000) (ψ := 181581/500000) 266 255
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t413 : ((29008825851/625000000000 : ℚ) : ℝ) ≤ stT266 413 := by
  have hc : ((58953/62500 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).1
  have hw2 : ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((492067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29008825851/625000000000 : ℚ) : ℝ)
      = ((492067/10000000 : ℚ) : ℝ) * ((58953/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c414 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((953869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 381159/5000000) (δ := 13471/1000000000) (ψ := 181581/500000) 266 255
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t414 : ((468776285387/10000000000000 : ℚ) : ℝ) ≤ stT266 414 := by
  have hc : ((953819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).1
  have hw2 : ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((491473/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((468776285387/10000000000000 : ℚ) : ℝ)
      = ((491473/10000000 : ℚ) : ℝ) * ((953819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c415 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((584381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2366697/10000000) (δ := 13471/1000000000) (ψ := 181581/500000) 266 255
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t415 : ((448181877/15625000000 : ℚ) : ℝ) ≤ stT266 415 := by
  have hc : ((584331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).1
  have hw2 : ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((767/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((448181877/15625000000 : ℚ) : ℝ)
      = ((767/15625 : ℚ) : ℝ) * ((584331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c416 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-251/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3967153/10000000) (δ := 3333/250000000) (ψ := 181581/500000) 266 255
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t416 : ((-3950274587/5000000000000 : ℚ) : ℝ) ≤ stT266 416 := by
  have hc : ((-8057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3950274587/5000000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-8057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c417 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-304473/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2781909/5000000) (δ := 3333/250000000) (ψ := 181581/500000) 266 255
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t417 : ((-74556792047/2500000000000 : ℚ) : ℝ) ≤ stT266 417 := by
  have hc : ((-152249/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74556792047/2500000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-152249/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c418 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-961347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3578313/5000000) (δ := 3333/250000000) (ψ := 181581/500000) 266 255
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t418 : ((-117558663763/2500000000000 : ℚ) : ℝ) ≤ stT266 418 := by
  have hc : ((-961397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).2
  have h0 : (0:ℝ) ≤ ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117558663763/2500000000000 : ℚ) : ℝ)
      = ((122279/2500000 : ℚ) : ℝ) * ((-961397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c419 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-937067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87029/125000) (δ := 3341/250000000) (ψ := 181581/500000) 266 256
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t419 : ((-114452910561/2500000000000 : ℚ) : ℝ) ≤ stT266 419 := by
  have hc : ((-937117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).2
  have h0 : (0:ℝ) ≤ ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114452910561/2500000000000 : ℚ) : ℝ)
      = ((122133/2500000 : ℚ) : ℝ) * ((-937117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c420 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-274029/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5377093/10000000) (δ := 3341/250000000) (ψ := 181581/500000) 266 256
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t420 : ((-66862461677/2500000000000 : ℚ) : ℝ) ≤ stT266 420 := by
  have hc : ((-137027/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).2
  have h0 : (0:ℝ) ≤ ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66862461677/2500000000000 : ℚ) : ℝ)
      = ((487951/10000000 : ℚ) : ℝ) * ((-137027/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c421 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((5251/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -474457/1250000) (δ := 13439/1000000000) (ψ := 181581/500000) 266 256
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t421 : ((127837151/50000000000 : ℚ) : ℝ) ≤ stT266 421 := by
  have hc : ((2623/50000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127837151/50000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((2623/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c422 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((631603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -277243/1250000) (δ := 3341/250000000) (ψ := 181581/500000) 266 256
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t422 : ((38429368497/1250000000000 : ℚ) : ℝ) ≤ stT266 422 := by
  have hc : ((631553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38429368497/1250000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((631553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c423 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((483501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -322011/5000000) (δ := 3341/250000000) (ψ := 181581/500000) 266 256
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t423 : ((7346055213/156250000000 : ℚ) : ℝ) ≤ stT266 423 := by
  have hc : ((120869/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7346055213/156250000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((120869/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c424 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((932147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 926243/10000000) (δ := 13439/1000000000) (ψ := 181581/500000) 266 256
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t424 : ((226332725637/5000000000000 : ℚ) : ℝ) ≤ stT266 424 := by
  have hc : ((932097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).1
  have hw2 : ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((242821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226332725637/5000000000000 : ℚ) : ℝ)
      = ((242821/5000000 : ℚ) : ℝ) * ((932097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c425 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((542729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2492783/10000000) (δ := 3341/250000000) (ψ := 181581/500000) 266 256
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t425 : ((263237845209/10000000000000 : ℚ) : ℝ) ≤ stT266 425 := by
  have hc : ((542679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).1
  have hw2 : ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((485071/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((263237845209/10000000000000 : ℚ) : ℝ)
      = ((485071/10000000 : ℚ) : ℝ) * ((542679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c426 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-51447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2027833/5000000) (δ := 3341/250000000) (ψ := 181581/500000) 266 256
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t426 : ((-12475199747/5000000000000 : ℚ) : ℝ) ≤ stT266 426 := by
  have hc : ((-51497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12475199747/5000000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-51497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c427 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-625023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1403723/2500000) (δ := 13439/1000000000) (ψ := 181581/500000) 266 256
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t427 : ((-151247038591/5000000000000 : ℚ) : ℝ) ≤ stT266 427 := by
  have hc : ((-625073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151247038591/5000000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-625073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c428 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-962849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7170393/10000000) (δ := 3341/250000000) (ψ := 181581/500000) 266 256
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t428 : ((-465435526731/10000000000000 : ℚ) : ℝ) ≤ stT266 428 := by
  have hc : ((-962899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-465435526731/10000000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-962899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c429 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-235069/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6985593/10000000) (δ := 13347/1000000000) (ψ := 181581/500000) 266 257
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t429 : ((-45399409443/1000000000000 : ℚ) : ℝ) ≤ stT266 429 := by
  have hc : ((-470163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45399409443/1000000000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-470163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c430 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-568033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2718637/5000000) (δ := 841/62500000) (ψ := 181581/500000) 266 257
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t430 : ((-273954050169/10000000000000 : ℚ) : ℝ) ≤ stT266 430 := by
  have hc : ((-568083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-273954050169/10000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-568083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c431 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((13751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -973153/2500000) (δ := 841/62500000) (ψ := 181581/500000) 266 257
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t431 : ((6599538783/10000000000000 : ℚ) : ℝ) ≤ stT266 431 := by
  have hc : ((13701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6599538783/10000000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((13701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c432 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((9208/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1175737/5000000) (δ := 13347/1000000000) (ψ := 181581/500000) 266 257
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t432 : ((1134034719/40000000000 : ℚ) : ℝ) ≤ stT266 432 := by
  have hc : ((294631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1134034719/40000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((294631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c433 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((947477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -813861/10000000) (δ := 13347/1000000000) (ψ := 181581/500000) 266 257
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t433 : ((455304045963/10000000000000 : ℚ) : ℝ) ≤ stT266 433 := by
  have hc : ((947427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((455304045963/10000000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((947427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c434 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((239699/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 720161/10000000) (δ := 13347/1000000000) (ψ := 181581/500000) 266 257
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t434 : ((46021246119/1000000000000 : ℚ) : ℝ) ≤ stT266 434 := by
  have hc : ((479373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46021246119/1000000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((479373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c435 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((155351/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1125329/5000000) (δ := 841/62500000) (ψ := 181581/500000) 266 257
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t435 : ((148958126451/5000000000000 : ℚ) : ℝ) ≤ stT266 435 := by
  have hc : ((310677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148958126451/5000000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((310677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c436 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((14927/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3777631/10000000) (δ := 841/62500000) (ψ := 181581/500000) 266 257
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t436 : ((14285495877/5000000000000 : ℚ) : ℝ) ≤ stT266 436 := by
  have hc : ((29829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14285495877/5000000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((29829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c437 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-522377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 132527/250000) (δ := 13347/1000000000) (ψ := 181581/500000) 266 257
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t437 : ((-49982158371/2000000000000 : ℚ) : ℝ) ≤ stT266 437 := by
  have hc : ((-522427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).2
  have h0 : (0:ℝ) ≤ ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49982158371/2000000000000 : ℚ) : ℝ)
      = ((95673/2000000 : ℚ) : ℝ) * ((-522427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c438 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-457933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6821137/10000000) (δ := 13347/1000000000) (ψ := 181581/500000) 266 257
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t438 : ((-109410516801/2500000000000 : ℚ) : ℝ) ≤ stT266 438 := by
  have hc : ((-228979/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109410516801/2500000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-228979/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c439 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-490671/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3685147/5000000) (δ := 13349/1000000000) (ψ := 181581/500000) 266 258
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t439 : ((-14637277669/312500000000 : ℚ) : ℝ) ≤ stT266 439 := by
  have hc : ((-61337/62500 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14637277669/312500000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-61337/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c440 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-139527/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5857219/10000000) (δ := 6727/500000000) (ψ := 181581/500000) 266 258
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t440 : ((-16630438271/500000000000 : ℚ) : ℝ) ≤ stT266 440 := by
  have hc : ((-139537/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16630438271/500000000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-139537/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c441 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-41863/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4347603/10000000) (δ := 13349/1000000000) (ψ := 181581/500000) 266 258
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t441 : ((-39881472441/5000000000000 : ℚ) : ℝ) ≤ stT266 441 := by
  have hc : ((-83751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39881472441/5000000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-83751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c442 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((210363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1420689/5000000) (δ := 13349/1000000000) (ψ := 181581/500000) 266 258
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t442 : ((50023740019/2500000000000 : ℚ) : ℝ) ≤ stT266 442 := by
  have hc : ((105169/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).1
  have hw2 : ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((475651/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50023740019/2500000000000 : ℚ) : ℝ)
      = ((475651/10000000 : ℚ) : ℝ) * ((105169/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c443 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((107507/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83659/625000) (δ := 6727/500000000) (ψ := 181581/500000) 266 258
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t443 : ((102150222671/2500000000000 : ℚ) : ℝ) ≤ stT266 443 := by
  have hc : ((430003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).1
  have hw2 : ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237557/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102150222671/2500000000000 : ℚ) : ℝ)
      = ((237557/5000000 : ℚ) : ℝ) * ((430003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c444 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((99793/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80449/5000000) (δ := 6727/500000000) (ψ := 181581/500000) 266 258
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t444 : ((5919648683/125000000000 : ℚ) : ℝ) ≤ stT266 444 := by
  have hc : ((24947/25000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).1
  have hw2 : ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237289/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5919648683/125000000000 : ℚ) : ℝ)
      = ((237289/5000000 : ℚ) : ℝ) * ((24947/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c445 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((157657/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 414237/2500000) (δ := 13349/1000000000) (ψ := 181581/500000) 266 258
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t445 : ((14946354423/400000000000 : ℚ) : ℝ) ≤ stT266 445 := by
  have hc : ((157647/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).1
  have hw2 : ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94809/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14946354423/400000000000 : ℚ) : ℝ)
      = ((94809/2000000 : ℚ) : ℝ) * ((157647/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c446 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((305941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1574837/5000000) (δ := 6727/500000000) (ψ := 181581/500000) 266 258
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t446 : ((144843365083/10000000000000 : ℚ) : ℝ) ≤ stT266 446 := by
  have hc : ((305891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144843365083/10000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((305891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c447 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-70243/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 144969/312500) (δ := 6727/500000000) (ψ := 181581/500000) 266 258
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t447 : ((-8307431853/625000000000 : ℚ) : ℝ) ≤ stT266 447 := by
  have hc : ((-140511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).2
  have h0 : (0:ℝ) ≤ ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8307431853/625000000000 : ℚ) : ℝ)
      = ((59123/1250000 : ℚ) : ℝ) * ((-140511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c448 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-192563/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6125083/10000000) (δ := 13349/1000000000) (ψ := 181581/500000) 266 258
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t448 : ((-22745862607/625000000000 : ℚ) : ℝ) ≤ stT266 448 := by
  have hc : ((-385151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).2
  have h0 : (0:ℝ) ≤ ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22745862607/625000000000 : ℚ) : ℝ)
      = ((59057/1250000 : ℚ) : ℝ) * ((-385151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c449 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-497577/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7607767/10000000) (δ := 13349/1000000000) (ψ := 181581/500000) 266 258
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t449 : ((-11741665593/250000000000 : ℚ) : ℝ) ≤ stT266 449 := by
  have hc : ((-248801/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).2
  have h0 : (0:ℝ) ≤ ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11741665593/250000000000 : ℚ) : ℝ)
      = ((47193/1000000 : ℚ) : ℝ) * ((-248801/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c450 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-440391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6620771/10000000) (δ := 6721/500000000) (ψ := 181581/500000) 266 259
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t450 : ((-1297589403/31250000000 : ℚ) : ℝ) ≤ stT266 450 := by
  have hc : ((-13763/15625 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).2
  have h0 : (0:ℝ) ≤ ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1297589403/31250000000 : ℚ) : ℝ)
      = ((94281/2000000 : ℚ) : ℝ) * ((-13763/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c451 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-468017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1286151/2500000) (δ := 6721/500000000) (ψ := 181581/500000) 266 259
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t451 : ((-110202162547/5000000000000 : ℚ) : ℝ) ≤ stT266 451 := by
  have hc : ((-468067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110202162547/5000000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-468067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c452 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((50957/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1835881/5000000) (δ := 6721/500000000) (ψ := 181581/500000) 266 259
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t452 : ((149727347/31250000000 : ℚ) : ℝ) ≤ stT266 452 := by
  have hc : ((12733/125000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).1
  have hw2 : ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149727347/31250000000 : ℚ) : ℝ)
      = ((11759/250000 : ℚ) : ℝ) * ((12733/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c453 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((1273/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17204/78125) (δ := 6721/500000000) (ψ := 181581/500000) 266 259
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t453 : ((74757417/2500000000 : ℚ) : ℝ) ≤ stT266 453 := by
  have hc : ((12729/20000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).1
  have hw2 : ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5873/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74757417/2500000000 : ℚ) : ℝ)
      = ((5873/125000 : ℚ) : ℝ) * ((12729/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c454 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((957001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -735787/10000000) (δ := 6721/500000000) (ψ := 181581/500000) 266 259
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t454 : ((449119114173/10000000000000 : ℚ) : ℝ) ≤ stT266 454 := by
  have hc : ((956951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).1
  have hw2 : ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((469323/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((449119114173/10000000000000 : ℚ) : ℝ)
      = ((469323/10000000 : ℚ) : ℝ) * ((956951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c455 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((957967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 727413/10000000) (δ := 13361/1000000000) (ψ := 181581/500000) 266 259
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t455 : ((449078195019/10000000000000 : ℚ) : ℝ) ≤ stT266 455 := by
  have hc : ((957917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).1
  have hw2 : ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((468807/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((449078195019/10000000000000 : ℚ) : ℝ)
      = ((468807/10000000 : ℚ) : ℝ) * ((957917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c456 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((320521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1093677/5000000) (δ := 13361/1000000000) (ψ := 181581/500000) 266 259
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t456 : ((2345089263/78125000000 : ℚ) : ℝ) ≤ stT266 456 := by
  have hc : ((20031/31250 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).1
  have hw2 : ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117073/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2345089263/78125000000 : ℚ) : ℝ)
      = ((117073/2500000 : ℚ) : ℝ) * ((20031/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c457 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((5647/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 911009/2500000) (δ := 6721/500000000) (ψ := 181581/500000) 266 259
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t457 : ((264038421/50000000000 : ℚ) : ℝ) ≤ stT266 457 := by
  have hc : ((11289/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).1
  have hw2 : ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((23389/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((264038421/50000000000 : ℚ) : ℝ)
      = ((23389/500000 : ℚ) : ℝ) * ((11289/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c458 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-451317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5097593/10000000) (δ := 6721/500000000) (ψ := 181581/500000) 266 259
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t458 : ((-21091025809/1000000000000 : ℚ) : ℝ) ≤ stT266 458 := by
  have hc : ((-451367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).2
  have h0 : (0:ℝ) ≤ ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21091025809/1000000000000 : ℚ) : ℝ)
      = ((46727/1000000 : ℚ) : ℝ) * ((-451367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c459 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-866633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 261921/400000) (δ := 13361/1000000000) (ψ := 181581/500000) 266 259
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t459 : ((-404533823763/10000000000000 : ℚ) : ℝ) ≤ stT266 459 := by
  have hc : ((-866683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).2
  have h0 : (0:ℝ) ≤ ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-404533823763/10000000000000 : ℚ) : ℝ)
      = ((466761/10000000 : ℚ) : ℝ) * ((-866683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c460 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-199681/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1542553/2000000) (δ := 3367/250000000) (ψ := 181581/500000) 266 260
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t460 : ((-93106527823/2000000000000 : ℚ) : ℝ) ≤ stT266 460 := by
  have hc : ((-199691/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).2
  have h0 : (0:ℝ) ≤ ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93106527823/2000000000000 : ℚ) : ℝ)
      = ((466253/10000000 : ℚ) : ℝ) * ((-199691/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c461 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-402793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6268651/10000000) (δ := 3367/250000000) (ψ := 181581/500000) 266 260
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t461 : ((-93805637523/2500000000000 : ℚ) : ℝ) ≤ stT266 461 := by
  have hc : ((-201409/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).2
  have h0 : (0:ℝ) ≤ ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93805637523/2500000000000 : ℚ) : ℝ)
      = ((465747/10000000 : ℚ) : ℝ) * ((-201409/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c462 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-352551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4827729/10000000) (δ := 3367/250000000) (ψ := 181581/500000) 266 260
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t462 : ((-164045147043/10000000000000 : ℚ) : ℝ) ≤ stT266 462 := by
  have hc : ((-352601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).2
  have h0 : (0:ℝ) ≤ ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164045147043/10000000000000 : ℚ) : ℝ)
      = ((465243/10000000 : ℚ) : ℝ) * ((-352601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c463 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((213201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1694933/5000000) (δ := 3367/250000000) (ψ := 181581/500000) 266 260
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t463 : ((99059582589/10000000000000 : ℚ) : ℝ) ≤ stT266 463 := by
  have hc : ((213151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99059582589/10000000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((213151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c464 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((709469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1955129/10000000) (δ := 2667/200000000) (ψ := 181581/500000) 266 260
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t464 : ((164669628861/5000000000000 : ℚ) : ℝ) ≤ stT266 464 := by
  have hc : ((709419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164669628861/5000000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((709419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c465 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((12227/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10469/200000) (δ := 3367/250000000) (ψ := 181581/500000) 266 260
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t465 : ((22679338759/500000000000 : ℚ) : ℝ) ≤ stT266 465 := by
  have hc : ((97811/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22679338759/500000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((97811/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c466 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((116897/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 905103/10000000) (δ := 3367/250000000) (ψ := 181581/500000) 266 260
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t466 : ((216594351683/5000000000000 : ℚ) : ℝ) ≤ stT266 466 := by
  have hc : ((467563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216594351683/5000000000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((467563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c467 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((298019/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2330597/10000000) (δ := 3367/250000000) (ψ := 181581/500000) 266 260
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t467 : ((8618433471/312500000000 : ℚ) : ℝ) ≤ stT266 467 := by
  have hc : ((148997/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).1
  have hw2 : ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57843/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8618433471/312500000000 : ℚ) : ℝ)
      = ((57843/1250000 : ℚ) : ℝ) * ((148997/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c468 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((69527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 469129/1250000) (δ := 3367/250000000) (ψ := 181581/500000) 266 260
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t468 : ((128462973/40000000000 : ℚ) : ℝ) ≤ stT266 468 := by
  have hc : ((69477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).1
  have hw2 : ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128462973/40000000000 : ℚ) : ℝ)
      = ((1849/40000 : ℚ) : ℝ) * ((69477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c469 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-477839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2586237/5000000) (δ := 2667/200000000) (ψ := 181581/500000) 266 260
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t469 : ((-110334534431/5000000000000 : ℚ) : ℝ) ≤ stT266 469 := by
  have hc : ((-477889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110334534431/5000000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-477889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c470 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-437333/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3294429/5000000) (δ := 3367/250000000) (ψ := 181581/500000) 266 260
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t470 : ((-50434593807/1250000000000 : ℚ) : ℝ) ≤ stT266 470 := by
  have hc : ((-218679/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50434593807/1250000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-218679/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c471 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-499121/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1541143/2000000) (δ := 3357/250000000) (ψ := 181581/500000) 266 261
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t471 : ((-14374656081/312500000000 : ℚ) : ℝ) ≤ stT266 471 := by
  have hc : ((-249573/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14374656081/312500000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-249573/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c472 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-40593/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1573829/2500000) (δ := 107/8000000) (ψ := 181581/500000) 266 261
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t472 : ((-72990709/1953125000 : ℚ) : ℝ) ≤ stT266 472 := by
  have hc : ((-81191/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).2
  have h0 : (0:ℝ) ≤ ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72990709/1953125000 : ℚ) : ℝ)
      = ((3596/78125 : ℚ) : ℝ) * ((-81191/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c473 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-374973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -488791/1000000) (δ := 107/8000000) (ψ := 181581/500000) 266 261
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t473 : ((-172435950423/10000000000000 : ℚ) : ℝ) ≤ stT266 473 := by
  have hc : ((-375023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).2
  have h0 : (0:ℝ) ≤ ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172435950423/10000000000000 : ℚ) : ℝ)
      = ((459801/10000000 : ℚ) : ℝ) * ((-375023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c474 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((35299/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -348343/1000000) (δ := 107/8000000) (ψ := 181581/500000) 266 261
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t474 : ((3241753407/400000000000 : ℚ) : ℝ) ≤ stT266 474 := by
  have hc : ((35289/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3241753407/400000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((35289/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c475 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((84103/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2081943/10000000) (δ := 3357/250000000) (ψ := 181581/500000) 266 261
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t475 : ((154344783597/5000000000000 : ℚ) : ℝ) ≤ stT266 475 := by
  have hc : ((336387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154344783597/5000000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((336387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c476 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((60179/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -85431/1250000) (δ := 3357/250000000) (ψ := 181581/500000) 266 261
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t476 : ((220652417043/5000000000000 : ℚ) : ℝ) ≤ stT266 476 := by
  have hc : ((481407/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220652417043/5000000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((481407/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c477 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((119963/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 712121/10000000) (δ := 3357/250000000) (ψ := 181581/500000) 266 261
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t477 : ((54924357209/1250000000000 : ℚ) : ℝ) ≤ stT266 477 := by
  have hc : ((479827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54924357209/1250000000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((479827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c478 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((666023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2104831/10000000) (δ := 107/8000000) (ψ := 181581/500000) 266 261
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t478 : ((304608724497/10000000000000 : ℚ) : ℝ) ≤ stT266 478 := by
  have hc : ((665973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).1
  have hw2 : ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((457389/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((304608724497/10000000000000 : ℚ) : ℝ)
      = ((457389/10000000 : ℚ) : ℝ) * ((665973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c479 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((43029/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 873637/2500000) (δ := 107/8000000) (ψ := 181581/500000) 266 261
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t479 : ((39309424063/5000000000000 : ℚ) : ℝ) ≤ stT266 479 := by
  have hc : ((86033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).1
  have hw2 : ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((456911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39309424063/5000000000000 : ℚ) : ℝ)
      = ((456911/10000000 : ℚ) : ℝ) * ((86033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c480 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-46573/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 76273/156250) (δ := 107/8000000) (ψ := 181581/500000) 266 261
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t480 : ((-21260446553/1250000000000 : ℚ) : ℝ) ≤ stT266 480 := by
  have hc : ((-186317/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21260446553/1250000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-186317/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c481 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-50301/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6265403/10000000) (δ := 3357/250000000) (ψ := 181581/500000) 266 261
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t481 : ((-183493753113/5000000000000 : ℚ) : ℝ) ≤ stT266 481 := by
  have hc : ((-402433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183493753113/5000000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-402433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c482 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-996559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3823271/5000000) (δ := 107/8000000) (ψ := 181581/500000) 266 261
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t482 : ((-7092866253/156250000000 : ℚ) : ℝ) ≤ stT266 482 := by
  have hc : ((-996609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).2
  have h0 : (0:ℝ) ≤ ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7092866253/156250000000 : ℚ) : ℝ)
      = ((7117/156250 : ℚ) : ℝ) * ((-996609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c483 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-892333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6683209/10000000) (δ := 333/25000000) (ψ := 181581/500000) 266 262
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t483 : ((-50756067891/1250000000000 : ℚ) : ℝ) ≤ stT266 483 := by
  have hc : ((-892383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).2
  have h0 : (0:ℝ) ≤ ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50756067891/1250000000000 : ℚ) : ℝ)
      = ((56877/1250000 : ℚ) : ℝ) * ((-892383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c484 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-524663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5307789/10000000) (δ := 13483/1000000000) (ψ := 181581/500000) 266 262
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t484 : ((-119253097649/5000000000000 : ℚ) : ℝ) ≤ stT266 484 := by
  have hc : ((-524713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).2
  have h0 : (0:ℝ) ≤ ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119253097649/5000000000000 : ℚ) : ℝ)
      = ((227273/5000000 : ℚ) : ℝ) * ((-524713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c485 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-1661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -61489/156250) (δ := 333/25000000) (ψ := 181581/500000) 266 262
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t485 : ((-382786911/2500000000000 : ℚ) : ℝ) ≤ stT266 485 := by
  have hc : ((-843/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).2
  have h0 : (0:ℝ) ≤ ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-382786911/2500000000000 : ℚ) : ℝ)
      = ((454077/10000000 : ℚ) : ℝ) * ((-843/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c486 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((518063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2565529/10000000) (δ := 333/25000000) (ψ := 181581/500000) 266 262
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t486 : ((234975358917/10000000000000 : ℚ) : ℝ) ≤ stT266 486 := by
  have hc : ((518013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234975358917/10000000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((518013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c487 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((3549/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1198621/10000000) (δ := 13483/1000000000) (ψ := 181581/500000) 266 262
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t487 : ((502535587/12500000000 : ℚ) : ℝ) ≤ stT266 487 := by
  have hc : ((1109/1250 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).1
  have hw2 : ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453143/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((502535587/12500000000 : ℚ) : ℝ)
      = ((453143/10000000 : ℚ) : ℝ) * ((1109/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c488 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((99781/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 165493/10000000) (δ := 333/25000000) (ψ := 181581/500000) 266 262
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t488 : ((352862501/7812500000 : ℚ) : ℝ) ≤ stT266 488 := by
  have hc : ((3118/3125 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).1
  have hw2 : ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((226339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352862501/7812500000 : ℚ) : ℝ)
      = ((226339/5000000 : ℚ) : ℝ) * ((3118/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c489 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((819247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 381687/2500000) (δ := 333/25000000) (ψ := 181581/500000) 266 262
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t489 : ((74090634271/2000000000000 : ℚ) : ℝ) ≤ stT266 489 := by
  have hc : ((819197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).1
  have hw2 : ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90443/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74090634271/2000000000000 : ℚ) : ℝ)
      = ((90443/2000000 : ℚ) : ℝ) * ((819197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c490 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((101183/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2885277/10000000) (δ := 13483/1000000000) (ψ := 181581/500000) 266 262
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t490 : ((91408153773/5000000000000 : ℚ) : ℝ) ≤ stT266 490 := by
  have hc : ((202341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).1
  have hw2 : ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451753/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91408153773/5000000000000 : ℚ) : ℝ)
      = ((451753/10000000 : ℚ) : ℝ) * ((202341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c491 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-25061/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4241079/10000000) (δ := 13483/1000000000) (ψ := 181581/500000) 266 262
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t491 : ((-5657195937/1000000000000 : ℚ) : ℝ) ≤ stT266 491 := by
  have hc : ((-25071/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5657195937/1000000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-25071/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c492 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-123701/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 699261/1250000) (δ := 13483/1000000000) (ψ := 181581/500000) 266 262
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t492 : ((-11154649737/400000000000 : ℚ) : ℝ) ≤ stT266 492 := by
  have hc : ((-123711/200000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).2
  have h0 : (0:ℝ) ≤ ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11154649737/400000000000 : ℚ) : ℝ)
      = ((90167/2000000 : ℚ) : ℝ) * ((-123711/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c493 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-467263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 434019/625000) (δ := 13483/1000000000) (ψ := 181581/500000) 266 262
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t493 : ((-13153514679/312500000000 : ℚ) : ℝ) ≤ stT266 493 := by
  have hc : ((-58411/62500 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).2
  have h0 : (0:ℝ) ≤ ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13153514679/312500000000 : ℚ) : ℝ)
      = ((225189/5000000 : ℚ) : ℝ) * ((-58411/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c494 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-9847/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -927013/1250000) (δ := 13413/1000000000) (ψ := 181581/500000) 266 263
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t494 : ((-886121379/20000000000 : ℚ) : ℝ) ≤ stT266 494 := by
  have hc : ((-3939/4000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).2
  have h0 : (0:ℝ) ≤ ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-886121379/20000000000 : ℚ) : ℝ)
      = ((224961/5000000 : ℚ) : ℝ) * ((-3939/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c495 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-378183/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6071341/10000000) (δ := 13413/1000000000) (ψ := 181581/500000) 266 263
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t495 : ((-5312250473/156250000000 : ℚ) : ℝ) ≤ stT266 495 := by
  have hc : ((-11819/15625 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).2
  have h0 : (0:ℝ) ≤ ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5312250473/156250000000 : ℚ) : ℝ)
      = ((449467/10000000 : ℚ) : ℝ) * ((-11819/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c496 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((-15771/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2364619/5000000) (δ := 13413/1000000000) (ψ := 181581/500000) 266 263
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t496 : ((-7082522329/500000000000 : ℚ) : ℝ) ≤ stT266 496 := by
  have hc : ((-31547/100000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).2
  have h0 : (0:ℝ) ≤ ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7082522329/500000000000 : ℚ) : ℝ)
      = ((224507/5000000 : ℚ) : ℝ) * ((-31547/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c497 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((213203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3389861/10000000) (δ := 1339/100000000) (ψ := 181581/500000) 266 263
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t497 : ((95612122833/10000000000000 : ℚ) : ℝ) ≤ stT266 497 := by
  have hc : ((213153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).1
  have hw2 : ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((448561/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95612122833/10000000000000 : ℚ) : ℝ)
      = ((448561/10000000 : ℚ) : ℝ) * ((213153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c498 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((340641/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2053211/10000000) (δ := 1339/100000000) (ψ := 181581/500000) 266 263
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t498 : ((1907917947/62500000000 : ℚ) : ℝ) ≤ stT266 498 := by
  have hc : ((42577/62500 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).1
  have hw2 : ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((44811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1907917947/62500000000 : ℚ) : ℝ)
      = ((44811/1000000 : ℚ) : ℝ) * ((42577/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c499 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((479451/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -719221/10000000) (δ := 1339/100000000) (ψ := 181581/500000) 266 263
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t499 : ((107310161293/2500000000000 : ℚ) : ℝ) ≤ stT266 499 := by
  have hc : ((239713/250000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).1
  have hw2 : ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107310161293/2500000000000 : ℚ) : ℝ)
      = ((447661/10000000 : ℚ) : ℝ) * ((239713/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_c500 :
    |Real.cos (((266 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((38807/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 612109/10000000) (δ := 1339/100000000) (ψ := 181581/500000) 266 263
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st266_t500 : ((3470820093/80000000000 : ℚ) : ℝ) ≤ stT266 500 := by
  have hc : ((7761/8000 : ℚ) : ℝ)
      ≤ Real.cos (((266 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((181581/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st266_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).1
  have hw2 : ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3470820093/80000000000 : ℚ) : ℝ)
      = ((447213/10000000 : ℚ) : ℝ) * ((7761/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st266_p1 : ((116841/125000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT266 (i+1) := by
  rw [Finset.sum_range_one]
  exact st266_t1

theorem st266_p2 : ((120770414133/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT266 (i+1))
      = (∑ i ∈ Finset.range 1, stT266 (i+1)) + stT266 2 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 1
    simpa using h
  have hprev := st266_p1
  have hstep := st266_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p3 : ((1107049240863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT266 (i+1))
      = (∑ i ∈ Finset.range 2, stT266 (i+1)) + stT266 3 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 2
    simpa using h
  have hprev := st266_p2
  have hstep := st266_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p4 : ((-147461524629/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT266 (i+1))
      = (∑ i ∈ Finset.range 3, stT266 (i+1)) + stT266 4 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 3
    simpa using h
  have hprev := st266_p3
  have hstep := st266_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p5 : ((1382226800299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT266 (i+1))
      = (∑ i ∈ Finset.range 4, stT266 (i+1)) + stT266 5 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 4
    simpa using h
  have hprev := st266_p4
  have hstep := st266_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p6 : ((394558096291/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT266 (i+1))
      = (∑ i ∈ Finset.range 5, stT266 (i+1)) + stT266 6 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 5
    simpa using h
  have hprev := st266_p5
  have hstep := st266_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p7 : ((227777481021/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT266 (i+1))
      = (∑ i ∈ Finset.range 6, stT266 (i+1)) + stT266 7 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 6
    simpa using h
  have hprev := st266_p6
  have hstep := st266_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p8 : ((1443089816751/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT266 (i+1))
      = (∑ i ∈ Finset.range 7, stT266 (i+1)) + stT266 8 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 7
    simpa using h
  have hprev := st266_p7
  have hstep := st266_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p9 : ((2252956402431/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT266 (i+1))
      = (∑ i ∈ Finset.range 8, stT266 (i+1)) + stT266 9 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 8
    simpa using h
  have hprev := st266_p8
  have hstep := st266_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p10 : ((3107855470811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT266 (i+1))
      = (∑ i ∈ Finset.range 9, stT266 (i+1)) + stT266 10 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 9
    simpa using h
  have hprev := st266_p9
  have hstep := st266_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p11 : ((1653376537667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT266 (i+1))
      = (∑ i ∈ Finset.range 10, stT266 (i+1)) + stT266 11 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 10
    simpa using h
  have hprev := st266_p10
  have hstep := st266_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p12 : ((2564527529299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT266 (i+1))
      = (∑ i ∈ Finset.range 11, stT266 (i+1)) + stT266 12 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 11
    simpa using h
  have hprev := st266_p11
  have hstep := st266_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p13 : ((2404159663623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT266 (i+1))
      = (∑ i ∈ Finset.range 12, stT266 (i+1)) + stT266 13 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 12
    simpa using h
  have hprev := st266_p12
  have hstep := st266_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p14 : ((538185390627/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT266 (i+1))
      = (∑ i ∈ Finset.range 13, stT266 (i+1)) + stT266 14 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 13
    simpa using h
  have hprev := st266_p13
  have hstep := st266_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p15 : ((-1120248614529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT266 (i+1))
      = (∑ i ∈ Finset.range 14, stT266 (i+1)) + stT266 15 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 14
    simpa using h
  have hprev := st266_p14
  have hstep := st266_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p16 : ((-1094835771149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT266 (i+1))
      = (∑ i ∈ Finset.range 15, stT266 (i+1)) + stT266 16 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 15
    simpa using h
  have hprev := st266_p15
  have hstep := st266_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p17 : ((-175759241729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT266 (i+1))
      = (∑ i ∈ Finset.range 16, stT266 (i+1)) + stT266 17 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 16
    simpa using h
  have hprev := st266_p16
  have hstep := st266_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p18 : ((-1173829596629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT266 (i+1))
      = (∑ i ∈ Finset.range 17, stT266 (i+1)) + stT266 18 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 17
    simpa using h
  have hprev := st266_p17
  have hstep := st266_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p19 : ((-3066062585819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT266 (i+1))
      = (∑ i ∈ Finset.range 18, stT266 (i+1)) + stT266 19 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 18
    simpa using h
  have hprev := st266_p18
  have hstep := st266_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p20 : ((-2825417055279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT266 (i+1))
      = (∑ i ∈ Finset.range 19, stT266 (i+1)) + stT266 20 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 19
    simpa using h
  have hprev := st266_p19
  have hstep := st266_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p21 : ((-1741810743641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT266 (i+1))
      = (∑ i ∈ Finset.range 20, stT266 (i+1)) + stT266 21 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 20
    simpa using h
  have hprev := st266_p20
  have hstep := st266_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p22 : ((-1055794851251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT266 (i+1))
      = (∑ i ∈ Finset.range 21, stT266 (i+1)) + stT266 22 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 21
    simpa using h
  have hprev := st266_p21
  have hstep := st266_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p23 : ((-1895732960151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT266 (i+1))
      = (∑ i ∈ Finset.range 22, stT266 (i+1)) + stT266 23 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 22
    simpa using h
  have hprev := st266_p22
  have hstep := st266_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p24 : ((-3928950837849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT266 (i+1))
      = (∑ i ∈ Finset.range 23, stT266 (i+1)) + stT266 24 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 23
    simpa using h
  have hprev := st266_p23
  have hstep := st266_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p25 : ((-3480530837849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT266 (i+1))
      = (∑ i ∈ Finset.range 24, stT266 (i+1)) + stT266 25 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 24
    simpa using h
  have hprev := st266_p24
  have hstep := st266_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p26 : ((-2098955670501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT266 (i+1))
      = (∑ i ∈ Finset.range 25, stT266 (i+1)) + stT266 26 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 25
    simpa using h
  have hprev := st266_p25
  have hstep := st266_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p27 : ((-3994188859293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT266 (i+1))
      = (∑ i ∈ Finset.range 26, stT266 (i+1)) + stT266 27 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 26
    simpa using h
  have hprev := st266_p26
  have hstep := st266_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p28 : ((-421930160321/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT266 (i+1))
      = (∑ i ∈ Finset.range 27, stT266 (i+1)) + stT266 28 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 27
    simpa using h
  have hprev := st266_p27
  have hstep := st266_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p29 : ((-3966448817469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT266 (i+1))
      = (∑ i ∈ Finset.range 28, stT266 (i+1)) + stT266 29 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 28
    simpa using h
  have hprev := st266_p28
  have hstep := st266_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p30 : ((-1150990498611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT266 (i+1))
      = (∑ i ∈ Finset.range 29, stT266 (i+1)) + stT266 30 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 29
    simpa using h
  have hprev := st266_p29
  have hstep := st266_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p31 : ((-1537420496981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT266 (i+1))
      = (∑ i ∈ Finset.range 30, stT266 (i+1)) + stT266 31 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 30
    simpa using h
  have hprev := st266_p30
  have hstep := st266_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p32 : ((-1987985414407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT266 (i+1))
      = (∑ i ∈ Finset.range 31, stT266 (i+1)) + stT266 32 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 31
    simpa using h
  have hprev := st266_p31
  have hstep := st266_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p33 : ((-227123063279/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT266 (i+1))
      = (∑ i ∈ Finset.range 32, stT266 (i+1)) + stT266 33 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 32
    simpa using h
  have hprev := st266_p32
  have hstep := st266_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p34 : ((-207169555801/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT266 (i+1))
      = (∑ i ∈ Finset.range 33, stT266 (i+1)) + stT266 34 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 33
    simpa using h
  have hprev := st266_p33
  have hstep := st266_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p35 : ((-1852645655221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT266 (i+1))
      = (∑ i ∈ Finset.range 34, stT266 (i+1)) + stT266 35 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 34
    simpa using h
  have hprev := st266_p34
  have hstep := st266_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p36 : ((-4674433170937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT266 (i+1))
      = (∑ i ∈ Finset.range 35, stT266 (i+1)) + stT266 36 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 35
    simpa using h
  have hprev := st266_p35
  have hstep := st266_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p37 : ((-4057927432003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT266 (i+1))
      = (∑ i ∈ Finset.range 36, stT266 (i+1)) + stT266 37 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 36
    simpa using h
  have hprev := st266_p36
  have hstep := st266_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p38 : ((-2548992635623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT266 (i+1))
      = (∑ i ∈ Finset.range 37, stT266 (i+1)) + stT266 38 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 37
    simpa using h
  have hprev := st266_p37
  have hstep := st266_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p39 : ((-124721960761/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT266 (i+1))
      = (∑ i ∈ Finset.range 38, stT266 (i+1)) + stT266 39 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 38
    simpa using h
  have hprev := st266_p38
  have hstep := st266_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p40 : ((52391369833/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT266 (i+1))
      = (∑ i ∈ Finset.range 39, stT266 (i+1)) + stT266 40 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 39
    simpa using h
  have hprev := st266_p39
  have hstep := st266_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p41 : ((1070427710209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT266 (i+1))
      = (∑ i ∈ Finset.range 40, stT266 (i+1)) + stT266 41 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 40
    simpa using h
  have hprev := st266_p40
  have hstep := st266_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p42 : ((87568948717/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT266 (i+1))
      = (∑ i ∈ Finset.range 41, stT266 (i+1)) + stT266 42 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 41
    simpa using h
  have hprev := st266_p41
  have hstep := st266_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p43 : ((245710848267/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT266 (i+1))
      = (∑ i ∈ Finset.range 42, stT266 (i+1)) + stT266 43 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 42
    simpa using h
  have hprev := st266_p42
  have hstep := st266_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p44 : ((1684188921439/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT266 (i+1))
      = (∑ i ∈ Finset.range 43, stT266 (i+1)) + stT266 44 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 43
    simpa using h
  have hprev := st266_p43
  have hstep := st266_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p45 : ((114620770363/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT266 (i+1))
      = (∑ i ∈ Finset.range 44, stT266 (i+1)) + stT266 45 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 44
    simpa using h
  have hprev := st266_p44
  have hstep := st266_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p46 : ((3017754359891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT266 (i+1))
      = (∑ i ∈ Finset.range 45, stT266 (i+1)) + stT266 46 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 45
    simpa using h
  have hprev := st266_p45
  have hstep := st266_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p47 : ((7388351697269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT266 (i+1))
      = (∑ i ∈ Finset.range 46, stT266 (i+1)) + stT266 47 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 46
    simpa using h
  have hprev := st266_p46
  have hstep := st266_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p48 : ((4043122580197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT266 (i+1))
      = (∑ i ∈ Finset.range 47, stT266 (i+1)) + stT266 48 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 47
    simpa using h
  have hprev := st266_p47
  have hstep := st266_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p49 : ((3836266783169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT266 (i+1))
      = (∑ i ∈ Finset.range 48, stT266 (i+1)) + stT266 49 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 48
    simpa using h
  have hprev := st266_p48
  have hstep := st266_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p50 : ((3176415743979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT266 (i+1))
      = (∑ i ∈ Finset.range 49, stT266 (i+1)) + stT266 50 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 49
    simpa using h
  have hprev := st266_p49
  have hstep := st266_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p51 : ((5236237616591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT266 (i+1))
      = (∑ i ∈ Finset.range 50, stT266 (i+1)) + stT266 51 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 50
    simpa using h
  have hprev := st266_p50
  have hstep := st266_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p52 : ((5504964805091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT266 (i+1))
      = (∑ i ∈ Finset.range 51, stT266 (i+1)) + stT266 52 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 51
    simpa using h
  have hprev := st266_p51
  have hstep := st266_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p53 : ((6861094802281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT266 (i+1))
      = (∑ i ∈ Finset.range 52, stT266 (i+1)) + stT266 53 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 52
    simpa using h
  have hprev := st266_p52
  have hstep := st266_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p54 : ((1853691919909/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT266 (i+1))
      = (∑ i ∈ Finset.range 53, stT266 (i+1)) + stT266 54 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 53
    simpa using h
  have hprev := st266_p53
  have hstep := st266_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p55 : ((1573105723609/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT266 (i+1))
      = (∑ i ∈ Finset.range 54, stT266 (i+1)) + stT266 55 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 54
    simpa using h
  have hprev := st266_p54
  have hstep := st266_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p56 : ((5464541955033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT266 (i+1))
      = (∑ i ∈ Finset.range 55, stT266 (i+1)) + stT266 56 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 55
    simpa using h
  have hprev := st266_p55
  have hstep := st266_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p57 : ((6507765875277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT266 (i+1))
      = (∑ i ∈ Finset.range 56, stT266 (i+1)) + stT266 57 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 56
    simpa using h
  have hprev := st266_p56
  have hstep := st266_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p58 : ((7224667305741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT266 (i+1))
      = (∑ i ∈ Finset.range 57, stT266 (i+1)) + stT266 58 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 57
    simpa using h
  have hprev := st266_p57
  have hstep := st266_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p59 : ((6031826215921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT266 (i+1))
      = (∑ i ∈ Finset.range 58, stT266 (i+1)) + stT266 59 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 58
    simpa using h
  have hprev := st266_p58
  have hstep := st266_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p60 : ((2906270839103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT266 (i+1))
      = (∑ i ∈ Finset.range 59, stT266 (i+1)) + stT266 60 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 59
    simpa using h
  have hprev := st266_p59
  have hstep := st266_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p61 : ((3539708580111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT266 (i+1))
      = (∑ i ∈ Finset.range 60, stT266 (i+1)) + stT266 61 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 60
    simpa using h
  have hprev := st266_p60
  have hstep := st266_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p62 : ((1608768188877/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT266 (i+1))
      = (∑ i ∈ Finset.range 61, stT266 (i+1)) + stT266 62 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 61
    simpa using h
  have hprev := st266_p61
  have hstep := st266_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p63 : ((2870988825247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT266 (i+1))
      = (∑ i ∈ Finset.range 62, stT266 (i+1)) + stT266 63 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 62
    simpa using h
  have hprev := st266_p62
  have hstep := st266_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p64 : ((3494865700247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT266 (i+1))
      = (∑ i ∈ Finset.range 63, stT266 (i+1)) + stT266 64 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 63
    simpa using h
  have hprev := st266_p63
  have hstep := st266_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p65 : ((3181767755477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT266 (i+1))
      = (∑ i ∈ Finset.range 64, stT266 (i+1)) + stT266 65 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 64
    simpa using h
  have hprev := st266_p64
  have hstep := st266_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p66 : ((736879003643/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT266 (i+1))
      = (∑ i ∈ Finset.range 65, stT266 (i+1)) + stT266 66 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 65
    simpa using h
  have hprev := st266_p65
  have hstep := st266_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p67 : ((1763478463457/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT266 (i+1))
      = (∑ i ∈ Finset.range 66, stT266 (i+1)) + stT266 67 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 66
    simpa using h
  have hprev := st266_p66
  have hstep := st266_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p68 : ((2988358888533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT266 (i+1))
      = (∑ i ∈ Finset.range 67, stT266 (i+1)) + stT266 68 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 67
    simpa using h
  have hprev := st266_p67
  have hstep := st266_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p69 : ((1597869238629/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT266 (i+1))
      = (∑ i ∈ Finset.range 68, stT266 (i+1)) + stT266 69 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 68
    simpa using h
  have hprev := st266_p68
  have hstep := st266_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p70 : ((105988430397/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT266 (i+1))
      = (∑ i ∈ Finset.range 69, stT266 (i+1)) + stT266 70 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 69
    simpa using h
  have hprev := st266_p69
  have hstep := st266_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p71 : ((580725121539/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT266 (i+1))
      = (∑ i ∈ Finset.range 70, stT266 (i+1)) + stT266 71 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 70
    simpa using h
  have hprev := st266_p70
  have hstep := st266_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p72 : ((6985289632479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT266 (i+1))
      = (∑ i ∈ Finset.range 71, stT266 (i+1)) + stT266 72 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 71
    simpa using h
  have hprev := st266_p71
  have hstep := st266_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p73 : ((9533781743/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT266 (i+1))
      = (∑ i ∈ Finset.range 72, stT266 (i+1)) + stT266 73 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 72
    simpa using h
  have hprev := st266_p72
  have hstep := st266_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p74 : ((6607609990463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT266 (i+1))
      = (∑ i ∈ Finset.range 73, stT266 (i+1)) + stT266 74 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 73
    simpa using h
  have hprev := st266_p73
  have hstep := st266_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p75 : ((6419680093311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT266 (i+1))
      = (∑ i ∈ Finset.range 74, stT266 (i+1)) + stT266 75 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 74
    simpa using h
  have hprev := st266_p74
  have hstep := st266_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p76 : ((1234261991983/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT266 (i+1))
      = (∑ i ∈ Finset.range 75, stT266 (i+1)) + stT266 76 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 75
    simpa using h
  have hprev := st266_p75
  have hstep := st266_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p77 : ((270823396977/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT266 (i+1))
      = (∑ i ∈ Finset.range 76, stT266 (i+1)) + stT266 77 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 76
    simpa using h
  have hprev := st266_p76
  have hstep := st266_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p78 : ((5923993118883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT266 (i+1))
      = (∑ i ∈ Finset.range 77, stT266 (i+1)) + stT266 78 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 77
    simpa using h
  have hprev := st266_p77
  have hstep := st266_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p79 : ((692223893559/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT266 (i+1))
      = (∑ i ∈ Finset.range 78, stT266 (i+1)) + stT266 79 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 78
    simpa using h
  have hprev := st266_p78
  have hstep := st266_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p80 : ((1461535877241/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT266 (i+1))
      = (∑ i ∈ Finset.range 79, stT266 (i+1)) + stT266 80 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 79
    simpa using h
  have hprev := st266_p79
  have hstep := st266_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p81 : ((6950217843001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT266 (i+1))
      = (∑ i ∈ Finset.range 80, stT266 (i+1)) + stT266 81 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 80
    simpa using h
  have hprev := st266_p80
  have hstep := st266_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p82 : ((5845902947317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT266 (i+1))
      = (∑ i ∈ Finset.range 81, stT266 (i+1)) + stT266 82 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 81
    simpa using h
  have hprev := st266_p81
  have hstep := st266_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p83 : ((6938766911691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT266 (i+1))
      = (∑ i ∈ Finset.range 82, stT266 (i+1)) + stT266 83 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 82
    simpa using h
  have hprev := st266_p82
  have hstep := st266_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p84 : ((5857825139781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT266 (i+1))
      = (∑ i ∈ Finset.range 83, stT266 (i+1)) + stT266 84 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 83
    simpa using h
  have hprev := st266_p83
  have hstep := st266_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p85 : ((6931316070701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT266 (i+1))
      = (∑ i ∈ Finset.range 84, stT266 (i+1)) + stT266 85 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 84
    simpa using h
  have hprev := st266_p84
  have hstep := st266_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p86 : ((1171956954417/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT266 (i+1))
      = (∑ i ∈ Finset.range 85, stT266 (i+1)) + stT266 86 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 85
    simpa using h
  have hprev := st266_p85
  have hstep := st266_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p87 : ((1386138129217/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT266 (i+1))
      = (∑ i ∈ Finset.range 86, stT266 (i+1)) + stT266 87 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 86
    simpa using h
  have hprev := st266_p86
  have hstep := st266_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p88 : ((5866255803973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT266 (i+1))
      = (∑ i ∈ Finset.range 87, stT266 (i+1)) + stT266 88 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 87
    simpa using h
  have hprev := st266_p87
  have hstep := st266_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p89 : ((1381380723747/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT266 (i+1))
      = (∑ i ∈ Finset.range 88, stT266 (i+1)) + stT266 89 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 88
    simpa using h
  have hprev := st266_p88
  have hstep := st266_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p90 : ((2960274898597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT266 (i+1))
      = (∑ i ∈ Finset.range 89, stT266 (i+1)) + stT266 90 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 89
    simpa using h
  have hprev := st266_p89
  have hstep := st266_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p91 : ((3403513484329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT266 (i+1))
      = (∑ i ∈ Finset.range 90, stT266 (i+1)) + stT266 91 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 90
    simpa using h
  have hprev := st266_p90
  have hstep := st266_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p92 : ((3039330224553/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT266 (i+1))
      = (∑ i ∈ Finset.range 91, stT266 (i+1)) + stT266 92 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 91
    simpa using h
  have hprev := st266_p91
  have hstep := st266_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p93 : ((3291284430729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT266 (i+1))
      = (∑ i ∈ Finset.range 92, stT266 (i+1)) + stT266 93 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 92
    simpa using h
  have hprev := st266_p92
  have hstep := st266_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p94 : ((1591658361451/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT266 (i+1))
      = (∑ i ∈ Finset.range 93, stT266 (i+1)) + stT266 94 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 93
    simpa using h
  have hprev := st266_p93
  have hstep := st266_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p95 : ((3123975123521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT266 (i+1))
      = (∑ i ∈ Finset.range 94, stT266 (i+1)) + stT266 95 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 94
    simpa using h
  have hprev := st266_p94
  have hstep := st266_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p96 : ((3356023797031/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT266 (i+1))
      = (∑ i ∈ Finset.range 95, stT266 (i+1)) + stT266 96 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 95
    simpa using h
  have hprev := st266_p95
  have hstep := st266_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p97 : ((2972190139927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT266 (i+1))
      = (∑ i ∈ Finset.range 96, stT266 (i+1)) + stT266 97 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 96
    simpa using h
  have hprev := st266_p96
  have hstep := st266_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p98 : ((690929565299/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT266 (i+1))
      = (∑ i ∈ Finset.range 97, stT266 (i+1)) + stT266 98 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 97
    simpa using h
  have hprev := st266_p97
  have hstep := st266_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p99 : ((1478539068063/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT266 (i+1))
      = (∑ i ∈ Finset.range 98, stT266 (i+1)) + stT266 99 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 98
    simpa using h
  have hprev := st266_p98
  have hstep := st266_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p100 : ((6734304452103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT266 (i+1))
      = (∑ i ∈ Finset.range 99, stT266 (i+1)) + stT266 100 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 99
    simpa using h
  have hprev := st266_p99
  have hstep := st266_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p101 : ((6286303518173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT266 (i+1))
      = (∑ i ∈ Finset.range 100, stT266 (i+1)) + stT266 101 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 100
    simpa using h
  have hprev := st266_p100
  have hstep := st266_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p102 : ((6232902856237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT266 (i+1))
      = (∑ i ∈ Finset.range 101, stT266 (i+1)) + stT266 102 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 101
    simpa using h
  have hprev := st266_p101
  have hstep := st266_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p103 : ((6789519149653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT266 (i+1))
      = (∑ i ∈ Finset.range 102, stT266 (i+1)) + stT266 103 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 102
    simpa using h
  have hprev := st266_p102
  have hstep := st266_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p104 : ((5885872573751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT266 (i+1))
      = (∑ i ∈ Finset.range 103, stT266 (i+1)) + stT266 104 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 103
    simpa using h
  have hprev := st266_p103
  have hstep := st266_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p105 : ((6842806933151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT266 (i+1))
      = (∑ i ∈ Finset.range 104, stT266 (i+1)) + stT266 105 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 104
    simpa using h
  have hprev := st266_p104
  have hstep := st266_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p106 : ((6178333668689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT266 (i+1))
      = (∑ i ∈ Finset.range 105, stT266 (i+1)) + stT266 106 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 105
    simpa using h
  have hprev := st266_p105
  have hstep := st266_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p107 : ((6283851936353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT266 (i+1))
      = (∑ i ∈ Finset.range 106, stT266 (i+1)) + stT266 107 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 106
    simpa using h
  have hprev := st266_p106
  have hstep := st266_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p108 : ((6793090994603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT266 (i+1))
      = (∑ i ∈ Finset.range 107, stT266 (i+1)) + stT266 108 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 107
    simpa using h
  have hprev := st266_p107
  have hstep := st266_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p109 : ((2942386557203/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT266 (i+1))
      = (∑ i ∈ Finset.range 108, stT266 (i+1)) + stT266 109 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 108
    simpa using h
  have hprev := st266_p108
  have hstep := st266_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p110 : ((3383428521081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT266 (i+1))
      = (∑ i ∈ Finset.range 109, stT266 (i+1)) + stT266 110 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 109
    simpa using h
  have hprev := st266_p109
  have hstep := st266_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p111 : ((794542919961/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT266 (i+1))
      = (∑ i ∈ Finset.range 110, stT266 (i+1)) + stT266 111 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 110
    simpa using h
  have hprev := st266_p110
  have hstep := st266_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p112 : ((758647839133/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT266 (i+1))
      = (∑ i ∈ Finset.range 111, stT266 (i+1)) + stT266 112 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 111
    simpa using h
  have hprev := st266_p111
  have hstep := st266_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p113 : ((862673950223/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT266 (i+1))
      = (∑ i ∈ Finset.range 112, stT266 (i+1)) + stT266 113 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 112
    simpa using h
  have hprev := st266_p112
  have hstep := st266_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p114 : ((3005136084577/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT266 (i+1))
      = (∑ i ∈ Finset.range 113, stT266 (i+1)) + stT266 114 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 113
    simpa using h
  have hprev := st266_p113
  have hstep := st266_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p115 : ((3203429330161/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT266 (i+1))
      = (∑ i ∈ Finset.range 114, stT266 (i+1)) + stT266 115 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 114
    simpa using h
  have hprev := st266_p114
  have hstep := st266_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p116 : ((3383857750051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT266 (i+1))
      = (∑ i ∈ Finset.range 115, stT266 (i+1)) + stT266 116 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 115
    simpa using h
  have hprev := st266_p115
  have hstep := st266_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p117 : ((5888162814221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT266 (i+1))
      = (∑ i ∈ Finset.range 116, stT266 (i+1)) + stT266 117 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 116
    simpa using h
  have hprev := st266_p116
  have hstep := st266_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p118 : ((6665880299753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT266 (i+1))
      = (∑ i ∈ Finset.range 117, stT266 (i+1)) + stT266 118 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 117
    simpa using h
  have hprev := st266_p117
  have hstep := st266_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p119 : ((1641426087433/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT266 (i+1))
      = (∑ i ∈ Finset.range 118, stT266 (i+1)) + stT266 119 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 118
    simpa using h
  have hprev := st266_p118
  have hstep := st266_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p120 : ((1476722250129/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT266 (i+1))
      = (∑ i ∈ Finset.range 119, stT266 (i+1)) + stT266 120 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 119
    simpa using h
  have hprev := st266_p119
  have hstep := st266_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p121 : ((1700726571579/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT266 (i+1))
      = (∑ i ∈ Finset.range 120, stT266 (i+1)) + stT266 121 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 120
    simpa using h
  have hprev := st266_p120
  have hstep := st266_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p122 : ((1602464446407/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT266 (i+1))
      = (∑ i ∈ Finset.range 121, stT266 (i+1)) + stT266 122 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 121
    simpa using h
  have hprev := st266_p121
  have hstep := st266_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p123 : ((1490226368147/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT266 (i+1))
      = (∑ i ∈ Finset.range 122, stT266 (i+1)) + stT266 123 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 122
    simpa using h
  have hprev := st266_p122
  have hstep := st266_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p124 : ((3428582527723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT266 (i+1))
      = (∑ i ∈ Finset.range 123, stT266 (i+1)) + stT266 124 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 123
    simpa using h
  have hprev := st266_p123
  have hstep := st266_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p125 : ((126636777387/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT266 (i+1))
      = (∑ i ∈ Finset.range 124, stT266 (i+1)) + stT266 125 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 124
    simpa using h
  have hprev := st266_p124
  have hstep := st266_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p126 : ((5989510106277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT266 (i+1))
      = (∑ i ∈ Finset.range 125, stT266 (i+1)) + stT266 126 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 125
    simpa using h
  have hprev := st266_p125
  have hstep := st266_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p127 : ((6868433562209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT266 (i+1))
      = (∑ i ∈ Finset.range 126, stT266 (i+1)) + stT266 127 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 126
    simpa using h
  have hprev := st266_p126
  have hstep := st266_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p128 : ((253251854861/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT266 (i+1))
      = (∑ i ∈ Finset.range 127, stT266 (i+1)) + stT266 128 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 127
    simpa using h
  have hprev := st266_p127
  have hstep := st266_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p129 : ((5973503976851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT266 (i+1))
      = (∑ i ∈ Finset.range 128, stT266 (i+1)) + stT266 129 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 128
    simpa using h
  have hprev := st266_p128
  have hstep := st266_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p130 : ((6848675425093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT266 (i+1))
      = (∑ i ∈ Finset.range 129, stT266 (i+1)) + stT266 130 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 129
    simpa using h
  have hprev := st266_p129
  have hstep := st266_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p131 : ((800645552411/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT266 (i+1))
      = (∑ i ∈ Finset.range 130, stT266 (i+1)) + stT266 131 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 130
    simpa using h
  have hprev := st266_p130
  have hstep := st266_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p132 : ((5923472868519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT266 (i+1))
      = (∑ i ∈ Finset.range 131, stT266 (i+1)) + stT266 132 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 131
    simpa using h
  have hprev := st266_p131
  have hstep := st266_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p133 : ((1356169540577/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT266 (i+1))
      = (∑ i ∈ Finset.range 132, stT266 (i+1)) + stT266 133 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 132
    simpa using h
  have hprev := st266_p132
  have hstep := st266_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p134 : ((6548660448541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT266 (i+1))
      = (∑ i ∈ Finset.range 133, stT266 (i+1)) + stT266 134 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 133
    simpa using h
  have hprev := st266_p133
  have hstep := st266_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p135 : ((5878832255531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT266 (i+1))
      = (∑ i ∈ Finset.range 134, stT266 (i+1)) + stT266 135 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 134
    simpa using h
  have hprev := st266_p134
  have hstep := st266_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p136 : ((6631508720911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT266 (i+1))
      = (∑ i ∈ Finset.range 135, stT266 (i+1)) + stT266 136 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 135
    simpa using h
  have hprev := st266_p135
  have hstep := st266_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p137 : ((6735073876451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT266 (i+1))
      = (∑ i ∈ Finset.range 136, stT266 (i+1)) + stT266 137 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 136
    simpa using h
  have hprev := st266_p136
  have hstep := st266_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p138 : ((2954307422059/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT266 (i+1))
      = (∑ i ∈ Finset.range 137, stT266 (i+1)) + stT266 138 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 137
    simpa using h
  have hprev := st266_p137
  have hstep := st266_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p139 : ((3190931517547/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT266 (i+1))
      = (∑ i ∈ Finset.range 138, stT266 (i+1)) + stT266 139 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 138
    simpa using h
  have hprev := st266_p138
  have hstep := st266_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p140 : ((3444218255269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT266 (i+1))
      = (∑ i ∈ Finset.range 139, stT266 (i+1)) + stT266 140 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 139
    simpa using h
  have hprev := st266_p139
  have hstep := st266_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p141 : ((3044545127273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT266 (i+1))
      = (∑ i ∈ Finset.range 140, stT266 (i+1)) + stT266 141 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 140
    simpa using h
  have hprev := st266_p140
  have hstep := st266_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p142 : ((379973632911/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT266 (i+1))
      = (∑ i ∈ Finset.range 141, stT266 (i+1)) + stT266 142 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 141
    simpa using h
  have hprev := st266_p141
  have hstep := st266_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p143 : ((860267455473/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT266 (i+1))
      = (∑ i ∈ Finset.range 142, stT266 (i+1)) + stT266 143 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 142
    simpa using h
  have hprev := st266_p142
  have hstep := st266_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p144 : ((3217096726047/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT266 (i+1))
      = (∑ i ∈ Finset.range 143, stT266 (i+1)) + stT266 144 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 143
    simpa using h
  have hprev := st266_p143
  have hstep := st266_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p145 : ((1469578777641/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT266 (i+1))
      = (∑ i ∈ Finset.range 144, stT266 (i+1)) + stT266 145 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 144
    simpa using h
  have hprev := st266_p144
  have hstep := st266_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p146 : ((3306959286567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT266 (i+1))
      = (∑ i ∈ Finset.range 145, stT266 (i+1)) + stT266 146 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 145
    simpa using h
  have hprev := st266_p145
  have hstep := st266_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p147 : ((170067822833/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT266 (i+1))
      = (∑ i ∈ Finset.range 146, stT266 (i+1)) + stT266 147 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 146
    simpa using h
  have hprev := st266_p146
  have hstep := st266_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p148 : ((1196135527113/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT266 (i+1))
      = (∑ i ∈ Finset.range 147, stT266 (i+1)) + stT266 148 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 147
    simpa using h
  have hprev := st266_p147
  have hstep := st266_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p149 : ((3080539018191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT266 (i+1))
      = (∑ i ∈ Finset.range 148, stT266 (i+1)) + stT266 149 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 148
    simpa using h
  have hprev := st266_p148
  have hstep := st266_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p150 : ((3451511934551/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT266 (i+1))
      = (∑ i ∈ Finset.range 149, stT266 (i+1)) + stT266 150 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 149
    simpa using h
  have hprev := st266_p149
  have hstep := st266_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p151 : ((6425389132699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT266 (i+1))
      = (∑ i ∈ Finset.range 150, stT266 (i+1)) + stT266 151 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 150
    simpa using h
  have hprev := st266_p150
  have hstep := st266_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p152 : ((1173475367939/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT266 (i+1))
      = (∑ i ∈ Finset.range 151, stT266 (i+1)) + stT266 152 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 151
    simpa using h
  have hprev := st266_p151
  have hstep := st266_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p153 : ((6541291108567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT266 (i+1))
      = (∑ i ∈ Finset.range 152, stT266 (i+1)) + stT266 153 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 152
    simpa using h
  have hprev := st266_p152
  have hstep := st266_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p154 : ((6872056864907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT266 (i+1))
      = (∑ i ∈ Finset.range 153, stT266 (i+1)) + stT266 154 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 153
    simpa using h
  have hprev := st266_p153
  have hstep := st266_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p155 : ((6098356003127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT266 (i+1))
      = (∑ i ∈ Finset.range 154, stT266 (i+1)) + stT266 155 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 154
    simpa using h
  have hprev := st266_p154
  have hstep := st266_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p156 : ((5992690606511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT266 (i+1))
      = (∑ i ∈ Finset.range 155, stT266 (i+1)) + stT266 156 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 155
    simpa using h
  have hprev := st266_p155
  have hstep := st266_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p157 : ((1358146382739/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT266 (i+1))
      = (∑ i ∈ Finset.range 156, stT266 (i+1)) + stT266 157 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 156
    simpa using h
  have hprev := st266_p156
  have hstep := st266_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p158 : ((6699665980551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT266 (i+1))
      = (∑ i ∈ Finset.range 157, stT266 (i+1)) + stT266 158 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 157
    simpa using h
  have hprev := st266_p157
  have hstep := st266_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p159 : ((1185211447287/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT266 (i+1))
      = (∑ i ∈ Finset.range 158, stT266 (i+1)) + stT266 159 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 158
    simpa using h
  have hprev := st266_p158
  have hstep := st266_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p160 : ((3086991023271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT266 (i+1))
      = (∑ i ∈ Finset.range 159, stT266 (i+1)) + stT266 160 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 159
    simpa using h
  have hprev := st266_p159
  have hstep := st266_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p161 : ((3449062155141/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT266 (i+1))
      = (∑ i ∈ Finset.range 160, stT266 (i+1)) + stT266 161 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 160
    simpa using h
  have hprev := st266_p160
  have hstep := st266_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p162 : ((6534002445857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT266 (i+1))
      = (∑ i ∈ Finset.range 161, stT266 (i+1)) + stT266 162 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 161
    simpa using h
  have hprev := st266_p161
  have hstep := st266_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p163 : ((1466346252161/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT266 (i+1))
      = (∑ i ∈ Finset.range 162, stT266 (i+1)) + stT266 163 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 162
    simpa using h
  have hprev := st266_p162
  have hstep := st266_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p164 : ((1577221309047/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT266 (i+1))
      = (∑ i ∈ Finset.range 163, stT266 (i+1)) + stT266 164 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 163
    simpa using h
  have hprev := st266_p163
  have hstep := st266_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p165 : ((3464226823993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT266 (i+1))
      = (∑ i ∈ Finset.range 164, stT266 (i+1)) + stT266 165 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 164
    simpa using h
  have hprev := st266_p164
  have hstep := st266_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p166 : ((6436309493453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT266 (i+1))
      = (∑ i ∈ Finset.range 165, stT266 (i+1)) + stT266 166 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 165
    simpa using h
  have hprev := st266_p165
  have hstep := st266_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p167 : ((5851243607949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT266 (i+1))
      = (∑ i ∈ Finset.range 166, stT266 (i+1)) + stT266 167 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 166
    simpa using h
  have hprev := st266_p166
  have hstep := st266_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p168 : ((1273237003701/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT266 (i+1))
      = (∑ i ∈ Finset.range 167, stT266 (i+1)) + stT266 168 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 167
    simpa using h
  have hprev := st266_p167
  have hstep := st266_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p169 : ((277395039531/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT266 (i+1))
      = (∑ i ∈ Finset.range 168, stT266 (i+1)) + stT266 169 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 168
    simpa using h
  have hprev := st266_p168
  have hstep := st266_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p170 : ((641925999111/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT266 (i+1))
      = (∑ i ∈ Finset.range 169, stT266 (i+1)) + stT266 170 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 169
    simpa using h
  have hprev := st266_p169
  have hstep := st266_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p171 : ((584760961423/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT266 (i+1))
      = (∑ i ∈ Finset.range 170, stT266 (i+1)) + stT266 171 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 170
    simpa using h
  have hprev := st266_p170
  have hstep := st266_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p172 : ((3171356984819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT266 (i+1))
      = (∑ i ∈ Finset.range 171, stT266 (i+1)) + stT266 172 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 171
    simpa using h
  have hprev := st266_p171
  have hstep := st266_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p173 : ((6934811002793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT266 (i+1))
      = (∑ i ∈ Finset.range 172, stT266 (i+1)) + stT266 173 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 172
    simpa using h
  have hprev := st266_p172
  have hstep := st266_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p174 : ((1620458111603/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT266 (i+1))
      = (∑ i ∈ Finset.range 173, stT266 (i+1)) + stT266 174 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 173
    simpa using h
  have hprev := st266_p173
  have hstep := st266_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p175 : ((292765622189/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT266 (i+1))
      = (∑ i ∈ Finset.range 174, stT266 (i+1)) + stT266 175 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 174
    simpa using h
  have hprev := st266_p174
  have hstep := st266_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p176 : ((780254027057/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT266 (i+1))
      = (∑ i ∈ Finset.range 175, stT266 (i+1)) + stT266 176 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 175
    simpa using h
  have hprev := st266_p175
  have hstep := st266_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p177 : ((1727599335737/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT266 (i+1))
      = (∑ i ∈ Finset.range 176, stT266 (i+1)) + stT266 177 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 176
    simpa using h
  have hprev := st266_p176
  have hstep := st266_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p178 : ((413530537907/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT266 (i+1))
      = (∑ i ∈ Finset.range 177, stT266 (i+1)) + stT266 178 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 177
    simpa using h
  have hprev := st266_p177
  have hstep := st266_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p179 : ((369218794647/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT266 (i+1))
      = (∑ i ∈ Finset.range 178, stT266 (i+1)) + stT266 179 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 178
    simpa using h
  have hprev := st266_p178
  have hstep := st266_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p180 : ((3039923084791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT266 (i+1))
      = (∑ i ∈ Finset.range 179, stT266 (i+1)) + stT266 180 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 179
    simpa using h
  have hprev := st266_p179
  have hstep := st266_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p181 : ((340810521981/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT266 (i+1))
      = (∑ i ∈ Finset.range 180, stT266 (i+1)) + stT266 181 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 180
    simpa using h
  have hprev := st266_p180
  have hstep := st266_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p182 : ((339658322981/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT266 (i+1))
      = (∑ i ∈ Finset.range 181, stT266 (i+1)) + stT266 182 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 181
    simpa using h
  have hprev := st266_p181
  have hstep := st266_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p183 : ((3028201925607/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT266 (i+1))
      = (∑ i ∈ Finset.range 182, stT266 (i+1)) + stT266 183 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 182
    simpa using h
  have hprev := st266_p182
  have hstep := st266_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p184 : ((369215245989/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT266 (i+1))
      = (∑ i ∈ Finset.range 183, stT266 (i+1)) + stT266 184 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 183
    simpa using h
  have hprev := st266_p183
  have hstep := st266_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p185 : ((3301181531063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT266 (i+1))
      = (∑ i ∈ Finset.range 184, stT266 (i+1)) + stT266 185 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 184
    simpa using h
  have hprev := st266_p184
  have hstep := st266_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p186 : ((433371387151/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT266 (i+1))
      = (∑ i ∈ Finset.range 185, stT266 (i+1)) + stT266 186 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 185
    simpa using h
  have hprev := st266_p185
  have hstep := st266_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p187 : ((6336118472913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT266 (i+1))
      = (∑ i ∈ Finset.range 186, stT266 (i+1)) + stT266 187 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 186
    simpa using h
  have hprev := st266_p186
  have hstep := st266_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p188 : ((182203126859/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT266 (i+1))
      = (∑ i ∈ Finset.range 187, stT266 (i+1)) + stT266 188 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 187
    simpa using h
  have hprev := st266_p187
  have hstep := st266_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p189 : ((97935831793/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT266 (i+1))
      = (∑ i ∈ Finset.range 188, stT266 (i+1)) + stT266 189 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 188
    simpa using h
  have hprev := st266_p188
  have hstep := st266_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p190 : ((863998348503/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT266 (i+1))
      = (∑ i ∈ Finset.range 189, stT266 (i+1)) + stT266 190 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 189
    simpa using h
  have hprev := st266_p189
  have hstep := st266_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p191 : ((6695603854999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT266 (i+1))
      = (∑ i ∈ Finset.range 190, stT266 (i+1)) + stT266 191 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 190
    simpa using h
  have hprev := st266_p190
  have hstep := st266_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p192 : ((1195846506099/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT266 (i+1))
      = (∑ i ∈ Finset.range 191, stT266 (i+1)) + stT266 192 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 191
    simpa using h
  have hprev := st266_p191
  have hstep := st266_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p193 : ((5930926398551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT266 (i+1))
      = (∑ i ∈ Finset.range 192, stT266 (i+1)) + stT266 193 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 192
    simpa using h
  have hprev := st266_p192
  have hstep := st266_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p194 : ((1324824118243/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT266 (i+1))
      = (∑ i ∈ Finset.range 193, stT266 (i+1)) + stT266 194 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 193
    simpa using h
  have hprev := st266_p193
  have hstep := st266_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p195 : ((1389220669693/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT266 (i+1))
      = (∑ i ∈ Finset.range 194, stT266 (i+1)) + stT266 195 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 194
    simpa using h
  have hprev := st266_p194
  have hstep := st266_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p196 : ((6389125982817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT266 (i+1))
      = (∑ i ∈ Finset.range 195, stT266 (i+1)) + stT266 196 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 195
    simpa using h
  have hprev := st266_p195
  have hstep := st266_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p197 : ((182306374963/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT266 (i+1))
      = (∑ i ∈ Finset.range 196, stT266 (i+1)) + stT266 197 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 196
    simpa using h
  have hprev := st266_p196
  have hstep := st266_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p198 : ((6144905749587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT266 (i+1))
      = (∑ i ∈ Finset.range 197, stT266 (i+1)) + stT266 198 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 197
    simpa using h
  have hprev := st266_p197
  have hstep := st266_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p199 : ((854536179983/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT266 (i+1))
      = (∑ i ∈ Finset.range 198, stT266 (i+1)) + stT266 199 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 198
    simpa using h
  have hprev := st266_p198
  have hstep := st266_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p200 : ((684689673697/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT266 (i+1))
      = (∑ i ∈ Finset.range 199, stT266 (i+1)) + stT266 200 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 199
    simpa using h
  have hprev := st266_p199
  have hstep := st266_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p201 : ((1541266919489/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT266 (i+1))
      = (∑ i ∈ Finset.range 200, stT266 (i+1)) + stT266 201 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 200
    simpa using h
  have hprev := st266_p200
  have hstep := st266_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p202 : ((2910817580887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT266 (i+1))
      = (∑ i ∈ Finset.range 201, stT266 (i+1)) + stT266 202 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 201
    simpa using h
  have hprev := st266_p201
  have hstep := st266_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p203 : ((790862763283/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT266 (i+1))
      = (∑ i ∈ Finset.range 202, stT266 (i+1)) + stT266 203 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 202
    simpa using h
  have hprev := st266_p202
  have hstep := st266_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p204 : ((1731841318721/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT266 (i+1))
      = (∑ i ∈ Finset.range 203, stT266 (i+1)) + stT266 204 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 203
    simpa using h
  have hprev := st266_p203
  have hstep := st266_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p205 : ((1685260161607/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT266 (i+1))
      = (∑ i ∈ Finset.range 204, stT266 (i+1)) + stT266 205 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 204
    simpa using h
  have hprev := st266_p204
  have hstep := st266_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p206 : ((755535718051/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT266 (i+1))
      = (∑ i ∈ Finset.range 205, stT266 (i+1)) + stT266 206 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 205
    simpa using h
  have hprev := st266_p205
  have hstep := st266_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p207 : ((5846127969557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT266 (i+1))
      = (∑ i ∈ Finset.range 206, stT266 (i+1)) + stT266 207 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 206
    simpa using h
  have hprev := st266_p206
  have hstep := st266_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p208 : ((3213432447091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT266 (i+1))
      = (∑ i ∈ Finset.range 207, stT266 (i+1)) + stT266 208 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 207
    simpa using h
  have hprev := st266_p207
  have hstep := st266_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p209 : ((1739207641891/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT266 (i+1))
      = (∑ i ∈ Finset.range 208, stT266 (i+1)) + stT266 209 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 208
    simpa using h
  have hprev := st266_p208
  have hstep := st266_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p210 : ((1672531394773/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT266 (i+1))
      = (∑ i ∈ Finset.range 209, stT266 (i+1)) + stT266 210 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 209
    simpa using h
  have hprev := st266_p209
  have hstep := st266_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p211 : ((187638297239/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT266 (i+1))
      = (∑ i ∈ Finset.range 210, stT266 (i+1)) + stT266 211 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 210
    simpa using h
  have hprev := st266_p210
  have hstep := st266_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p212 : ((2926086824501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT266 (i+1))
      = (∑ i ∈ Finset.range 211, stT266 (i+1)) + stT266 212 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 211
    simpa using h
  have hprev := st266_p211
  have hstep := st266_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p213 : ((3219471650123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT266 (i+1))
      = (∑ i ∈ Finset.range 212, stT266 (i+1)) + stT266 213 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 212
    simpa using h
  have hprev := st266_p212
  have hstep := st266_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p214 : ((3480121243453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT266 (i+1))
      = (∑ i ∈ Finset.range 213, stT266 (i+1)) + stT266 214 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 213
    simpa using h
  have hprev := st266_p213
  have hstep := st266_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p215 : ((3355936773903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT266 (i+1))
      = (∑ i ∈ Finset.range 214, stT266 (i+1)) + stT266 215 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 214
    simpa using h
  have hprev := st266_p214
  have hstep := st266_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p216 : ((2945250273/4882812500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT266 (i+1))
      = (∑ i ∈ Finset.range 215, stT266 (i+1)) + stT266 216 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 215
    simpa using h
  have hprev := st266_p215
  have hstep := st266_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p217 : ((5827390189359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT266 (i+1))
      = (∑ i ∈ Finset.range 216, stT266 (i+1)) + stT266 217 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 216
    simpa using h
  have hprev := st266_p216
  have hstep := st266_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p218 : ((6365000058379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT266 (i+1))
      = (∑ i ∈ Finset.range 217, stT266 (i+1)) + stT266 218 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 217
    simpa using h
  have hprev := st266_p217
  have hstep := st266_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p219 : ((1387233081231/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT266 (i+1))
      = (∑ i ∈ Finset.range 218, stT266 (i+1)) + stT266 219 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 218
    simpa using h
  have hprev := st266_p218
  have hstep := st266_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p220 : ((1359814311111/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT266 (i+1))
      = (∑ i ∈ Finset.range 219, stT266 (i+1)) + stT266 220 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 219
    simpa using h
  have hprev := st266_p219
  have hstep := st266_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p221 : ((766865753897/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT266 (i+1))
      = (∑ i ∈ Finset.range 220, stT266 (i+1)) + stT266 221 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 220
    simpa using h
  have hprev := st266_p220
  have hstep := st266_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p222 : ((5795816574199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT266 (i+1))
      = (∑ i ∈ Finset.range 221, stT266 (i+1)) + stT266 222 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 221
    simpa using h
  have hprev := st266_p221
  have hstep := st266_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p223 : ((388091381859/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT266 (i+1))
      = (∑ i ∈ Finset.range 222, stT266 (i+1)) + stT266 223 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 222
    simpa using h
  have hprev := st266_p222
  have hstep := st266_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p224 : ((6850582307517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT266 (i+1))
      = (∑ i ∈ Finset.range 223, stT266 (i+1)) + stT266 224 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 223
    simpa using h
  have hprev := st266_p223
  have hstep := st266_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p225 : ((6917551573881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT266 (i+1))
      = (∑ i ∈ Finset.range 224, stT266 (i+1)) + stT266 225 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 224
    simpa using h
  have hprev := st266_p224
  have hstep := st266_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p226 : ((3165593851477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT266 (i+1))
      = (∑ i ∈ Finset.range 225, stT266 (i+1)) + stT266 226 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 225
    simpa using h
  have hprev := st266_p225
  have hstep := st266_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p227 : ((2908057656169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT266 (i+1))
      = (∑ i ∈ Finset.range 226, stT266 (i+1)) + stT266 227 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 226
    simpa using h
  have hprev := st266_p226
  have hstep := st266_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p228 : ((1499928001047/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT266 (i+1))
      = (∑ i ∈ Finset.range 227, stT266 (i+1)) + stT266 228 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 227
    simpa using h
  have hprev := st266_p227
  have hstep := st266_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p229 : ((415955111727/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT266 (i+1))
      = (∑ i ∈ Finset.range 228, stT266 (i+1)) + stT266 229 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 228
    simpa using h
  have hprev := st266_p228
  have hstep := st266_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p230 : ((218525904991/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT266 (i+1))
      = (∑ i ∈ Finset.range 229, stT266 (i+1)) + stT266 230 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 229
    simpa using h
  have hprev := st266_p229
  have hstep := st266_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p231 : ((206636136643/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT266 (i+1))
      = (∑ i ∈ Finset.range 230, stT266 (i+1)) + stT266 231 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 230
    simpa using h
  have hprev := st266_p230
  have hstep := st266_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p232 : ((746025369853/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT266 (i+1))
      = (∑ i ∈ Finset.range 231, stT266 (i+1)) + stT266 232 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 231
    simpa using h
  have hprev := st266_p231
  have hstep := st266_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p233 : ((727197163573/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT266 (i+1))
      = (∑ i ∈ Finset.range 232, stT266 (i+1)) + stT266 233 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 232
    simpa using h
  have hprev := st266_p232
  have hstep := st266_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p234 : ((791569462263/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT266 (i+1))
      = (∑ i ∈ Finset.range 233, stT266 (i+1)) + stT266 234 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 233
    simpa using h
  have hprev := st266_p233
  have hstep := st266_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p235 : ((216058905341/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT266 (i+1))
      = (∑ i ∈ Finset.range 234, stT266 (i+1)) + stT266 235 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 234
    simpa using h
  have hprev := st266_p234
  have hstep := st266_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p236 : ((6894647593327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT266 (i+1))
      = (∑ i ∈ Finset.range 235, stT266 (i+1)) + stT266 236 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 235
    simpa using h
  have hprev := st266_p235
  have hstep := st266_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p237 : ((6300592443807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT266 (i+1))
      = (∑ i ∈ Finset.range 236, stT266 (i+1)) + stT266 237 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 236
    simpa using h
  have hprev := st266_p236
  have hstep := st266_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p238 : ((5806222161699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT266 (i+1))
      = (∑ i ∈ Finset.range 237, stT266 (i+1)) + stT266 238 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 237
    simpa using h
  have hprev := st266_p237
  have hstep := st266_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p239 : ((5964935530489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT266 (i+1))
      = (∑ i ∈ Finset.range 238, stT266 (i+1)) + stT266 239 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 238
    simpa using h
  have hprev := st266_p238
  have hstep := st266_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p240 : ((6595923048923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT266 (i+1))
      = (∑ i ∈ Finset.range 239, stT266 (i+1)) + stT266 240 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 239
    simpa using h
  have hprev := st266_p239
  have hstep := st266_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p241 : ((1399881510347/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT266 (i+1))
      = (∑ i ∈ Finset.range 240, stT266 (i+1)) + stT266 241 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 240
    simpa using h
  have hprev := st266_p240
  have hstep := st266_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p242 : ((1346924558327/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT266 (i+1))
      = (∑ i ∈ Finset.range 241, stT266 (i+1)) + stT266 242 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 241
    simpa using h
  have hprev := st266_p241
  have hstep := st266_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p243 : ((1218774469561/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT266 (i+1))
      = (∑ i ∈ Finset.range 242, stT266 (i+1)) + stT266 243 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 242
    simpa using h
  have hprev := st266_p242
  have hstep := st266_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p244 : ((57714284483/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT266 (i+1))
      = (∑ i ∈ Finset.range 243, stT266 (i+1)) + stT266 244 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 243
    simpa using h
  have hprev := st266_p243
  have hstep := st266_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p245 : ((1527708469701/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT266 (i+1))
      = (∑ i ∈ Finset.range 244, stT266 (i+1)) + stT266 245 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 244
    simpa using h
  have hprev := st266_p244
  have hstep := st266_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p246 : ((1686671627719/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT266 (i+1))
      = (∑ i ∈ Finset.range 245, stT266 (i+1)) + stT266 246 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 245
    simpa using h
  have hprev := st266_p245
  have hstep := st266_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p247 : ((875678527257/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT266 (i+1))
      = (∑ i ∈ Finset.range 246, stT266 (i+1)) + stT266 247 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 246
    simpa using h
  have hprev := st266_p246
  have hstep := st266_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p248 : ((6618120153123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT266 (i+1))
      = (∑ i ∈ Finset.range 247, stT266 (i+1)) + stT266 248 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 247
    simpa using h
  have hprev := st266_p247
  have hstep := st266_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p249 : ((5992012527623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT266 (i+1))
      = (∑ i ∈ Finset.range 248, stT266 (i+1)) + stT266 249 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 248
    simpa using h
  have hprev := st266_p248
  have hstep := st266_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p250 : ((5775639210727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT266 (i+1))
      = (∑ i ∈ Finset.range 249, stT266 (i+1)) + stT266 250 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 249
    simpa using h
  have hprev := st266_p249
  have hstep := st266_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p251 : ((1237671858779/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT266 (i+1))
      = (∑ i ∈ Finset.range 250, stT266 (i+1)) + stT266 251 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 250
    simpa using h
  have hprev := st266_p250
  have hstep := st266_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p252 : ((1361152067639/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT266 (i+1))
      = (∑ i ∈ Finset.range 251, stT266 (i+1)) + stT266 252 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 251
    simpa using h
  have hprev := st266_p251
  have hstep := st266_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p253 : ((7002137309953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT266 (i+1))
      = (∑ i ∈ Finset.range 252, stT266 (i+1)) + stT266 253 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 252
    simpa using h
  have hprev := st266_p252
  have hstep := st266_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p254 : ((6582931446529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT266 (i+1))
      = (∑ i ∈ Finset.range 253, stT266 (i+1)) + stT266 254 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 253
    simpa using h
  have hprev := st266_p253
  have hstep := st266_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p255 : ((1492478539501/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT266 (i+1))
      = (∑ i ∈ Finset.range 254, stT266 (i+1)) + stT266 255 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 254
    simpa using h
  have hprev := st266_p254
  have hstep := st266_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p256 : ((5771078214867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT266 (i+1))
      = (∑ i ∈ Finset.range 255, stT266 (i+1)) + stT266 256 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 255
    simpa using h
  have hprev := st266_p255
  have hstep := st266_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p257 : ((6179215658557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT266 (i+1))
      = (∑ i ∈ Finset.range 256, stT266 (i+1)) + stT266 257 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 256
    simpa using h
  have hprev := st266_p256
  have hstep := st266_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p258 : ((1358438017721/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT266 (i+1))
      = (∑ i ∈ Finset.range 257, stT266 (i+1)) + stT266 258 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 257
    simpa using h
  have hprev := st266_p257
  have hstep := st266_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p259 : ((3507339047057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT266 (i+1))
      = (∑ i ∈ Finset.range 258, stT266 (i+1)) + stT266 259 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 258
    simpa using h
  have hprev := st266_p258
  have hstep := st266_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p260 : ((1658747396567/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT266 (i+1))
      = (∑ i ∈ Finset.range 259, stT266 (i+1)) + stT266 260 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 259
    simpa using h
  have hprev := st266_p259
  have hstep := st266_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p261 : ((752457074721/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT266 (i+1))
      = (∑ i ∈ Finset.range 260, stT266 (i+1)) + stT266 261 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 260
    simpa using h
  have hprev := st266_p260
  have hstep := st266_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p262 : ((5753995747541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT266 (i+1))
      = (∑ i ∈ Finset.range 261, stT266 (i+1)) + stT266 262 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 261
    simpa using h
  have hprev := st266_p261
  have hstep := st266_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p263 : ((6086133942929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT266 (i+1))
      = (∑ i ∈ Finset.range 262, stT266 (i+1)) + stT266 263 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 262
    simpa using h
  have hprev := st266_p262
  have hstep := st266_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p264 : ((3350771160913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT266 (i+1))
      = (∑ i ∈ Finset.range 263, stT266 (i+1)) + stT266 264 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 263
    simpa using h
  have hprev := st266_p263
  have hstep := st266_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p265 : ((7026540620231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT266 (i+1))
      = (∑ i ∈ Finset.range 264, stT266 (i+1)) + stT266 265 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 264
    simpa using h
  have hprev := st266_p264
  have hstep := st266_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p266 : ((6762944989691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT266 (i+1))
      = (∑ i ∈ Finset.range 265, stT266 (i+1)) + stT266 266 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 265
    simpa using h
  have hprev := st266_p265
  have hstep := st266_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p267 : ((1538989254029/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT266 (i+1))
      = (∑ i ∈ Finset.range 266, stT266 (i+1)) + stT266 267 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 266
    simpa using h
  have hprev := st266_p266
  have hstep := st266_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p268 : ((288009521473/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT266 (i+1))
      = (∑ i ∈ Finset.range 267, stT266 (i+1)) + stT266 268 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 267
    simpa using h
  have hprev := st266_p267
  have hstep := st266_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p269 : ((593213169801/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT266 (i+1))
      = (∑ i ∈ Finset.range 268, stT266 (i+1)) + stT266 269 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 268
    simpa using h
  have hprev := st266_p268
  have hstep := st266_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p270 : ((651388670877/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT266 (i+1))
      = (∑ i ∈ Finset.range 269, stT266 (i+1)) + stT266 270 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 269
    simpa using h
  have hprev := st266_p269
  have hstep := st266_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p271 : ((3492038241953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT266 (i+1))
      = (∑ i ∈ Finset.range 270, stT266 (i+1)) + stT266 271 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 270
    simpa using h
  have hprev := st266_p270
  have hstep := st266_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p272 : ((3463425360523/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT266 (i+1))
      = (∑ i ∈ Finset.range 271, stT266 (i+1)) + stT266 272 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 271
    simpa using h
  have hprev := st266_p271
  have hstep := st266_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p273 : ((3197868563121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT266 (i+1))
      = (∑ i ∈ Finset.range 272, stT266 (i+1)) + stT266 273 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 272
    simpa using h
  have hprev := st266_p272
  have hstep := st266_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p274 : ((1464438076009/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT266 (i+1))
      = (∑ i ∈ Finset.range 273, stT266 (i+1)) + stT266 274 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 273
    simpa using h
  have hprev := st266_p273
  have hstep := st266_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p275 : ((5779926758679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT266 (i+1))
      = (∑ i ∈ Finset.range 274, stT266 (i+1)) + stT266 275 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 274
    simpa using h
  have hprev := st266_p274
  have hstep := st266_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p276 : ((3113285960523/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT266 (i+1))
      = (∑ i ∈ Finset.range 275, stT266 (i+1)) + stT266 276 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 275
    simpa using h
  have hprev := st266_p275
  have hstep := st266_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p277 : ((6811914227451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT266 (i+1))
      = (∑ i ∈ Finset.range 276, stT266 (i+1)) + stT266 277 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 276
    simpa using h
  have hprev := st266_p276
  have hstep := st266_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p278 : ((7037038341771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT266 (i+1))
      = (∑ i ∈ Finset.range 277, stT266 (i+1)) + stT266 278 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 277
    simpa using h
  have hprev := st266_p277
  have hstep := st266_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p279 : ((6713805915531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT266 (i+1))
      = (∑ i ∈ Finset.range 278, stT266 (i+1)) + stT266 279 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 278
    simpa using h
  have hprev := st266_p278
  have hstep := st266_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p280 : ((3058436397123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT266 (i+1))
      = (∑ i ∈ Finset.range 279, stT266 (i+1)) + stT266 280 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 279
    simpa using h
  have hprev := st266_p279
  have hstep := st266_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p281 : ((2872889064423/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT266 (i+1))
      = (∑ i ∈ Finset.range 280, stT266 (i+1)) + stT266 281 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 280
    simpa using h
  have hprev := st266_p280
  have hstep := st266_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p282 : ((1476665483079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT266 (i+1))
      = (∑ i ∈ Finset.range 281, stT266 (i+1)) + stT266 282 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 281
    simpa using h
  have hprev := st266_p281
  have hstep := st266_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p283 : ((1615970839503/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT266 (i+1))
      = (∑ i ∈ Finset.range 282, stT266 (i+1)) + stT266 283 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 282
    simpa using h
  have hprev := st266_p282
  have hstep := st266_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p284 : ((869915308839/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT266 (i+1))
      = (∑ i ∈ Finset.range 283, stT266 (i+1)) + stT266 284 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 283
    simpa using h
  have hprev := st266_p283
  have hstep := st266_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p285 : ((436921954431/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT266 (i+1))
      = (∑ i ∈ Finset.range 284, stT266 (i+1)) + stT266 285 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 284
    simpa using h
  have hprev := st266_p284
  have hstep := st266_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p286 : ((1307101415853/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT266 (i+1))
      = (∑ i ∈ Finset.range 285, stT266 (i+1)) + stT266 286 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 285
    simpa using h
  have hprev := st266_p285
  have hstep := st266_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p287 : ((5961590057433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT266 (i+1))
      = (∑ i ∈ Finset.range 286, stT266 (i+1)) + stT266 287 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 286
    simpa using h
  have hprev := st266_p286
  have hstep := st266_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p288 : ((5727023743001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT266 (i+1))
      = (∑ i ∈ Finset.range 287, stT266 (i+1)) + stT266 288 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 287
    simpa using h
  have hprev := st266_p287
  have hstep := st266_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p289 : ((6015516539931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT266 (i+1))
      = (∑ i ∈ Finset.range 288, stT266 (i+1)) + stT266 289 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 288
    simpa using h
  have hprev := st266_p288
  have hstep := st266_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p290 : ((6597018778791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT266 (i+1))
      = (∑ i ∈ Finset.range 289, stT266 (i+1)) + stT266 290 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 289
    simpa using h
  have hprev := st266_p289
  have hstep := st266_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p291 : ((7015236820461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT266 (i+1))
      = (∑ i ∈ Finset.range 290, stT266 (i+1)) + stT266 291 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 290
    simpa using h
  have hprev := st266_p290
  have hstep := st266_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p292 : ((6946259759653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT266 (i+1))
      = (∑ i ∈ Finset.range 291, stT266 (i+1)) + stT266 292 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 291
    simpa using h
  have hprev := st266_p291
  have hstep := st266_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p293 : ((6446145852061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT266 (i+1))
      = (∑ i ∈ Finset.range 292, stT266 (i+1)) + stT266 293 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 292
    simpa using h
  have hprev := st266_p292
  have hstep := st266_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p294 : ((5900906202169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT266 (i+1))
      = (∑ i ∈ Finset.range 293, stT266 (i+1)) + stT266 294 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 293
    simpa using h
  have hprev := st266_p293
  have hstep := st266_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p295 : ((5726271906657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT266 (i+1))
      = (∑ i ∈ Finset.range 294, stT266 (i+1)) + stT266 295 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 294
    simpa using h
  have hprev := st266_p294
  have hstep := st266_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p296 : ((6052315619043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT266 (i+1))
      = (∑ i ∈ Finset.range 295, stT266 (i+1)) + stT266 296 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 295
    simpa using h
  have hprev := st266_p295
  have hstep := st266_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p297 : ((265231085611/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT266 (i+1))
      = (∑ i ∈ Finset.range 296, stT266 (i+1)) + stT266 297 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 296
    simpa using h
  have hprev := st266_p296
  have hstep := st266_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p298 : ((7027623754451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT266 (i+1))
      = (∑ i ∈ Finset.range 297, stT266 (i+1)) + stT266 298 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 297
    simpa using h
  have hprev := st266_p297
  have hstep := st266_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p299 : ((3474487903013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT266 (i+1))
      = (∑ i ∈ Finset.range 298, stT266 (i+1)) + stT266 299 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 298
    simpa using h
  have hprev := st266_p298
  have hstep := st266_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p300 : ((3227811224157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT266 (i+1))
      = (∑ i ∈ Finset.range 299, stT266 (i+1)) + stT266 300 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 299
    simpa using h
  have hprev := st266_p299
  have hstep := st266_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p301 : ((5911989478017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT266 (i+1))
      = (∑ i ∈ Finset.range 300, stT266 (i+1)) + stT266 301 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 300
    simpa using h
  have hprev := st266_p300
  have hstep := st266_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p302 : ((5714853160521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT266 (i+1))
      = (∑ i ∈ Finset.range 301, stT266 (i+1)) + stT266 302 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 301
    simpa using h
  have hprev := st266_p301
  have hstep := st266_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p303 : ((6005110627037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT266 (i+1))
      = (∑ i ∈ Finset.range 302, stT266 (i+1)) + stT266 303 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 302
    simpa using h
  have hprev := st266_p302
  have hstep := st266_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p304 : ((6570866702807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT266 (i+1))
      = (∑ i ∈ Finset.range 303, stT266 (i+1)) + stT266 304 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 303
    simpa using h
  have hprev := st266_p303
  have hstep := st266_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p305 : ((56043821971/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT266 (i+1))
      = (∑ i ∈ Finset.range 304, stT266 (i+1)) + stT266 305 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 304
    simpa using h
  have hprev := st266_p304
  have hstep := st266_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p306 : ((7000391669561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT266 (i+1))
      = (∑ i ∈ Finset.range 305, stT266 (i+1)) + stT266 306 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 305
    simpa using h
  have hprev := st266_p305
  have hstep := st266_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p307 : ((209973811/320000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT266 (i+1))
      = (∑ i ∈ Finset.range 306, stT266 (i+1)) + stT266 307 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 306
    simpa using h
  have hprev := st266_p306
  have hstep := st266_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p308 : ((3000077206261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT266 (i+1))
      = (∑ i ∈ Finset.range 307, stT266 (i+1)) + stT266 308 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 307
    simpa using h
  have hprev := st266_p307
  have hstep := st266_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p309 : ((713600535487/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT266 (i+1))
      = (∑ i ∈ Finset.range 308, stT266 (i+1)) + stT266 309 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 308
    simpa using h
  have hprev := st266_p308
  have hstep := st266_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p310 : ((5888420246263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT266 (i+1))
      = (∑ i ∈ Finset.range 309, stT266 (i+1)) + stT266 310 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 309
    simpa using h
  have hprev := st266_p309
  have hstep := st266_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p311 : ((1603092209757/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT266 (i+1))
      = (∑ i ∈ Finset.range 310, stT266 (i+1)) + stT266 311 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 310
    simpa using h
  have hprev := st266_p310
  have hstep := st266_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p312 : ((432450950393/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT266 (i+1))
      = (∑ i ∈ Finset.range 311, stT266 (i+1)) + stT266 312 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 311
    simpa using h
  have hprev := st266_p311
  have hstep := st266_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p313 : ((1412675463541/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT266 (i+1))
      = (∑ i ∈ Finset.range 312, stT266 (i+1)) + stT266 313 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 312
    simpa using h
  have hprev := st266_p312
  have hstep := st266_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p314 : ((1687281134081/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT266 (i+1))
      = (∑ i ∈ Finset.range 313, stT266 (i+1)) + stT266 314 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 313
    simpa using h
  have hprev := st266_p313
  have hstep := st266_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p315 : ((1547686236709/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT266 (i+1))
      = (∑ i ∈ Finset.range 314, stT266 (i+1)) + stT266 315 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 314
    simpa using h
  have hprev := st266_p314
  have hstep := st266_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p316 : ((1440903009541/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT266 (i+1))
      = (∑ i ∈ Finset.range 315, stT266 (i+1)) + stT266 316 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 315
    simpa using h
  have hprev := st266_p315
  have hstep := st266_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p317 : ((287569407849/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT266 (i+1))
      = (∑ i ∈ Finset.range 316, stT266 (i+1)) + stT266 317 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 316
    simpa using h
  have hprev := st266_p316
  have hstep := st266_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p318 : ((76998286167/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT266 (i+1))
      = (∑ i ∈ Finset.range 317, stT266 (i+1)) + stT266 318 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 317
    simpa using h
  have hprev := st266_p317
  have hstep := st266_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p319 : ((839739386031/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT266 (i+1))
      = (∑ i ∈ Finset.range 318, stT266 (i+1)) + stT266 319 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 318
    simpa using h
  have hprev := st266_p318
  have hstep := st266_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p320 : ((882457152687/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT266 (i+1))
      = (∑ i ∈ Finset.range 319, stT266 (i+1)) + stT266 320 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 319
    simpa using h
  have hprev := st266_p319
  have hstep := st266_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p321 : ((3482003033519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT266 (i+1))
      = (∑ i ∈ Finset.range 320, stT266 (i+1)) + stT266 321 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 320
    simpa using h
  have hprev := st266_p320
  have hstep := st266_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p322 : ((129903656963/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT266 (i+1))
      = (∑ i ∈ Finset.range 321, stT266 (i+1)) + stT266 322 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 321
    simpa using h
  have hprev := st266_p321
  have hstep := st266_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p323 : ((1191306056839/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT266 (i+1))
      = (∑ i ∈ Finset.range 322, stT266 (i+1)) + stT266 323 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 322
    simpa using h
  have hprev := st266_p322
  have hstep := st266_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p324 : ((5692604517499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT266 (i+1))
      = (∑ i ∈ Finset.range 323, stT266 (i+1)) + stT266 324 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 323
    simpa using h
  have hprev := st266_p323
  have hstep := st266_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p325 : ((5869552153399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT266 (i+1))
      = (∑ i ∈ Finset.range 324, stT266 (i+1)) + stT266 325 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 324
    simpa using h
  have hprev := st266_p324
  have hstep := st266_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p326 : ((254928572983/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT266 (i+1))
      = (∑ i ∈ Finset.range 325, stT266 (i+1)) + stT266 326 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 325
    simpa using h
  have hprev := st266_p325
  have hstep := st266_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p327 : ((6885533253009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT266 (i+1))
      = (∑ i ∈ Finset.range 326, stT266 (i+1)) + stT266 327 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 326
    simpa using h
  have hprev := st266_p326
  have hstep := st266_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p328 : ((442911092613/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT266 (i+1))
      = (∑ i ∈ Finset.range 327, stT266 (i+1)) + stT266 328 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 327
    simpa using h
  have hprev := st266_p327
  have hstep := st266_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p329 : ((171330445101/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT266 (i+1))
      = (∑ i ∈ Finset.range 328, stT266 (i+1)) + stT266 329 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 328
    simpa using h
  have hprev := st266_p328
  have hstep := st266_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p330 : ((1582947836241/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT266 (i+1))
      = (∑ i ∈ Finset.range 329, stT266 (i+1)) + stT266 330 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 329
    simpa using h
  have hprev := st266_p329
  have hstep := st266_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p331 : ((2921901365457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT266 (i+1))
      = (∑ i ∈ Finset.range 330, stT266 (i+1)) + stT266 331 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 330
    simpa using h
  have hprev := st266_p330
  have hstep := st266_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p332 : ((2843405001263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT266 (i+1))
      = (∑ i ∈ Finset.range 331, stT266 (i+1)) + stT266 332 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 331
    simpa using h
  have hprev := st266_p331
  have hstep := st266_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p333 : ((2977136575113/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT266 (i+1))
      = (∑ i ∈ Finset.range 332, stT266 (i+1)) + stT266 333 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 332
    simpa using h
  have hprev := st266_p332
  have hstep := st266_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p334 : ((810321189797/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT266 (i+1))
      = (∑ i ∈ Finset.range 333, stT266 (i+1)) + stT266 334 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 333
    simpa using h
  have hprev := st266_p333
  have hstep := st266_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p335 : ((3476698128333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT266 (i+1))
      = (∑ i ∈ Finset.range 334, stT266 (i+1)) + stT266 335 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 334
    simpa using h
  have hprev := st266_p334
  have hstep := st266_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p336 : ((3543105835593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT266 (i+1))
      = (∑ i ∈ Finset.range 335, stT266 (i+1)) + stT266 336 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 335
    simpa using h
  have hprev := st266_p335
  have hstep := st266_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p337 : ((1701001836639/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT266 (i+1))
      = (∑ i ∈ Finset.range 336, stT266 (i+1)) + stT266 337 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 336
    simpa using h
  have hprev := st266_p336
  have hstep := st266_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p338 : ((6275402458273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT266 (i+1))
      = (∑ i ∈ Finset.range 337, stT266 (i+1)) + stT266 338 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 337
    simpa using h
  have hprev := st266_p337
  have hstep := st266_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p339 : ((5811695057623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT266 (i+1))
      = (∑ i ∈ Finset.range 338, stT266 (i+1)) + stT266 339 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 338
    simpa using h
  have hprev := st266_p338
  have hstep := st266_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p340 : ((5682969405557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT266 (i+1))
      = (∑ i ∈ Finset.range 339, stT266 (i+1)) + stT266 340 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 339
    simpa using h
  have hprev := st266_p339
  have hstep := st266_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p341 : ((5962102668647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT266 (i+1))
      = (∑ i ∈ Finset.range 340, stT266 (i+1)) + stT266 341 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 340
    simpa using h
  have hprev := st266_p340
  have hstep := st266_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p342 : ((6485966939357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT266 (i+1))
      = (∑ i ∈ Finset.range 341, stT266 (i+1)) + stT266 342 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 341
    simpa using h
  have hprev := st266_p341
  have hstep := st266_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p343 : ((6952800365369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT266 (i+1))
      = (∑ i ∈ Finset.range 342, stT266 (i+1)) + stT266 343 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 342
    simpa using h
  have hprev := st266_p342
  have hstep := st266_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p344 : ((7096611312359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT266 (i+1))
      = (∑ i ∈ Finset.range 343, stT266 (i+1)) + stT266 344 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 343
    simpa using h
  have hprev := st266_p343
  have hstep := st266_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p345 : ((6837481056793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT266 (i+1))
      = (∑ i ∈ Finset.range 344, stT266 (i+1)) + stT266 345 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 344
    simpa using h
  have hprev := st266_p344
  have hstep := st266_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p346 : ((6323674097853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT266 (i+1))
      = (∑ i ∈ Finset.range 345, stT266 (i+1)) + stT266 346 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 345
    simpa using h
  have hprev := st266_p345
  have hstep := st266_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p347 : ((2922375078969/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT266 (i+1))
      = (∑ i ∈ Finset.range 346, stT266 (i+1)) + stT266 347 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 346
    simpa using h
  have hprev := st266_p346
  have hstep := st266_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p348 : ((5667740384139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT266 (i+1))
      = (∑ i ∈ Finset.range 347, stT266 (i+1)) + stT266 348 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 347
    simpa using h
  have hprev := st266_p347
  have hstep := st266_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p349 : ((2944654527807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT266 (i+1))
      = (∑ i ∈ Finset.range 348, stT266 (i+1)) + stT266 349 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 348
    simpa using h
  have hprev := st266_p348
  have hstep := st266_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p350 : ((1596274229721/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT266 (i+1))
      = (∑ i ∈ Finset.range 349, stT266 (i+1)) + stT266 350 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 349
    simpa using h
  have hprev := st266_p349
  have hstep := st266_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p351 : ((1720384371801/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT266 (i+1))
      = (∑ i ∈ Finset.range 350, stT266 (i+1)) + stT266 351 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 350
    simpa using h
  have hprev := st266_p350
  have hstep := st266_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p352 : ((7107585876309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT266 (i+1))
      = (∑ i ∈ Finset.range 351, stT266 (i+1)) + stT266 352 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 351
    simpa using h
  have hprev := st266_p351
  have hstep := st266_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p353 : ((1735464366671/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT266 (i+1))
      = (∑ i ∈ Finset.range 352, stT266 (i+1)) + stT266 353 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 352
    simpa using h
  have hprev := st266_p352
  have hstep := st266_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p354 : ((3237919730857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT266 (i+1))
      = (∑ i ∈ Finset.range 353, stT266 (i+1)) + stT266 354 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 353
    simpa using h
  have hprev := st266_p353
  have hstep := st266_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p355 : ((5961385679489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT266 (i+1))
      = (∑ i ∈ Finset.range 354, stT266 (i+1)) + stT266 355 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 354
    simpa using h
  have hprev := st266_p354
  have hstep := st266_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p356 : ((2836802086237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT266 (i+1))
      = (∑ i ∈ Finset.range 355, stT266 (i+1)) + stT266 356 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 355
    simpa using h
  have hprev := st266_p355
  have hstep := st266_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p357 : ((2882133656521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT266 (i+1))
      = (∑ i ∈ Finset.range 356, stT266 (i+1)) + stT266 357 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 356
    simpa using h
  have hprev := st266_p356
  have hstep := st266_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p358 : ((3091763978503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT266 (i+1))
      = (∑ i ∈ Finset.range 357, stT266 (i+1)) + stT266 358 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 357
    simpa using h
  have hprev := st266_p357
  have hstep := st266_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p359 : ((6709263924497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT266 (i+1))
      = (∑ i ∈ Finset.range 358, stT266 (i+1)) + stT266 359 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 358
    simpa using h
  have hprev := st266_p358
  have hstep := st266_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p360 : ((7065948102503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT266 (i+1))
      = (∑ i ∈ Finset.range 359, stT266 (i+1)) + stT266 360 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 359
    simpa using h
  have hprev := st266_p359
  have hstep := st266_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p361 : ((27612698163/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT266 (i+1))
      = (∑ i ∈ Finset.range 360, stT266 (i+1)) + stT266 361 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 360
    simpa using h
  have hprev := st266_p360
  have hstep := st266_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p362 : ((6718219270459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT266 (i+1))
      = (∑ i ∈ Finset.range 361, stT266 (i+1)) + stT266 362 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 361
    simpa using h
  have hprev := st266_p361
  have hstep := st266_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p363 : ((6196316028283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT266 (i+1))
      = (∑ i ∈ Finset.range 362, stT266 (i+1)) + stT266 363 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 362
    simpa using h
  have hprev := st266_p362
  have hstep := st266_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p364 : ((90175587933/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT266 (i+1))
      = (∑ i ∈ Finset.range 363, stT266 (i+1)) + stT266 364 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 363
    simpa using h
  have hprev := st266_p363
  have hstep := st266_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p365 : ((88422346531/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT266 (i+1))
      = (∑ i ∈ Finset.range 364, stT266 (i+1)) + stT266 365 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 364
    simpa using h
  have hprev := st266_p364
  have hstep := st266_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p366 : ((1478747327179/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT266 (i+1))
      = (∑ i ∈ Finset.range 365, stT266 (i+1)) + stT266 366 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 365
    simpa using h
  have hprev := st266_p365
  have hstep := st266_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p367 : ((6408242742021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT266 (i+1))
      = (∑ i ∈ Finset.range 366, stT266 (i+1)) + stT266 367 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 366
    simpa using h
  have hprev := st266_p366
  have hstep := st266_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p368 : ((6890244629061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT266 (i+1))
      = (∑ i ∈ Finset.range 367, stT266 (i+1)) + stT266 368 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 367
    simpa using h
  have hprev := st266_p367
  have hstep := st266_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p369 : ((3560285581779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT266 (i+1))
      = (∑ i ∈ Finset.range 368, stT266 (i+1)) + stT266 369 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 368
    simpa using h
  have hprev := st266_p368
  have hstep := st266_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p370 : ((3493064315289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT266 (i+1))
      = (∑ i ∈ Finset.range 369, stT266 (i+1)) + stT266 370 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 369
    simpa using h
  have hprev := st266_p369
  have hstep := st266_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p371 : ((819385707941/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT266 (i+1))
      = (∑ i ∈ Finset.range 370, stT266 (i+1)) + stT266 371 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 370
    simpa using h
  have hprev := st266_p370
  have hstep := st266_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p372 : ((1510152167229/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT266 (i+1))
      = (∑ i ∈ Finset.range 371, stT266 (i+1)) + stT266 372 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 371
    simpa using h
  have hprev := st266_p371
  have hstep := st266_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p373 : ((284725778201/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT266 (i+1))
      = (∑ i ∈ Finset.range 372, stT266 (i+1)) + stT266 373 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 372
    simpa using h
  have hprev := st266_p372
  have hstep := st266_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p374 : ((1421056766021/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT266 (i+1))
      = (∑ i ∈ Finset.range 373, stT266 (i+1)) + stT266 374 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 373
    simpa using h
  have hprev := st266_p373
  have hstep := st266_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p375 : ((6013086747579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT266 (i+1))
      = (∑ i ∈ Finset.range 374, stT266 (i+1)) + stT266 375 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 374
    simpa using h
  have hprev := st266_p374
  have hstep := st266_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p376 : ((6521164755289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT266 (i+1))
      = (∑ i ∈ Finset.range 375, stT266 (i+1)) + stT266 376 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 375
    simpa using h
  have hprev := st266_p375
  have hstep := st266_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p377 : ((6964321452119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT266 (i+1))
      = (∑ i ∈ Finset.range 376, stT266 (i+1)) + stT266 377 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 376
    simpa using h
  have hprev := st266_p376
  have hstep := st266_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p378 : ((7131756883127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT266 (i+1))
      = (∑ i ∈ Finset.range 377, stT266 (i+1)) + stT266 378 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 377
    simpa using h
  have hprev := st266_p377
  have hstep := st266_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p379 : ((6945420432299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT266 (i+1))
      = (∑ i ∈ Finset.range 378, stT266 (i+1)) + stT266 379 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 378
    simpa using h
  have hprev := st266_p378
  have hstep := st266_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p380 : ((6494887990779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT266 (i+1))
      = (∑ i ∈ Finset.range 379, stT266 (i+1)) + stT266 380 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 379
    simpa using h
  have hprev := st266_p379
  have hstep := st266_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p381 : ((5992795256559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT266 (i+1))
      = (∑ i ∈ Finset.range 380, stT266 (i+1)) + stT266 381 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 380
    simpa using h
  have hprev := st266_p380
  have hstep := st266_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p382 : ((5673775389449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT266 (i+1))
      = (∑ i ∈ Finset.range 381, stT266 (i+1)) + stT266 382 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 381
    simpa using h
  have hprev := st266_p381
  have hstep := st266_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p383 : ((5685109859081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT266 (i+1))
      = (∑ i ∈ Finset.range 382, stT266 (i+1)) + stT266 383 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 382
    simpa using h
  have hprev := st266_p382
  have hstep := st266_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p384 : ((6019981915111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT266 (i+1))
      = (∑ i ∈ Finset.range 383, stT266 (i+1)) + stT266 384 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 383
    simpa using h
  have hprev := st266_p383
  have hstep := st266_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p385 : ((6522837359189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT266 (i+1))
      = (∑ i ∈ Finset.range 384, stT266 (i+1)) + stT266 385 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 384
    simpa using h
  have hprev := st266_p384
  have hstep := st266_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p386 : ((6962770246541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT266 (i+1))
      = (∑ i ∈ Finset.range 385, stT266 (i+1)) + stT266 386 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 385
    simpa using h
  have hprev := st266_p385
  have hstep := st266_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p387 : ((7139767514501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT266 (i+1))
      = (∑ i ∈ Finset.range 386, stT266 (i+1)) + stT266 387 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 386
    simpa using h
  have hprev := st266_p386
  have hstep := st266_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p388 : ((1394973070699/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT266 (i+1))
      = (∑ i ∈ Finset.range 387, stT266 (i+1)) + stT266 388 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 387
    simpa using h
  have hprev := st266_p387
  have hstep := st266_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p389 : ((3272007312673/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT266 (i+1))
      = (∑ i ∈ Finset.range 388, stT266 (i+1)) + stT266 389 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 388
    simpa using h
  have hprev := st266_p388
  have hstep := st266_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p390 : ((3020867541103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT266 (i+1))
      = (∑ i ∈ Finset.range 389, stT266 (i+1)) + stT266 390 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 389
    simpa using h
  have hprev := st266_p389
  have hstep := st266_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p391 : ((1423139958257/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT266 (i+1))
      = (∑ i ∈ Finset.range 390, stT266 (i+1)) + stT266 391 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 390
    simpa using h
  have hprev := st266_p390
  have hstep := st266_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p392 : ((5650864211447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT266 (i+1))
      = (∑ i ∈ Finset.range 391, stT266 (i+1)) + stT266 392 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 391
    simpa using h
  have hprev := st266_p391
  have hstep := st266_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p393 : ((1483406915157/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT266 (i+1))
      = (∑ i ∈ Finset.range 392, stT266 (i+1)) + stT266 393 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 392
    simpa using h
  have hprev := st266_p392
  have hstep := st266_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p394 : ((1603734737553/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT266 (i+1))
      = (∑ i ∈ Finset.range 393, stT266 (i+1)) + stT266 394 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 393
    simpa using h
  have hprev := st266_p393
  have hstep := st266_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p395 : ((688318261623/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT266 (i+1))
      = (∑ i ∈ Finset.range 394, stT266 (i+1)) + stT266 395 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 394
    simpa using h
  have hprev := st266_p394
  have hstep := st266_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p396 : ((178360977591/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT266 (i+1))
      = (∑ i ∈ Finset.range 395, stT266 (i+1)) + stT266 396 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 395
    simpa using h
  have hprev := st266_p395
  have hstep := st266_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p397 : ((176520059743/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT266 (i+1))
      = (∑ i ∈ Finset.range 396, stT266 (i+1)) + stT266 397 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 396
    simpa using h
  have hprev := st266_p396
  have hstep := st266_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p398 : ((669551882353/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT266 (i+1))
      = (∑ i ∈ Finset.range 397, stT266 (i+1)) + stT266 398 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 397
    simpa using h
  have hprev := st266_p397
  have hstep := st266_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p399 : ((6196755657851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT266 (i+1))
      = (∑ i ∈ Finset.range 398, stT266 (i+1)) + stT266 399 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 398
    simpa using h
  have hprev := st266_p398
  have hstep := st266_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p400 : ((2889103160377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT266 (i+1))
      = (∑ i ∈ Finset.range 399, stT266 (i+1)) + stT266 400 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 399
    simpa using h
  have hprev := st266_p399
  have hstep := st266_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p401 : ((5617454367569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT266 (i+1))
      = (∑ i ∈ Finset.range 400, stT266 (i+1)) + stT266 401 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 400
    simpa using h
  have hprev := st266_p400
  have hstep := st266_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p402 : ((5781315505483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT266 (i+1))
      = (∑ i ∈ Finset.range 401, stT266 (i+1)) + stT266 402 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 401
    simpa using h
  have hprev := st266_p401
  have hstep := st266_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p403 : ((6199292613823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT266 (i+1))
      = (∑ i ∈ Finset.range 402, stT266 (i+1)) + stT266 403 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 402
    simpa using h
  have hprev := st266_p402
  have hstep := st266_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p404 : ((267801060571/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT266 (i+1))
      = (∑ i ∈ Finset.range 403, stT266 (i+1)) + stT266 404 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 403
    simpa using h
  have hprev := st266_p403
  have hstep := st266_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p405 : ((7061370238637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT266 (i+1))
      = (∑ i ∈ Finset.range 404, stT266 (i+1)) + stT266 405 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 404
    simpa using h
  have hprev := st266_p404
  have hstep := st266_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p406 : ((3573409570781/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT266 (i+1))
      = (∑ i ∈ Finset.range 405, stT266 (i+1)) + stT266 406 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 405
    simpa using h
  have hprev := st266_p405
  have hstep := st266_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p407 : ((216166865309/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT266 (i+1))
      = (∑ i ∈ Finset.range 406, stT266 (i+1)) + stT266 407 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 406
    simpa using h
  have hprev := st266_p406
  have hstep := st266_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p408 : ((646871501779/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT266 (i+1))
      = (∑ i ∈ Finset.range 407, stT266 (i+1)) + stT266 408 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 407
    simpa using h
  have hprev := st266_p407
  have hstep := st266_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p409 : ((5985543151033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT266 (i+1))
      = (∑ i ∈ Finset.range 408, stT266 (i+1)) + stT266 409 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 408
    simpa using h
  have hprev := st266_p408
  have hstep := st266_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p410 : ((2832397065539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT266 (i+1))
      = (∑ i ∈ Finset.range 409, stT266 (i+1)) + stT266 410 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 409
    simpa using h
  have hprev := st266_p409
  have hstep := st266_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p411 : ((2817887458347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT266 (i+1))
      = (∑ i ∈ Finset.range 410, stT266 (i+1)) + stT266 411 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 410
    simpa using h
  have hprev := st266_p410
  have hstep := st266_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p412 : ((2954431256603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT266 (i+1))
      = (∑ i ∈ Finset.range 411, stT266 (i+1)) + stT266 412 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 411
    simpa using h
  have hprev := st266_p411
  have hstep := st266_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p413 : ((3186501863411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT266 (i+1))
      = (∑ i ∈ Finset.range 412, stT266 (i+1)) + stT266 413 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 412
    simpa using h
  have hprev := st266_p412
  have hstep := st266_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p414 : ((6841780012209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT266 (i+1))
      = (∑ i ∈ Finset.range 413, stT266 (i+1)) + stT266 414 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 413
    simpa using h
  have hprev := st266_p413
  have hstep := st266_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p415 : ((7128616413489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT266 (i+1))
      = (∑ i ∈ Finset.range 414, stT266 (i+1)) + stT266 415 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 414
    simpa using h
  have hprev := st266_p414
  have hstep := st266_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p416 : ((1424143172863/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT266 (i+1))
      = (∑ i ∈ Finset.range 415, stT266 (i+1)) + stT266 416 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 415
    simpa using h
  have hprev := st266_p415
  have hstep := st266_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p417 : ((6822488696127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT266 (i+1))
      = (∑ i ∈ Finset.range 416, stT266 (i+1)) + stT266 417 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 416
    simpa using h
  have hprev := st266_p416
  have hstep := st266_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p418 : ((254090161643/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT266 (i+1))
      = (∑ i ∈ Finset.range 417, stT266 (i+1)) + stT266 418 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 417
    simpa using h
  have hprev := st266_p417
  have hstep := st266_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p419 : ((5894442398831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT266 (i+1))
      = (∑ i ∈ Finset.range 418, stT266 (i+1)) + stT266 419 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 418
    simpa using h
  have hprev := st266_p418
  have hstep := st266_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p420 : ((5626992552123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT266 (i+1))
      = (∑ i ∈ Finset.range 419, stT266 (i+1)) + stT266 420 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 419
    simpa using h
  have hprev := st266_p419
  have hstep := st266_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p421 : ((5652559982323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT266 (i+1))
      = (∑ i ∈ Finset.range 420, stT266 (i+1)) + stT266 421 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 420
    simpa using h
  have hprev := st266_p420
  have hstep := st266_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p422 : ((5959994930299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT266 (i+1))
      = (∑ i ∈ Finset.range 421, stT266 (i+1)) + stT266 422 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 421
    simpa using h
  have hprev := st266_p421
  have hstep := st266_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p423 : ((6430142463931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT266 (i+1))
      = (∑ i ∈ Finset.range 422, stT266 (i+1)) + stT266 423 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 422
    simpa using h
  have hprev := st266_p422
  have hstep := st266_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p424 : ((1376561583041/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT266 (i+1))
      = (∑ i ∈ Finset.range 423, stT266 (i+1)) + stT266 424 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 423
    simpa using h
  have hprev := st266_p423
  have hstep := st266_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p425 : ((3573022880207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT266 (i+1))
      = (∑ i ∈ Finset.range 424, stT266 (i+1)) + stT266 425 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 424
    simpa using h
  have hprev := st266_p424
  have hstep := st266_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p426 : ((178027384023/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT266 (i+1))
      = (∑ i ∈ Finset.range 425, stT266 (i+1)) + stT266 426 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 425
    simpa using h
  have hprev := st266_p425
  have hstep := st266_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p427 : ((3409300641869/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT266 (i+1))
      = (∑ i ∈ Finset.range 426, stT266 (i+1)) + stT266 427 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 426
    simpa using h
  have hprev := st266_p426
  have hstep := st266_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p428 : ((6353165757007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT266 (i+1))
      = (∑ i ∈ Finset.range 427, stT266 (i+1)) + stT266 428 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 427
    simpa using h
  have hprev := st266_p427
  have hstep := st266_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p429 : ((5899171662577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT266 (i+1))
      = (∑ i ∈ Finset.range 428, stT266 (i+1)) + stT266 429 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 428
    simpa using h
  have hprev := st266_p428
  have hstep := st266_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p430 : ((703152201551/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT266 (i+1))
      = (∑ i ∈ Finset.range 429, stT266 (i+1)) + stT266 430 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 429
    simpa using h
  have hprev := st266_p429
  have hstep := st266_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p431 : ((5631817151191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT266 (i+1))
      = (∑ i ∈ Finset.range 430, stT266 (i+1)) + stT266 431 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 430
    simpa using h
  have hprev := st266_p430
  have hstep := st266_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p432 : ((5915325830941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT266 (i+1))
      = (∑ i ∈ Finset.range 431, stT266 (i+1)) + stT266 432 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 431
    simpa using h
  have hprev := st266_p431
  have hstep := st266_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p433 : ((796328734613/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT266 (i+1))
      = (∑ i ∈ Finset.range 432, stT266 (i+1)) + stT266 433 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 432
    simpa using h
  have hprev := st266_p432
  have hstep := st266_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p434 : ((3415421169047/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT266 (i+1))
      = (∑ i ∈ Finset.range 433, stT266 (i+1)) + stT266 434 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 433
    simpa using h
  have hprev := st266_p433
  have hstep := st266_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p435 : ((1782189647749/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT266 (i+1))
      = (∑ i ∈ Finset.range 434, stT266 (i+1)) + stT266 435 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 434
    simpa using h
  have hprev := st266_p434
  have hstep := st266_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p436 : ((28629318331/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT266 (i+1))
      = (∑ i ∈ Finset.range 435, stT266 (i+1)) + stT266 436 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 435
    simpa using h
  have hprev := st266_p435
  have hstep := st266_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p437 : ((1381483758179/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT266 (i+1))
      = (∑ i ∈ Finset.range 436, stT266 (i+1)) + stT266 437 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 436
    simpa using h
  have hprev := st266_p436
  have hstep := st266_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p438 : ((6469776723691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT266 (i+1))
      = (∑ i ∈ Finset.range 437, stT266 (i+1)) + stT266 438 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 437
    simpa using h
  have hprev := st266_p437
  have hstep := st266_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p439 : ((6001383838283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT266 (i+1))
      = (∑ i ∈ Finset.range 438, stT266 (i+1)) + stT266 439 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 438
    simpa using h
  have hprev := st266_p438
  have hstep := st266_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p440 : ((5668775072863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT266 (i+1))
      = (∑ i ∈ Finset.range 439, stT266 (i+1)) + stT266 440 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 439
    simpa using h
  have hprev := st266_p439
  have hstep := st266_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p441 : ((5589012127981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT266 (i+1))
      = (∑ i ∈ Finset.range 440, stT266 (i+1)) + stT266 441 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 440
    simpa using h
  have hprev := st266_p440
  have hstep := st266_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p442 : ((5789107088057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT266 (i+1))
      = (∑ i ∈ Finset.range 441, stT266 (i+1)) + stT266 442 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 441
    simpa using h
  have hprev := st266_p441
  have hstep := st266_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p443 : ((6197707978741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT266 (i+1))
      = (∑ i ∈ Finset.range 442, stT266 (i+1)) + stT266 443 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 442
    simpa using h
  have hprev := st266_p442
  have hstep := st266_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p444 : ((6671279873381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT266 (i+1))
      = (∑ i ∈ Finset.range 443, stT266 (i+1)) + stT266 444 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 443
    simpa using h
  have hprev := st266_p443
  have hstep := st266_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p445 : ((1761234683489/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT266 (i+1))
      = (∑ i ∈ Finset.range 444, stT266 (i+1)) + stT266 445 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 444
    simpa using h
  have hprev := st266_p444
  have hstep := st266_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p446 : ((7189782099039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT266 (i+1))
      = (∑ i ∈ Finset.range 445, stT266 (i+1)) + stT266 446 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 445
    simpa using h
  have hprev := st266_p445
  have hstep := st266_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p447 : ((7056863189391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT266 (i+1))
      = (∑ i ∈ Finset.range 446, stT266 (i+1)) + stT266 447 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 446
    simpa using h
  have hprev := st266_p446
  have hstep := st266_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p448 : ((6692929387679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT266 (i+1))
      = (∑ i ∈ Finset.range 447, stT266 (i+1)) + stT266 448 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 447
    simpa using h
  have hprev := st266_p447
  have hstep := st266_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p449 : ((6223262763959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT266 (i+1))
      = (∑ i ∈ Finset.range 448, stT266 (i+1)) + stT266 449 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 448
    simpa using h
  have hprev := st266_p448
  have hstep := st266_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p450 : ((5808034154999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT266 (i+1))
      = (∑ i ∈ Finset.range 449, stT266 (i+1)) + stT266 450 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 449
    simpa using h
  have hprev := st266_p449
  have hstep := st266_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p451 : ((1117525965981/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT266 (i+1))
      = (∑ i ∈ Finset.range 450, stT266 (i+1)) + stT266 451 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 450
    simpa using h
  have hprev := st266_p450
  have hstep := st266_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p452 : ((1127108516189/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT266 (i+1))
      = (∑ i ∈ Finset.range 451, stT266 (i+1)) + stT266 452 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 451
    simpa using h
  have hprev := st266_p451
  have hstep := st266_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p453 : ((1186914449789/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT266 (i+1))
      = (∑ i ∈ Finset.range 452, stT266 (i+1)) + stT266 453 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 452
    simpa using h
  have hprev := st266_p452
  have hstep := st266_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p454 : ((3191845681559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT266 (i+1))
      = (∑ i ∈ Finset.range 453, stT266 (i+1)) + stT266 454 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 453
    simpa using h
  have hprev := st266_p453
  have hstep := st266_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p455 : ((6832769558137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT266 (i+1))
      = (∑ i ∈ Finset.range 454, stT266 (i+1)) + stT266 455 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 454
    simpa using h
  have hprev := st266_p454
  have hstep := st266_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p456 : ((7132940983801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT266 (i+1))
      = (∑ i ∈ Finset.range 455, stT266 (i+1)) + stT266 456 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 455
    simpa using h
  have hprev := st266_p455
  have hstep := st266_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p457 : ((7185748668001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT266 (i+1))
      = (∑ i ∈ Finset.range 456, stT266 (i+1)) + stT266 457 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 456
    simpa using h
  have hprev := st266_p456
  have hstep := st266_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p458 : ((6974838409911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT266 (i+1))
      = (∑ i ∈ Finset.range 457, stT266 (i+1)) + stT266 458 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 457
    simpa using h
  have hprev := st266_p457
  have hstep := st266_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p459 : ((1642576146537/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT266 (i+1))
      = (∑ i ∈ Finset.range 458, stT266 (i+1)) + stT266 459 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 458
    simpa using h
  have hprev := st266_p458
  have hstep := st266_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p460 : ((6104771947033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT266 (i+1))
      = (∑ i ∈ Finset.range 459, stT266 (i+1)) + stT266 460 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 459
    simpa using h
  have hprev := st266_p459
  have hstep := st266_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p461 : ((5729549396941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT266 (i+1))
      = (∑ i ∈ Finset.range 460, stT266 (i+1)) + stT266 461 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 460
    simpa using h
  have hprev := st266_p460
  have hstep := st266_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p462 : ((2782752124949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT266 (i+1))
      = (∑ i ∈ Finset.range 461, stT266 (i+1)) + stT266 462 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 461
    simpa using h
  have hprev := st266_p461
  have hstep := st266_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p463 : ((5664563832487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT266 (i+1))
      = (∑ i ∈ Finset.range 462, stT266 (i+1)) + stT266 463 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 462
    simpa using h
  have hprev := st266_p462
  have hstep := st266_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p464 : ((5993903090209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT266 (i+1))
      = (∑ i ∈ Finset.range 463, stT266 (i+1)) + stT266 464 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 463
    simpa using h
  have hprev := st266_p463
  have hstep := st266_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p465 : ((6447489865389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT266 (i+1))
      = (∑ i ∈ Finset.range 464, stT266 (i+1)) + stT266 465 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 464
    simpa using h
  have hprev := st266_p464
  have hstep := st266_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p466 : ((1376135713751/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT266 (i+1))
      = (∑ i ∈ Finset.range 465, stT266 (i+1)) + stT266 466 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 465
    simpa using h
  have hprev := st266_p465
  have hstep := st266_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p467 : ((7156468439827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT266 (i+1))
      = (∑ i ∈ Finset.range 466, stT266 (i+1)) + stT266 467 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 466
    simpa using h
  have hprev := st266_p466
  have hstep := st266_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p468 : ((7188584183077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT266 (i+1))
      = (∑ i ∈ Finset.range 467, stT266 (i+1)) + stT266 468 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 467
    simpa using h
  have hprev := st266_p467
  have hstep := st266_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p469 : ((1393583022843/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT266 (i+1))
      = (∑ i ∈ Finset.range 468, stT266 (i+1)) + stT266 469 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 468
    simpa using h
  have hprev := st266_p468
  have hstep := st266_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p470 : ((6564438363759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT266 (i+1))
      = (∑ i ∈ Finset.range 469, stT266 (i+1)) + stT266 470 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 469
    simpa using h
  have hprev := st266_p469
  have hstep := st266_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p471 : ((6104449369167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT266 (i+1))
      = (∑ i ∈ Finset.range 470, stT266 (i+1)) + stT266 471 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 470
    simpa using h
  have hprev := st266_p470
  have hstep := st266_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p472 : ((5730736939087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT266 (i+1))
      = (∑ i ∈ Finset.range 471, stT266 (i+1)) + stT266 472 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 471
    simpa using h
  have hprev := st266_p471
  have hstep := st266_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p473 : ((694787623583/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT266 (i+1))
      = (∑ i ∈ Finset.range 472, stT266 (i+1)) + stT266 473 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 472
    simpa using h
  have hprev := st266_p472
  have hstep := st266_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p474 : ((5639344823839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT266 (i+1))
      = (∑ i ∈ Finset.range 473, stT266 (i+1)) + stT266 474 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 473
    simpa using h
  have hprev := st266_p473
  have hstep := st266_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p475 : ((5948034391033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT266 (i+1))
      = (∑ i ∈ Finset.range 474, stT266 (i+1)) + stT266 475 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 474
    simpa using h
  have hprev := st266_p474
  have hstep := st266_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p476 : ((6389339225119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT266 (i+1))
      = (∑ i ∈ Finset.range 475, stT266 (i+1)) + stT266 476 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 475
    simpa using h
  have hprev := st266_p475
  have hstep := st266_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p477 : ((6828734082791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT266 (i+1))
      = (∑ i ∈ Finset.range 476, stT266 (i+1)) + stT266 477 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 476
    simpa using h
  have hprev := st266_p476
  have hstep := st266_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p478 : ((891667850911/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT266 (i+1))
      = (∑ i ∈ Finset.range 477, stT266 (i+1)) + stT266 478 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 477
    simpa using h
  have hprev := st266_p477
  have hstep := st266_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p479 : ((3605980827707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT266 (i+1))
      = (∑ i ∈ Finset.range 478, stT266 (i+1)) + stT266 479 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 478
    simpa using h
  have hprev := st266_p478
  have hstep := st266_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p480 : ((704187808299/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT266 (i+1))
      = (∑ i ∈ Finset.range 479, stT266 (i+1)) + stT266 480 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 479
    simpa using h
  have hprev := st266_p479
  have hstep := st266_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p481 : ((1668722644191/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT266 (i+1))
      = (∑ i ∈ Finset.range 480, stT266 (i+1)) + stT266 481 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 480
    simpa using h
  have hprev := st266_p480
  have hstep := st266_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p482 : ((1555236784143/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT266 (i+1))
      = (∑ i ∈ Finset.range 481, stT266 (i+1)) + stT266 482 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 481
    simpa using h
  have hprev := st266_p481
  have hstep := st266_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p483 : ((1453724648361/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT266 (i+1))
      = (∑ i ∈ Finset.range 482, stT266 (i+1)) + stT266 483 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 482
    simpa using h
  have hprev := st266_p482
  have hstep := st266_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p484 : ((2788196199073/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT266 (i+1))
      = (∑ i ∈ Finset.range 483, stT266 (i+1)) + stT266 484 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 483
    simpa using h
  have hprev := st266_p483
  have hstep := st266_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p485 : ((2787430625251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT266 (i+1))
      = (∑ i ∈ Finset.range 484, stT266 (i+1)) + stT266 485 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 484
    simpa using h
  have hprev := st266_p484
  have hstep := st266_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p486 : ((5809836609419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT266 (i+1))
      = (∑ i ∈ Finset.range 485, stT266 (i+1)) + stT266 486 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 485
    simpa using h
  have hprev := st266_p485
  have hstep := st266_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p487 : ((6211865079019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT266 (i+1))
      = (∑ i ∈ Finset.range 486, stT266 (i+1)) + stT266 487 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 486
    simpa using h
  have hprev := st266_p486
  have hstep := st266_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p488 : ((6663529080299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT266 (i+1))
      = (∑ i ∈ Finset.range 487, stT266 (i+1)) + stT266 488 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 487
    simpa using h
  have hprev := st266_p487
  have hstep := st266_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p489 : ((3516991125827/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT266 (i+1))
      = (∑ i ∈ Finset.range 488, stT266 (i+1)) + stT266 489 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 488
    simpa using h
  have hprev := st266_p488
  have hstep := st266_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p490 : ((9020998199/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT266 (i+1))
      = (∑ i ∈ Finset.range 489, stT266 (i+1)) + stT266 490 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 489
    simpa using h
  have hprev := st266_p489
  have hstep := st266_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p491 : ((716022659983/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT266 (i+1))
      = (∑ i ∈ Finset.range 490, stT266 (i+1)) + stT266 491 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 490
    simpa using h
  have hprev := st266_p490
  have hstep := st266_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p492 : ((1376272071281/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT266 (i+1))
      = (∑ i ∈ Finset.range 491, stT266 (i+1)) + stT266 492 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 491
    simpa using h
  have hprev := st266_p491
  have hstep := st266_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p493 : ((6460447886677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT266 (i+1))
      = (∑ i ∈ Finset.range 492, stT266 (i+1)) + stT266 493 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 492
    simpa using h
  have hprev := st266_p492
  have hstep := st266_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p494 : ((6017387197177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT266 (i+1))
      = (∑ i ∈ Finset.range 493, stT266 (i+1)) + stT266 494 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 493
    simpa using h
  have hprev := st266_p493
  have hstep := st266_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p495 : ((1135480633381/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT266 (i+1))
      = (∑ i ∈ Finset.range 494, stT266 (i+1)) + stT266 495 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 494
    simpa using h
  have hprev := st266_p494
  have hstep := st266_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p496 : ((221430108813/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT266 (i+1))
      = (∑ i ∈ Finset.range 495, stT266 (i+1)) + stT266 496 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 495
    simpa using h
  have hprev := st266_p495
  have hstep := st266_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p497 : ((2815682421579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT266 (i+1))
      = (∑ i ∈ Finset.range 496, stT266 (i+1)) + stT266 497 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 496
    simpa using h
  have hprev := st266_p496
  have hstep := st266_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p498 : ((2968315857339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT266 (i+1))
      = (∑ i ∈ Finset.range 497, stT266 (i+1)) + stT266 498 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 497
    simpa using h
  have hprev := st266_p497
  have hstep := st266_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p499 : ((127317447197/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT266 (i+1))
      = (∑ i ∈ Finset.range 498, stT266 (i+1)) + stT266 499 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 498
    simpa using h
  have hprev := st266_p498
  have hstep := st266_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_p500 : ((271988994859/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT266 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT266 (i+1))
      = (∑ i ∈ Finset.range 499, stT266 (i+1)) + stT266 500 := by
    have h := Finset.sum_range_succ (fun i => stT266 (i+1)) 499
    simpa using h
  have hprev := st266_p499
  have hstep := st266_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st266_s500 :
    |Real.sin (((266 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((181581/500000 : ℚ) : ℝ))
      - ((48481/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 612109/10000000) (δ := 1339/100000000) (ψ := 181581/500000) 266 263
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 266`** (evaluated boundary). -/
theorem station_266_sign : 0 < hardyG ((((266:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 266 500 (by norm_num) (by norm_num)
    ((181581/500000 : ℚ) : ℝ)
  have hchain := st266_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT266 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((266 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((181581/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st266_c500
  have hsinb := abs_le.mp st266_s500
  have hbdy_lo : ((-5811827003999/283025000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((266 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((181581/500000 : ℚ) : ℝ))) / 2
          - ((((266:ℕ)):ℝ))
            * Real.sin (((266 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((181581/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((266:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((266:ℝ) * Real.log (500:ℝ) - ((181581/500000 : ℚ) : ℝ))) / 2
        - ((266:ℝ)) * Real.sin ((266:ℝ) * Real.log (500:ℝ) - ((181581/500000 : ℚ) : ℝ))
        ≥ ((-25991257/400000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((266:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-25991257/400000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (223607/5000000)
          * ((-25991257/400000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((-25991257/400000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((266:ℕ)):ℝ))+1) * (((((266:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((1393270396623/2500000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((271988994859/400000000000 : ℚ) : ℝ) + ((-5811827003999/283025000000000 : ℚ) : ℝ)
      - ((1393270396623/2500000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((181581/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((266:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((181581/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((266:ℕ)):ℝ)))).re
      - Real.sin ((181581/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((266:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((266:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((266:ℕ)):ℝ))
      = (((((266:ℕ)):ℝ)) * (Real.log ((((266:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((266:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_266
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
  have hθwin : |(((181581/500000 : ℚ) : ℝ) + ((58:ℤ)) * (2*Real.pi)) - theta ((((266:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((266:ℕ)):ℝ)))
    (φ := ((181581/500000 : ℚ) : ℝ) + ((58:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((181581/500000 : ℚ)) : ℝ) 58).1,
    (cos_sin_shift (((181581/500000 : ℚ)) : ℝ) 58).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_266_sign
end AxiomAudit
